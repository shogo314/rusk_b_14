//! C++ runtime provider. Rusk HIR/LIR bodies never contain these native sources.
use super::*;
use crate::ir::lir::{self, Program};
use crate::native::NativeRequests;
struct CppReachability<'a> {
    functions: Vec<bool>,
    types: BTreeSet<&'a str>,
    requests: NativeRequests,
}

fn body_dependencies<'a>(
    body: &'a lir::Function,
    functions: &mut Vec<usize>,
    types: &mut Vec<&'a str>,
) {
    types.extend(body.slots.iter().map(|slot| slot.ty.as_str()));
    functions.extend(body.blocks.iter().flat_map(|block| {
        block
            .instructions
            .iter()
            .filter_map(|instruction| match instruction {
                lir::Operation::Call(call) => Some(call.function),
                _ => None,
            })
    }));
}

impl Compiler {
    pub(super) fn finalize_native_references(
        &self,
        text: &str,
        requests: &NativeRequests,
    ) -> String {
        let references = requests
            .direct
            .iter()
            .map(|&(index, object)| {
                let name = if self.capture_parameters(index).is_empty() {
                    self.abi_reference_name(index, object)
                } else {
                    format!("rusk_capture_reference_{index}_{object}")
                };
                (format!("rusk_pending_reference_{index}_{object}__"), name)
            })
            .collect::<BTreeMap<_, _>>();
        let mut output = String::with_capacity(text.len());
        let mut remaining = text;
        while let Some(at) = remaining.find("rusk_pending_reference_") {
            output.push_str(&remaining[..at]);
            remaining = &remaining[at..];
            let Some(end) = remaining.find("__") else {
                break;
            };
            let reference = &remaining[..end + 2];
            output.push_str(references.get(reference).map_or(reference, String::as_str));
            remaining = &remaining[end + 2..];
        }
        output.push_str(remaining);
        output
    }

    fn cpp_reachability<'a>(&'a self, program: &'a Program) -> CppReachability<'a> {
        let mut reachable = CppReachability {
            functions: vec![false; program.functions.len()],
            types: BTreeSet::new(),
            requests: NativeRequests::default(),
        };
        let mut functions = Vec::new();
        // Scalar representations are checked by C++ static assertions, even
        // when Rusk code never reads a value of the declared type.
        let mut types: Vec<_> = self
            .native_types
            .iter()
            .filter(|(_, meta)| matches!(meta.kind, crate::ir::hir::Type::Scalar(_)))
            .map(|(ty, _)| ty.as_str())
            .collect();
        body_dependencies(&program.main, &mut functions, &mut types);
        let previously_emitted_externs = || {
            self.used
                .iter()
                .copied()
                .filter(|&id| self.functions[id].checked.is_none())
        };
        let mut keep_opaque_dependencies = self.has_opaque_symbols();
        if keep_opaque_dependencies {
            functions.extend(previously_emitted_externs());
        }
        while !functions.is_empty() || !types.is_empty() {
            while let Some(id) = functions.pop() {
                if std::mem::replace(&mut reachable.functions[id], true) {
                    continue;
                }
                let function = &program.functions[id];
                let declaration = &self.functions[id];
                if !keep_opaque_dependencies
                    && declaration.checked.is_none()
                    && declaration.origin == Origin::User
                    && !self
                        .native_resource_requirements
                        .contains_key(&declaration.name.span)
                {
                    // Existing opaque C++ can refer to an extern by its C++ name.
                    keep_opaque_dependencies = true;
                    functions.extend(previously_emitted_externs());
                }
                types.extend(function.params.iter().map(String::as_str));
                types.push(&function.result);
                if let Some(body) = &function.body {
                    body_dependencies(body, &mut functions, &mut types);
                }
                if let Some(requests) = self.native_function_requests.get(&id) {
                    functions.extend(requests.targets());
                    reachable.requests.extend(requests);
                }
                if let Some(dependencies) = self.native_function_types.get(&id) {
                    types.extend(dependencies.iter().map(String::as_str));
                }
            }
            while let Some(ty) = types.pop() {
                let ty = access_types::underlying(ty);
                let Some(kind) = program.types.get(ty) else {
                    // Generic value arguments can appear alongside type arguments.
                    continue;
                };
                if !reachable.types.insert(ty) {
                    continue;
                }
                if let Some(fields) = kind.fields() {
                    types.extend(fields.iter().map(|(_, ty)| ty.as_str()));
                }
                if let crate::ir::hir::Type::Enum(variants) = kind {
                    types.extend(
                        variants
                            .iter()
                            .flat_map(|(_, fields)| fields.iter().map(String::as_str)),
                    );
                }
                types.extend(type_metadata::references(kind));
                if let Some((_, arguments)) = tuples::type_parts(ty) {
                    types.extend(arguments);
                }
                if let Some(dependencies) = self.native_type_dependencies.get(ty) {
                    types.extend(dependencies.iter().map(String::as_str));
                }
                if let Some(requests) = self.native_type_requests.get(ty) {
                    functions.extend(requests.targets());
                    reachable.requests.extend(requests);
                }
            }
        }
        reachable
    }

    pub(super) fn cpp_functions(&self, reachable: &[bool]) -> Vec<crate::backend::FunctionInfo> {
        self.functions
            .iter()
            .enumerate()
            .map(|(id, f)| crate::backend::FunctionInfo {
                cpp: if f.checked.is_none() && !self.capture_parameters(id).is_empty() {
                    format!("rusk_native_environment_{id}")
                } else {
                    f.cpp.clone()
                },
                result: access_types::underlying(&f.result).to_string(),
                unit_object: self.native_unit_object(id),
                trusted: f.body.is_none()
                    && (f.origin == Origin::StandardLibrary || self.native_lowering(id).is_some()),
                lowering: self
                    .capture_parameters(id)
                    .is_empty()
                    .then(|| self.native_lowering(id).cloned())
                    .flatten(),
                captures: self.native_capture_keys(id),
                native_entry: (f.checked.is_none()
                    && reachable[id]
                    && !self.capture_parameters(id).is_empty())
                .then(|| f.cpp.clone()),
            })
            .collect()
    }

    pub(super) fn cpp_context(&self, program: &Program) -> crate::backend::Context {
        use externs::native_types::Declaration;
        let CppReachability {
            functions: reachable,
            types,
            requests: mut native_requests,
        } = self.cpp_reachability(program);
        let functions = self.cpp_functions(&reachable);
        let mut prelude = String::new();
        let native_functions = self
            .functions
            .iter()
            .enumerate()
            .filter(|(id, function)| reachable[*id] && function.checked.is_none())
            .map(|(_, function)| (function.origin, &function.name.span));
        let native_types = types
            .iter()
            .filter_map(|ty| self.native_type_resource_origins.get(*ty))
            .map(|(origin, span)| (*origin, span));
        let symbols = self.required_native_symbols(native_functions.chain(native_types));
        for name in self
            .symbol_order
            .iter()
            .filter(|name| symbols.contains(name.as_str()))
        {
            prelude += &self.symbols[name].code;
            prelude += "\n";
        }
        prelude += &crate::metadata::cpp_constants();
        prelude += &self.enum_forwards(&types);
        prelude += &self.record_forwards(&types);
        for (declaration, code) in &self.native_type_prelude {
            if match declaration {
                Declaration::Type(ty) => types.contains(ty.as_str()),
                Declaration::Value(id) => native_requests.values.contains(id),
            } {
                prelude += code;
            }
        }
        prelude += &self.enum_cpp(&types);
        prelude += &self.record_cpp(&types);
        prelude += &self.scalar_representation_checks();
        let (concrete_foreign_definitions, foreign_definitions): (Vec<_>, Vec<_>) =
            (0..self.functions.len())
                .filter(|&id| reachable[id] && self.functions[id].checked.is_none())
                .partition(|&id| {
                    self.functions[id].origin != Origin::Generated
                        && !self.generic_calls.contains_key(&id)
                        && !self.native_concrete_templates.contains(&id)
                        && !self.native_derived_functions.contains(&id)
                });
        let definitions = |ids: Vec<usize>| {
            ids.into_iter()
                .map(|id| self.functions[id].code.clone())
                .collect()
        };
        let epilogue = self.enum_copy_cpp(&reachable) + &self.record_copy_cpp(&reachable);
        native_requests.declarations.extend(
            self.generic_instances
                .values()
                .copied()
                .chain(self.native_concrete_templates.iter().copied())
                .filter(|&id| self.functions[id].body.is_none() && reachable[id]),
        );
        crate::backend::Context {
            types: self.types.clone(),
            functions,
            reachable,
            prelude,
            concrete_foreign_definitions: definitions(concrete_foreign_definitions),
            foreign_definitions: definitions(foreign_definitions),
            native_requests,
            epilogue,
        }
    }
}
