//! Explicit semantic contracts for the embedded runtime. These describe Rusk
//! operations, never C++ names or source patterns. They are a trust boundary.
pub(crate) mod aliases;
pub(crate) mod composition;

use crate::analysis::effects::{Effect, ReturnAlias, Summary};
use std::collections::BTreeMap;

/// Parameter writes/retention and returned aliases require projection mappings;
/// until those are declared, such native dependencies remain opaque.
pub(crate) fn dependency_covered(base: &Summary, dependency: &Summary) -> bool {
    dependency.external_write == Effect::No
        && dependency.io <= base.io
        && dependency.may_fail <= base.may_fail
        && dependency.may_diverge <= base.may_diverge
        && !dependency.returned.unknown
        && dependency.returned.aliases.is_empty()
        && dependency.parameters.iter().all(|p| {
            p.write == Effect::No && p.structural == Effect::No && p.retained == Effect::No
        })
}

/// Generated aggregates and standard storage have no arbitrary destructor calls
/// when every stored value has the same property. Recursive nominal graphs are
/// checked coinductively; opaque foreign values keep release effects unknown.
fn quiet_release(ty: &str, types: &BTreeMap<String, crate::ir::hir::Type>) -> bool {
    fn walk(
        ty: &str,
        types: &BTreeMap<String, crate::ir::hir::Type>,
        seen: &mut std::collections::BTreeSet<String>,
        budget: &mut usize,
        depth: usize,
    ) -> bool {
        use crate::ir::hir::Type;
        if *budget == 0 || depth > 128 {
            return false;
        }
        *budget -= 1;
        if !seen.insert(ty.into()) {
            return true;
        }
        match types.get(ty) {
            Some(Type::Scalar(_)) => true,
            Some(Type::Vector(t) | Type::Buffer(t) | Type::Set(t)) => {
                walk(t, types, seen, budget, depth + 1)
            }
            Some(
                Type::Record(fields)
                | Type::Shared(fields)
                | Type::FunctionFamily { fields, .. }
                | Type::Callable { fields, .. },
            ) => fields
                .iter()
                .all(|(_, t)| walk(t, types, seen, budget, depth + 1)),
            Some(Type::Enum(variants)) => variants.iter().all(|(_, fields)| {
                fields
                    .iter()
                    .all(|t| walk(t, types, seen, budget, depth + 1))
            }),
            Some(Type::Dict { key, value }) => {
                walk(key, types, seen, budget, depth + 1)
                    && walk(value, types, seen, budget, depth + 1)
            }
            Some(Type::Iterator { element, retained }) => {
                walk(element, types, seen, budget, depth + 1)
                    && retained
                        .iter()
                        .all(|(_, t)| walk(t, types, seen, budget, depth + 1))
            }
            _ => false,
        }
    }
    walk(ty, types, &mut Default::default(), &mut 4096, 0)
}

pub(crate) fn contract(
    specification: &str,
    parameters: &[String],
    result: &str,
    types: &BTreeMap<String, crate::ir::hir::Type>,
) -> Result<Summary, String> {
    fn builtin_value(ty: &str, types: &BTreeMap<String, crate::ir::hir::Type>) -> bool {
        fn walk(ty: &str, types: &BTreeMap<String, crate::ir::hir::Type>, depth: usize) -> bool {
            if depth >= 64 {
                return false;
            }
            match types.get(ty) {
                Some(crate::ir::hir::Type::Scalar(_)) => true,
                Some(
                    crate::ir::hir::Type::Buffer(element) | crate::ir::hir::Type::Vector(element),
                ) => walk(element, types, depth + 1),
                _ => false,
            }
        }
        walk(ty, types, 0)
    }
    let specification = match specification {
        "deep_read_fresh" | "deep_resize_first" => {
            // Generated record copies can invoke user-defined copy functions;
            // foreign data can also supply arbitrary target-language helpers.
            if parameters.iter().any(|ty| !builtin_value(ty, types)) {
                return Ok(Summary::opaque(parameters.len()));
            }
            match specification {
                "deep_read_fresh" => "checked_read_fresh",
                "deep_resize_first" => "checked_resize_first",
                _ => unreachable!("deep operation matched above"),
            }
        }
        other => other,
    };
    let mut summary = Summary::native(parameters.len());
    for parameter in &mut summary.parameters {
        parameter.read = Effect::May;
    }
    summary.returned.fresh = result != "Unit";
    match specification {
        "read_fresh" => {}
        "checked_read_fresh" => summary.may_fail = Effect::May,
        "checked_cursor_consume" => {
            summary.cursor_step = true;
            summary.may_fail = Effect::May;
            summary.may_diverge = Effect::May;
        }
        "write_first"
        | "checked_write_first"
        | "checked_resize_first"
        | "checked_mutate_fresh"
        | "checked_cursor_step" => {
            let first = summary
                .parameters
                .first_mut()
                .ok_or("native write contract requires an argument")?;
            first.write = Effect::May;
            first.root_only = true;
            summary.cursor_step = specification == "checked_cursor_step";
            if specification == "checked_resize_first" {
                first.structural = Effect::May;
            }
            if specification != "write_first" {
                summary.may_fail = Effect::May;
            }
            if !matches!(
                specification,
                "checked_mutate_fresh" | "checked_cursor_step"
            ) && result != "Unit"
            {
                return Err("native write contract requires Unit result".into());
            }
        }
        "io_read_fresh" | "io_write" | "checked_io_write" => {
            summary.io = Effect::May;
            summary.may_diverge = Effect::May; // IO can block.
            if specification == "io_read_fresh" {
                summary.may_fail = Effect::May;
                if result == "Unit" {
                    return Err("native input contract requires a result".into());
                }
            } else {
                if result != "Unit" {
                    return Err("native output contract requires Unit result".into());
                }
                summary.may_fail = if specification == "checked_io_write" {
                    Effect::May
                } else {
                    Effect::No
                };
            }
        }
        "resize_retain_second" | "replace_element" => {
            let source = if specification == "replace_element" {
                2
            } else {
                1
            };
            if parameters.len() != source + 1 {
                return Err("native element store contract has invalid arity".into());
            }
            let Some(crate::ir::hir::Type::Vector(element)) = types.get(&parameters[0]) else {
                return Err("native element store requires a vector".into());
            };
            if *element != parameters[source]
                || (source == 2
                    && !matches!(
                        types.get(&parameters[1]),
                        Some(crate::ir::hir::Type::Scalar(crate::ir::hir::Scalar::I64))
                    ))
            {
                return Err("native element store type mismatch".into());
            }
            summary.parameters[0].write = Effect::May;
            summary.parameters[0].root_only = source == 1 || quiet_release(element, types);
            summary.parameters[0].structural = if source == 1 { Effect::May } else { Effect::No };
            summary.parameters[source].escape = Effect::May;
            summary.parameters[source].retained = Effect::May;
            summary.parameters[source].readonly_sealed = element.starts_with("__RuskReadonly<");
            summary.parameters[source].readonly_sealed_paths = readonly_paths(element, types);
            if source == 1 {
                if result != "Unit" {
                    return Err("native append requires Unit result".into());
                }
            } else {
                if result != element {
                    return Err("native element store result mismatch".into());
                }
                summary.may_fail = Effect::May;
                summary.returned.fresh = false;
                summary.returned.aliases.insert(ReturnAlias {
                    result_path: vec![],
                    parameter: source,
                    parameter_path: vec![],
                });
            }
        }
        specification if specification.starts_with("variant_constructor:") => {
            let variant = specification
                .strip_prefix("variant_constructor:")
                .and_then(|n| n.parse::<usize>().ok())
                .ok_or("invalid native enum constructor contract")?;
            let Some(crate::ir::hir::Type::Enum(variants)) = types.get(result) else {
                return Err("native enum constructor contract requires an enum result".into());
            };
            if variants
                .get(variant)
                .is_none_or(|(_, fields)| fields != parameters)
            {
                return Err("native enum constructor contract has an invalid payload".into());
            }
            for parameter in 0..parameters.len() {
                summary.parameters[parameter].escape = Effect::May;
                summary.returned.aliases.insert(ReturnAlias {
                    result_path: vec![crate::analysis::effects::Projection::VariantField {
                        variant,
                        field: parameter,
                    }],
                    parameter,
                    parameter_path: vec![],
                });
            }
        }
        specification if specification.starts_with("checked_variant_field:") => {
            let mut parts = specification.split(':').skip(1);
            let mut number = || {
                parts
                    .next()
                    .and_then(|p| p.parse::<usize>().ok())
                    .ok_or("invalid native enum field contract")
            };
            let variant = number()?;
            let field = number()?;
            if parts.next().is_some() {
                return Err("invalid native enum field contract".into());
            }
            if parameters.len() != 1 {
                return Err("native enum field contract requires one receiver".into());
            }
            let Some(crate::ir::hir::Type::Enum(variants)) = types.get(&parameters[0]) else {
                return Err("native enum field contract requires an enum".into());
            };
            if variants
                .get(variant)
                .and_then(|(_, fields)| fields.get(field))
                .is_none_or(|ty| ty != result)
            {
                return Err("native enum field contract has an invalid payload".into());
            }
            summary.returned.fresh = false;
            summary.returned.aliases.insert(ReturnAlias {
                result_path: vec![],
                parameter: 0,
                parameter_path: vec![crate::analysis::effects::Projection::VariantField {
                    variant,
                    field,
                }],
            });
            summary.parameters[0].escape = Effect::May;
            summary.may_fail = Effect::May;
        }
        "checked_clear_first" => {
            if parameters.len() != 1 || result != "Unit" {
                return Err("native clear requires one vector and Unit result".into());
            }
            let Some(crate::ir::hir::Type::Vector(element)) = types.get(&parameters[0]) else {
                return Err("native clear requires a vector".into());
            };
            if !quiet_release(element, types) {
                return Ok(Summary::opaque(parameters.len()));
            }
            summary.parameters[0].write = Effect::May;
            summary.parameters[0].structural = Effect::May;
            summary.parameters[0].root_only = true;
            summary.may_fail = Effect::May;
        }
        "pop_element" => {
            if parameters.len() != 1
                || !matches!(
                    types.get(&parameters[0]),
                    Some(crate::ir::hir::Type::Vector(_))
                )
            {
                return Err("native pop requires one vector".into());
            }
            summary.parameters[0].write = Effect::May;
            summary.parameters[0].structural = Effect::May;
            summary.parameters[0].root_only = true;
            summary.parameters[0].escape = Effect::May;
            summary.returned.fresh = false;
            summary.returned.aliases.insert(ReturnAlias {
                result_path: vec![],
                parameter: 0,
                parameter_path: vec![crate::analysis::effects::Projection::Element],
            });
            summary.may_fail = Effect::May;
        }
        "element" => {
            if parameters.len() != 2
                || !matches!(
                    types.get(&parameters[1]),
                    Some(crate::ir::hir::Type::Scalar(crate::ir::hir::Scalar::I64))
                )
            {
                return Err("native element contract requires a container and an integer index representation".into());
            }
            summary.returned.fresh = false;
            summary.returned.aliases.insert(ReturnAlias {
                result_path: vec![],
                parameter: 0,
                parameter_path: vec![crate::analysis::effects::Projection::Element],
            });
            summary.parameters[0].escape = Effect::May;
            summary.may_fail = Effect::May;
        }
        _ => return Err(format!("unknown native effect contract '{specification}'")),
    }
    summary.validate_signature(parameters, result, types, false)?;
    Ok(summary)
}

#[cfg(test)]
mod tests;

// This is a must-set: omitted recursive or opaque paths retain conservative
// behavior. Every returned path is guaranteed readonly by the storage type.
fn readonly_paths(
    ty: &str,
    types: &BTreeMap<String, crate::ir::hir::Type>,
) -> std::collections::BTreeSet<Vec<crate::analysis::effects::Projection>> {
    use crate::analysis::effects::Projection;
    use crate::ir::hir::Type;
    fn walk(
        ty: &str,
        types: &BTreeMap<String, Type>,
        path: &mut Vec<Projection>,
        result: &mut std::collections::BTreeSet<Vec<Projection>>,
        budget: &mut usize,
    ) {
        if *budget == 0 || path.len() > 16 || result.len() >= 64 {
            return;
        }
        *budget -= 1;
        if ty.starts_with("__RuskReadonly<") {
            result.insert(path.clone());
            return;
        }
        let children: Vec<(Projection, &str)> = match types.get(ty) {
            Some(Type::Vector(t) | Type::Buffer(t)) => vec![(Projection::Element, t)],
            Some(
                Type::Record(f)
                | Type::Shared(f)
                | Type::Callable { fields: f, .. }
                | Type::FunctionFamily { fields: f, .. },
            ) => f
                .iter()
                .enumerate()
                .map(|(i, (_, t))| (Projection::Field(i), t.as_str()))
                .collect(),
            Some(Type::Enum(v)) => v
                .iter()
                .enumerate()
                .flat_map(|(variant, (_, fields))| {
                    fields.iter().enumerate().map(move |(field, t)| {
                        (Projection::VariantField { variant, field }, t.as_str())
                    })
                })
                .collect(),
            _ => vec![],
        };
        for (projection, child) in children {
            path.push(projection);
            walk(child, types, path, result, budget);
            path.pop();
        }
    }
    let mut result = std::collections::BTreeSet::new();
    walk(ty, types, &mut vec![], &mut result, &mut 4096);
    result
}
