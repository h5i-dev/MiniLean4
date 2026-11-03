//! Strict positivity (acceptance condition 3).

use crate::{
    declaration::{ConstructorSpec, InductiveSpec, RecursiveFieldInfo},
    kernel::Result,
    term::{const_term, occurs_const, spine, var, Term},
};

/// Condition 3 for every field of one constructor: a field that mentions `I`
/// must be a strictly positive recursive field.
///
/// Returns the recursive fields, in field order. The recursor needs them to
/// build the induction hypotheses.
pub(crate) fn check_recursive_fields(
    spec: &InductiveSpec,
    constructor: &ConstructorSpec,
) -> Result<Vec<RecursiveFieldInfo>> {
    constructor
        .fields
        .iter()
        .enumerate()
        .filter(|(_, (_, field_type))| occurs_const(field_type, &spec.name))
        .map(|(field_index, (_, field_type))| {
            check_recursive_field(field_index, field_type, spec)
        })
        .collect()
}

/// Checks that a field type mentioning `I` has the strictly positive form
///
/// ```text
/// Pi (y_1 : B_1) ... Pi (y_k : B_k). I ps ss
/// ```
///
/// where `ps` are exactly the parameters, in order, and `I` occurs neither in
/// `Bs` nor in `ss`. This rejects, for example, `(Bad -> False) -> Bad`, where
/// `Bad` occurs to the left of an arrow.
fn check_recursive_field(
    constructor_field_index: usize,
    field_type: &Term,
    spec: &InductiveSpec,
) -> Result<RecursiveFieldInfo> {
    const ERROR: &str = "non-strictly-positive / unsupported recursive field";
    let inductive = spec.name.as_str();

    // Peel off Pi (ys : Bs); I must not occur in any B_i.
    let mut argument_binders = vec![];
    let mut target = field_type;
    while let Term::Pi(y, domain, body) = target {
        if occurs_const(domain, inductive) {
            return Err(ERROR.into());
        }
        argument_binders.push((y.clone(), (**domain).clone()));
        target = body;
    }

    // The target must be I ps ss.
    let (head, args) = spine(target);
    let num_params = spec.params.len();
    if head != const_term(inductive) || args.len() != num_params + spec.indices.len() {
        return Err(ERROR.into());
    }
    let (param_args, target_indices) = args.split_at(num_params);
    let params_unchanged = param_args
        .iter()
        .zip(&spec.params)
        .all(|(arg, (param, _))| arg == &var(param));
    if !params_unchanged {
        return Err(ERROR.into());
    }
    if target_indices.iter().any(|s| occurs_const(s, inductive)) {
        return Err(ERROR.into());
    }

    Ok(RecursiveFieldInfo {
        constructor_field_index,
        argument_binders,
        target_indices: target_indices.to_vec(),
    })
}
