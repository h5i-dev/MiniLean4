//! Data stored in the signature: declarations, the input format for inductive
//! types, and the metadata the kernel derives from a checked inductive type.
//!
//! Notation in comments (ASCII only): a plural name stands for a sequence,
//! e.g. `ps` = `p_1 ... p_k` and `(ps : Ps)` = `(p_1 : P_1) ... (p_k : P_k)`.
//! `is : Js` are the indices, `as : As_j` the fields of constructor `c_j`,
//! and `I.rec_v` is the recursor into `Sort v` (named `I.rec0`, `I.rec1`, ...).

use crate::term::Term;

/// A sequence of bindings `(x_1 : A_1) ... (x_k : A_k)`.
///
/// The same representation is used for local typing contexts `Gamma` and for
/// telescopes such as parameters, indices, and constructor fields. Later
/// entries may mention earlier names, and lookup searches from the end.
pub type Context = Vec<(String, Term)>;

/// What kind of constant a [`Decl`] introduces.
#[derive(Clone, Debug)]
pub enum DeclKind {
    /// A constant with no body. Reduction never unfolds it.
    Axiom,
    /// A constant with a body, unfolded by delta-reduction.
    Definition(Term),
    /// The type former `I` of an inductive type.
    Inductive,
    /// A constructor `c_j` of an inductive type.
    Constructor,
    /// A recursor `I.rec_v`, reduced by iota-reduction.
    Recursor(RecursorInfo),
}

/// A constant in the signature `Sigma`: its type and its kind.
#[derive(Clone, Debug)]
pub struct Decl {
    pub ty: Term,
    pub kind: DeclKind,
}

// ---------------------------------------------------------------------------
// Input: the declaration a user writes. `Kernel::add_inductive` checks it.
// ---------------------------------------------------------------------------

/// An unchecked `inductive` declaration, the input to `Kernel::add_inductive`:
///
/// ```text
/// I  : Pi (ps : Ps). Pi (is : Js). Sort u
/// c_j : Pi (ps : Ps). Pi (as : As_j). I ps ts_j
/// ```
#[derive(Clone, Debug)]
pub struct InductiveSpec {
    /// `I`
    pub name: String,
    /// The parameters `(ps : Ps)`, shared by all constructors.
    pub params: Context,
    /// The indices `(is : Js)`, which may differ between constructors.
    pub indices: Context,
    /// `u` in `Sort u`, the universe the inductive type lives in.
    pub universe_level: u64,
    pub constructors: Vec<ConstructorSpec>,
}

/// One constructor `c_j : Pi (ps : Ps). Pi (as : As_j). I ps ts_j` of an [`InductiveSpec`].
/// The parameters are implicit: they are taken from the inductive type.
#[derive(Clone, Debug)]
pub struct ConstructorSpec {
    /// `c_j`, which must be qualified as `I.name`.
    pub name: String,
    /// The fields `(as : As_j)`.
    pub fields: Context,
    /// The index terms `ts_j` in the result type `I ps ts_j`.
    pub result_indices: Vec<Term>,
}

// ---------------------------------------------------------------------------
// Output: what the kernel records about an accepted inductive type.
// ---------------------------------------------------------------------------

/// A checked inductive type, stored in `Kernel::inductives`.
/// This is the single source of truth used to generate and reduce recursors.
#[derive(Clone, Debug)]
pub struct InductiveInfo {
    /// `I`
    pub name: String,
    /// `(ps : Ps)`
    pub params: Context,
    /// `(is : Js)`
    pub indices: Context,
    /// `u` in `I : ... -> Sort u`.
    pub universe_level: u64,
    pub constructors: Vec<ConstructorInfo>,
    /// Whether `I.rec_v` may be generated for `v >= 1`. Always true for `u >= 1`;
    /// for a proposition (`u = 0`) only when it is a subsingleton.
    pub large_elimination: bool,
}

/// A checked constructor `c_j`, with its recursive fields identified.
#[derive(Clone, Debug)]
pub struct ConstructorInfo {
    /// `c_j`
    pub name: String,
    /// `(as : As_j)`
    pub fields: Context,
    /// `ts_j`
    pub result_indices: Vec<Term>,
    /// The fields whose type mentions `I`, in field order. Each one gets an
    /// induction hypothesis in the minor premise of the recursor.
    pub recursive_fields: Vec<RecursiveFieldInfo>,
}

/// A recursive field, i.e. a field of the strictly positive form
///
/// ```text
/// a_k : Pi (ys : Bs). I ps ss
/// ```
///
/// When `ys` is empty this is just `a_k : I ps ss`, like the field of `Nat.succ`.
#[derive(Clone, Debug)]
pub struct RecursiveFieldInfo {
    /// `k`: the position of `a_k` among the constructor's fields.
    pub constructor_field_index: usize,
    /// `(ys : Bs)`: the arguments of the field, when the field is a function.
    pub argument_binders: Context,
    /// `ss`: the indices of the inductive type the field returns.
    pub target_indices: Vec<Term>,
}

/// Recursor-specific data for `I.rec_v`. The constructors, parameters, and
/// indices are not copied here; they are looked up in the [`InductiveInfo`]
/// of `inductive`.
#[derive(Clone, Debug)]
pub struct RecursorInfo {
    /// `I`
    pub inductive: String,
    /// `v` in `I.rec_v`: the motive has type `... -> Sort v`.
    pub elimination_universe: u64,
    /// 0-based position of the major premise `x` in
    /// `I.rec_v ps M ms is x`, i.e. `|ps| + 1 + |ms| + |is|`.
    pub major_argument_index: usize,
}
