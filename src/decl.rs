use crate::term::Term;

// A kernel maintains a global context of named declarations and inductive families.
pub type Context = Vec<(String, Term)>;

// A declaration is a named type and a kind (axiom, definition, inductive, constructor, or recursor).
#[derive(Clone, Debug)]
pub enum DeclKind {
    Axiom,
    Definition(Term),
    Inductive,
    Constructor,
    Recursor { spec: RecursorInfo },
}

// A declaration is a named type and a kind (axiom, definition, inductive, constructor, or recursor).
#[derive(Clone, Debug)]
pub struct Decl {
    pub ty: Term,
    pub kind: DeclKind,
}

// A constructor specification, with its name, fields, and result indices.
#[derive(Clone, Debug)]
pub struct ConstructorSpec {
    pub name: String,
    pub fields: Context,
    pub result_indices: Vec<Term>,
}

// A checked surface declaration. Parameters and indices form dependent telescopes.
#[derive(Clone, Debug)]
pub struct InductiveSpec {
    pub name: String,
    pub params: Context,
    pub indices: Context,
    pub sort: u64,
    pub constructors: Vec<ConstructorSpec>,
}

// A checked surface declaration. Parameters and indices form dependent telescopes.
#[derive(Clone, Debug)]
pub struct RecursiveField {
    pub field_index: usize,
    pub binders: Context,
    pub indices: Vec<Term>,
}

// A checked surface declaration. Parameters and indices form dependent telescopes.
#[derive(Clone, Debug)]
pub struct ConstructorInfo {
    pub name: String,
    pub fields: Context,
    pub result_indices: Vec<Term>,
    pub recursive: Vec<RecursiveField>,
}

// A family specification, with its parameters, indices, sort, constructors, and large elimination flag.
#[derive(Clone, Debug)]
pub struct FamilyInfo {
    pub params: Context,
    pub indices: Context,
    pub sort: u64,
    pub constructors: Vec<ConstructorInfo>,
    pub large_elimination: bool,
}

// A recursor specification, with its inductive type, parameters, indices, constructors, level, and major index.
#[derive(Clone, Debug)]
pub struct RecursorInfo {
    pub inductive: String,
    pub params: Context,
    pub indices: Context,
    pub constructors: Vec<ConstructorInfo>,
    pub level: u64,
    pub major_index: usize,
}
