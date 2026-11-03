//! Minimal, named-variable dependent-type kernel and proof-state engine.
//! This is a teaching implementation, not a production proof assistant.
//!
//! Suggested reading order, following the text:
//! [`term`] -> [`substitution`] -> [`typecheck`] -> [`reduction`] ->
//! [`declaration`] -> [`inductive`] -> [`proof`].
pub mod declaration;
pub mod inductive;
pub mod kernel;
pub mod proof;
pub mod reduction;
pub mod substitution;
pub mod syntax;
pub mod template;
pub mod term;
pub mod typecheck;
