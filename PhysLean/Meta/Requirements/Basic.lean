/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

# Requirements

-/
@[expose] public section

open Lean
structure API where
  /-- The name of the API. -/
  name : String
  /-- The description of the API. -/
  description : String

structure Requirement where
  /-- The name of the requirement. -/
  name : String
  /-- The description of the requirement. -/
  description : String
  /-- The API that the requirement belongs to. -/
  api : API


syntax (name := Requirement_attr) "requirement" ident : attr

/-- The `requirement` attribute. -/
meta initialize Lean.registerBuiltinAttribute {
  name := `Requirement_attr
  descr := "The `Requirement` attribute is used to mark the declarations
    which are associated with a given requirement"
  add := fun decl stx _attrKind => do
    match stx with
    | `(attr| requirement $id) =>
      let env ← getEnv
      let reqName := id.getId
      let some reqInfo := env.find? reqName
        | throwError "unknown identifier '{reqName}'"
      let reqType := reqInfo.type
      unless reqType.isConstOf ``Requirement do
      throwError "'{reqName}' does not have type 'Requirement', has type '{reqType}'"
    | _ => throwError "unexpected syntax for requirement attribute"
  applicationTime := AttributeApplicationTime.beforeElaboration
}
