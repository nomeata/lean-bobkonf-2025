import Lean

open Lean Meta Elab Term

/--
A very simple `def`-like command that elaborates the body
of the definition with the constant to define in the scope
as an axiom.

NB: Using `match` in the body will fail.
-/
elab "simple_def " n:ident " : " t:term " := " e:term : command => do
  Command.runTermElabM fun _ => do
    let name := n.getId
    withDeclName name do
      let type ← elabTerm t none
      let type ← instantiateMVars type
      let value ←
        withoutModifyingEnv $ do
          Lean.addDecl (.axiomDecl { name, levelParams := [], type, isUnsafe := false})
          withSaveInfoContext do
            let value ← elabTermEnsuringType e type
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars value
      Lean.addDecl (.defnDecl {
        name, type, value, levelParams := []
        hints := .regular 0, safety := .safe
    })
