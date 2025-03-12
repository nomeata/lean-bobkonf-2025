/-
Lean has no recursive definition
================================

The logic implemented by Lean does not support recursion.
The Kernel will reject recursive definitions.

Let's try to define one anways…
(This is not how to use Lean )

-/

import Lean

open Lean Meta Elab Term

-- def test := fun (n : Nat) => test (n + 1)

/--
info: value: fun n => test (n + 1)
---
error: (kernel) unknown constant 'test'
-/
#guard_msgs in
run_elab
  let name := `test
  let type ← elabTerm (← `(Nat → Nat)) none
  let value ← withLocalDeclD `n (mkConst `Nat) fun n =>
    mkLambdaFVars #[n] <|
      mkApp (mkConst `test)
            (mkNatAdd n (mkNatLit 1))
  logInfo m!"value: {value}"
  Lean.addDecl (.defnDecl {
    name, type, value, levelParams := []
    hints := .regular 0, safety := .safe
  })

/-
Soundness
---------

Why is it so important that the Lean kernel does not simply
accept recursive definitions like other programming languages?

Because it would immediately break the soundness of the logic;
we could prove any propositon this way:
```
def reallyBad {P : Prop} : P := reallyBad
```
-/
