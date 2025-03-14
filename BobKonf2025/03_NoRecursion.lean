import BobKonf2025.SimpleDef

/-
Lean has no recursive definition
================================

The logic implemented by Lean does not support recursion.
The Kernel will reject recursive definitions.

Let's try to define one anways…
(The `simple_def` commands is a command I added.)

-/

simple_def foo : Nat → Nat :=
  fun n => (n + 1)

/-- error: (kernel) unknown constant 'bar' -/
#guard_msgs in
simple_def bar : Nat → Nat :=
  fun n => bar (n + 1)

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
