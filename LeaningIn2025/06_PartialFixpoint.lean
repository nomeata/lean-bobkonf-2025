/-!
Partial fixpoints
=================

The latest addition to the zoo of recursive function
definition mechanisms: `partial_fixpoint`.

No termination proof needed!
This allows non-terminating function specifications!

Mostly useful when verifying sofware or algorithms.
-/

/-
Here is an example of a function with a tricky termination proof:
-/

def f91 (n : Nat) : Option Nat :=
  if n > 100
    then pure (n - 10)
    else f91 (n + 11) >>= f91
partial_fixpoint

/-
Rules for `partial_fixpoint` (simplified):

* The function type returns an `Option`
* The function is constructed using monadic operations
  (bind, `do`-notation)

This defines the function and prove the equation.
The user can later, if they want, prove that the function
is total (i.e. never `none`)

More on this example on Zulip:
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/McCarthy.2091.20function.20using.20partial_fixpoint
-/
