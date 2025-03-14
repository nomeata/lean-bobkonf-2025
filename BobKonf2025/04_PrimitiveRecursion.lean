/-!

Primitive recursion
===================

How do we then express recursion?

We use *recursors*. For every inductive data,
there exists a recursor that can be used to define
primitively recursive definitions.
-/

-- Natural numbers are an inductive definition:

namespace JustToRecall

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

end JustToRecall

-- And this is the recursor for natural numbers:

/--
info: Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) : motive t
-/
#guard_msgs (whitespace := lax) in
#check Nat.rec
-- #print Nat.rec

/-
Addition on Nat, the usual way:

```
def add (a b : Nat) : Nat :=
  match a with
  | .zero => b
  | .succ a' => Nat.succ (add a' b)
```

Using the recursor, we can define it without recursion:
-/

def add (a b : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    (zero := b)
    (succ := fun _a' add_a'_b => Nat.succ add_a'_b)
    a

/-
And it works!
-/

/-- info: 35 -/
#guard_msgs in
#reduce add 12 23
