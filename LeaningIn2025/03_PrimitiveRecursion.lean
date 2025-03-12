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

-- And here is their recursor
/-
info: recursor Nat.rec.{u} :
  {motive : Nat → Sort u} →
  (zero : motive Nat.zero) →
  (succ : (n : Nat) → motive n → motive n.succ) →
  (t : Nat) → motive t
-/
-- #print Nat.rec

/-
Addition on Nat, the usual way:

```
def add (a b : Nat) : Nat := match a with
  | .zero => b
  | .succ a' => Nat.succ (add a' b)
```

Using the recursor, we can define it without recurion:
-/

def add (n1 n2 : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    (zero := n2)
    (succ := fun _n1' add_n1' => Nat.succ add_n1')
    n1

/-
And it works!
-/

/-- info: 35 -/
#guard_msgs in
#reduce add 12 23
