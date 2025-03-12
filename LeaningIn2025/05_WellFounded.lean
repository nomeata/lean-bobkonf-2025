/-!
Well-founded recursion
======================

You might want to define recursive functions
that are not structurally recursive.

Consider the following function to check if
all elements in an `Array` are the same:
-/

def areAllSame (arr : Array Nat) (i : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame arr (i + 1)
    else
      false
  else
    true
termination_by arr.size - i
decreasing_by
  omega

/-
It is not structural recursive (`i` gets larger as we go).

But there exists a *decreasing measure*:
The expression `arr.size - i` gets smaller in the recursive call.
We specify the measure in the `termination_by` clause.

For this to go through, we have prove to Lean that the measure is decreasing,
this happens in the `decreasing_by` clause.
-/

/-
Automatic recursion proofs
--------------------------

In many cases, Lean will automatically infer the termination measure
and/or the termination proof.
-/

def areAllSame' (arr : Array Nat) (i : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame' arr (i + 1)
    else
      false
  else
    true

/-
Use `termination_by?` to inspect the termination measure.
-/

/-
Lexicographic order
-------------------
The termination measure can be more complex, saying something like
“either `a` gets smaller, or `a` stays the same and `b` gets smaller”.

Classic example: The Ackermann funcion.
-/

def ackermann : (a b : Nat) → Nat
  | 0, b => b + 1
  | a + 1, 0 => ackermann a 1
  | a + 1, b + 1 => ackermann a (ackermann (a + 1) b)
-- termination_by?

/-
Downsides of well-founded recursion
---------------------------------

Well-founded recursion is (mostly) strictly more powerful than
structural recursion. So why ever use structural recursion?

1. No explicit proof needed

2. Good kernel reduction behavior.
   This is important for
    * defining types
    * kernel computation
      (e.g. evaluation using `rfl` or `by decide`).
-/
