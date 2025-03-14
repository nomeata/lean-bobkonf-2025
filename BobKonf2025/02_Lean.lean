import Std

/-!
Lean
====

Lean
is a general purpose programming language:
-/

def histogram (filename : String) : IO Unit := do
  let ls ← IO.FS.lines filename
  let mut counts : Std.TreeMap String Nat := .empty
  for l in ls do
    counts := counts.insert l (counts[l]?.getD 0 + 1)
  let entries := counts.toArray.qsort (·.2 > ·.2)
  for (line, count) in entries do
    if count > 1 then
      IO.println s!"\"{line}\": {count}"

-- #eval histogram "BobKonf2025/02_Lean.lean"

/-
Lean
is an Interactive Theorem Prover:
-/

theorem sum_of_n (n : Nat) :
  (List.range (n + 1)).reverse.sum = n * (n + 1) / 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ]
    simp [ih, Nat.mul_add, Nat.add_mul]
    omega
