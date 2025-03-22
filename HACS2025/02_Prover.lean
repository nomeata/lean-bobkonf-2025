/-
Lean is an Interactive Theorem Prover
=====================================
-/

theorem sum_of_n :
    (List.range (n + 1)).reverse.sum = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    simp [List.range_succ]
  | succ k ih =>
    rw [List.range_succ]
    simp [ih, Nat.mul_add, Nat.add_mul]
    omega
