set_option grind.warning false

@[simp] def divBy2 : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => divBy2 n + 1
termination_by structural x => x

theorem divBy2_mul : divBy2 (2 * n) = n := by
  induction n
  case zero =>
    simp
  case succ ih =>
    simp [Nat.mul_add, ih]


theorem divBy2_le : divBy2 n ≤ n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n' + 2 =>
    calc divBy2 (n' + 2)
      _ = divBy2 n' + 1 := by rw [divBy2]
      _ ≤ n' + 1 := by
        apply Nat.add_le_add_right
        exact divBy2_le
      _ ≤ n' + 2 := by simp


theorem divBy2_le' : divBy2 n ≤ n := by
  sleep 10000
  fun_induction divBy2 <;> grind [= divBy2]
  --  fun_induction divBy2 <;> grind [divBy2]

def divBy2' (n : Nat) : Nat :=
  if n < 2 then
    0
  else
    divBy2' (n - 2) + 1
termination_by n


theorem divBy2_le'' : divBy2' n ≤ n := by
  fun_induction divBy2' <;> grind [= divBy2']
