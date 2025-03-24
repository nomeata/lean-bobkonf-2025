import Mathlib

def PolyN (α : Type*) (n : Nat) := Vector α n

instance [Zero α] : GetElem (PolyN α m) ℕ α (fun _ _ => True) where
  getElem u i _ :=
    if h : i < m then
      Vector.get u ⟨i, h⟩
    else
      0

instance [Add α] : Add (PolyN α n) where
  add u v := u.zipWith (· + ·) v

instance[Zero α] [Add α] [Mul α] : HMul (PolyN α m) (PolyN α n) (PolyN α (m + n - 1)) where
  hMul u v := Vector.ofFn fun i => Id.run do
    let mut c := 0
    for j in [:i+1] do
      c := c + u[j] * v[i - j]
    return c

def MyPoly (α : Type*) := Array α


def v1 : PolyN Int 3 := #v[1,2,3]
def v2 : PolyN Int 4 := #v[4,5,6,7]

/-- info: { toArray := #[4, 13, 28, 34, 32, 21], size_toArray := _ } -/
#guard_msgs in
#eval v1 * v2

@[ext]
theorem PolyN_ext [Zero α] (u v : PolyN α n)
    (h : ∀ (i : Nat), i < n → u[i] = v[i]) :
    (u = v) := by
  apply Vector.ext
  intro i h'
  specialize h i
  simp [GetElem.getElem, h'] at h
  exact h

@[simp]
theorem MyPolyN.get_add [Zero α] [AddSemigroup α] (u v : PolyN α n) (i : Nat) :
    (u + v)[i] = u[i] + v[i] := by
  simp [GetElem.getElem]
  split
  · apply Vector.getElem_zipWith
  · sorry -- wrong assumptions!

instance [Zero α] [AddSemigroup α] : AddSemigroup (PolyN α n) where
  add_assoc u v w := by
    ext i hi
    simp [add_assoc]
