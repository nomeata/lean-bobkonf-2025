
def IsPalindrome (xs : Array Nat) : Prop :=
  -- xs.reverse = xs
  Array.reverse xs = xs

def checkPalin (xs : Array Nat) : Bool := Id.run do
  for h : i in [0:xs.size] do
    have : i < xs.size := by
      exact Membership.get_elem_helper h rfl
    if ! xs[i] = xs[xs.size - 1 - i] then
      return false
  return true

/-- info: true -/
#guard_msgs in
#eval checkPalin #[1,2,3,2,1]

def helper (xs : Array Nat) (i : Nat) :=
  if h : i < xs.size / 2 then
    if xs[i] = xs[xs.size - 1 - i] then
      helper xs (i + 1)
    else
      false
  else
    true

def checkPalin' (xs : Array Nat) : Bool :=
  helper xs 0

theorem helper_correct :
    IsPalindrome xs → helper xs i = true := by
  intro h
  unfold IsPalindrome at h
  unfold helper
  split
  case isFalse =>
    rfl
  case isTrue =>
    rw [if_pos]
    case hc => calc xs[i]
       _ = xs.reverse[i]'(by simp; omega) := by simp [h]
       _ = xs[xs.size - 1 - i] := by simp
    apply helper_correct
    exact h

theorem checkPalin'_correct :
  IsPalindrome xs → checkPalin' xs = true := by
  intro h
  unfold checkPalin'
  apply helper_correct
  assumption
