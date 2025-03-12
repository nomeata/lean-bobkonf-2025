/--
Nested recursion (bonus material)
=================================

Consider the following data structure:
A tree where a node has a value and a list of children.
-/

structure Tree (α : Type) where
  val : α
  children : List (Tree α)

/-
One often wants a `map` function for such a tree:
-/

def Tree.map (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun t => Tree.map f t) children⟩
termination_by t => t
decreasing_by
  trace_state
  decreasing_tactic

/-
Here, Lean knows that the `t` provided by `List.map` is indeed
a member of the list `children`: We get `t ∈ children` into scope.
-/

/-
Until recently, Lean did not know that:
-/
set_option wf.preprocess false


/--
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type
val : α
children : List (Tree α)
t : Tree α
⊢ sizeOf t < 1 + sizeOf children
-/
#guard_msgs in
def Tree.map' (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun t => Tree.map' f t) children⟩
termination_by t => t

/--
This required the user to use `List.attach` to inject the necessary information:
-/

def Tree.map'' (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun ⟨t, _h⟩ => Tree.map'' f t) (List.attach children)⟩
termination_by t => t
