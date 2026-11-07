module

public import ArithmeticTriangles.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace ArithmeticTriangles

/-- The proposed classification list. Arithmeticity of all entries is
proved in `VerifiedCandidates.lean`; completeness is proved in `Classification.lean`.
This module defines the finite list and its elementary properties independently. -/
def expectedArithmeticTriples : Finset Triangle :=
  {⟨2, 3, 7⟩, ⟨2, 3, 9⟩, ⟨2, 3, 11⟩, ⟨2, 5, 5⟩, ⟨2, 7, 7⟩,
   ⟨3, 3, 4⟩, ⟨3, 3, 5⟩, ⟨3, 3, 6⟩, ⟨3, 3, 7⟩,
   ⟨3, 3, 8⟩, ⟨3, 3, 9⟩, ⟨3, 3, 12⟩, ⟨3, 3, 15⟩,
   ⟨4, 4, 4⟩, ⟨5, 5, 5⟩, ⟨6, 6, 6⟩, ⟨7, 7, 7⟩,
   ⟨8, 8, 8⟩, ⟨9, 9, 9⟩, ⟨12, 12, 12⟩, ⟨15, 15, 15⟩,
   ⟨3, 5, 5⟩, ⟨4, 5, 5⟩, ⟨5, 5, 10⟩, ⟨5, 5, 15⟩}

theorem expectedArithmeticTriples_card : expectedArithmeticTriples.card = 25 := by
  decide

theorem expectedArithmeticTriples_admissible :
    ∀ triangle ∈ expectedArithmeticTriples, triangle.Admissible := by
  intro triangle membership
  unfold expectedArithmeticTriples at membership
  fin_cases membership <;> norm_num [Triangle.Admissible]

theorem expectedArithmeticTriples_right_or_isosceles :
    ∀ triangle ∈ expectedArithmeticTriples, triangle.Right ∨ triangle.Isosceles := by
  intro triangle membership
  unfold expectedArithmeticTriples at membership
  fin_cases membership <;> norm_num [Triangle.Right, Triangle.Isosceles]

theorem expectedArithmeticTriples_hyperbolic (triangle : Triangle)
    (membership : triangle ∈ expectedArithmeticTriples) : triangle.Hyperbolic := by
  unfold expectedArithmeticTriples at membership
  fin_cases membership <;> norm_num [Triangle.Hyperbolic]

end ArithmeticTriangles
