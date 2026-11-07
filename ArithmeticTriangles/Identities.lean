module

public import ArithmeticTriangles.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace ArithmeticTriangles

theorem discriminant_right (b c : ℝ) :
    discriminant 0 b c = b ^ 2 + c ^ 2 - 4 := by
  unfold discriminant
  ring

theorem discriminant_isosceles_first (a c : ℝ) :
    discriminant a a c = (c + 2) * (a ^ 2 + c - 2) := by
  unfold discriminant
  ring

theorem discriminant_isosceles_last (a b : ℝ) :
    discriminant a b b = (a + 2) * (a + b ^ 2 - 2) := by
  unfold discriminant
  ring

theorem discriminant_equilateral (a : ℝ) :
    discriminant a a a = (a - 1) * (a + 2) ^ 2 := by
  unfold discriminant
  ring

theorem discriminant_two_unit_generators (c : ℝ) :
    discriminant 1 1 c = (c + 2) * (c - 1) := by
  unfold discriminant
  ring

/-- The algebraic identity behind the odd-conductor `D E` argument. -/
theorem discriminant_companion_product (a b c : ℝ) :
    discriminant (2 - a ^ 2) (2 - b ^ 2) (2 - c ^ 2) =
      discriminant a b c * companionDiscriminant a b c := by
  unfold discriminant companionDiscriminant
  ring

end ArithmeticTriangles
