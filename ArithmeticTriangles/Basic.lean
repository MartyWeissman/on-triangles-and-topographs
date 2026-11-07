module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ArithmeticTriangles

/-- The denominators of the angles `π/e`, `π/f`, and `π/g`.
Ordering and lower bounds are imposed separately by `Admissible`. -/
structure Triangle where
  e : ℕ
  f : ℕ
  g : ℕ
  deriving DecidableEq, Repr

namespace Triangle

def Admissible (triangle : Triangle) : Prop :=
  2 ≤ triangle.e ∧ triangle.e ≤ triangle.f ∧ triangle.f ≤ triangle.g

/-- For an admissible (ordered) triangle, the first angle is a right angle. -/
def Right (triangle : Triangle) : Prop := triangle.e = 2

def Equilateral (triangle : Triangle) : Prop :=
  triangle.e = triangle.f ∧ triangle.f = triangle.g

/-- Isosceles includes equilateral triangles. Under `Admissible`, equality
of the first and third denominators already forces equality of all three. -/
def Isosceles (triangle : Triangle) : Prop :=
  triangle.e = triangle.f ∨ triangle.f = triangle.g ∨ triangle.e = triangle.g

def Scalene (triangle : Triangle) : Prop :=
  triangle.e ≠ triangle.f ∧ triangle.f ≠ triangle.g ∧ triangle.e ≠ triangle.g

def Hyperbolic (triangle : Triangle) : Prop :=
  1 / (triangle.e : ℝ) + 1 / (triangle.f : ℝ) + 1 / (triangle.g : ℝ) < 1

def Spherical (triangle : Triangle) : Prop :=
  1 < 1 / (triangle.e : ℝ) + 1 / (triangle.f : ℝ) + 1 / (triangle.g : ℝ)

theorem equilateral_is_isosceles (triangle : Triangle)
    (equilateral : triangle.Equilateral) : triangle.Isosceles :=
  Or.inl equilateral.1

/-- The cases used in the classification, with right triangles treated first. -/
theorem classification_cases (triangle : Triangle) (admissible : triangle.Admissible) :
    triangle.Right ∨
      (2 < triangle.e ∧
        (triangle.Equilateral ∨
          (triangle.e = triangle.f ∧ triangle.f < triangle.g) ∨
          (triangle.e < triangle.f ∧ triangle.f = triangle.g) ∨
          (triangle.e < triangle.f ∧ triangle.f < triangle.g))) := by
  unfold Admissible at admissible
  unfold Right Equilateral
  omega

theorem strictly_ordered_iff_scalene (triangle : Triangle)
    (admissible : triangle.Admissible) :
    (triangle.e < triangle.f ∧ triangle.f < triangle.g) ↔ triangle.Scalene := by
  unfold Admissible at admissible
  unfold Scalene
  omega

end Triangle

/-- Every cosine generator has the same factor of two. -/
noncomputable def cosineGenerator (denominator : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / (denominator : ℝ))

/-- The polynomial denoted by `D` in the paper. -/
def discriminant {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 + b ^ 2 + c ^ 2 + a * b * c - 4

/-- The companion polynomial denoted by `E` in the paper. -/
def companionDiscriminant {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 + b ^ 2 + c ^ 2 - a * b * c - 4

noncomputable def Triangle.discriminant (triangle : Triangle) : ℝ :=
  ArithmeticTriangles.discriminant (cosineGenerator triangle.e)
    (cosineGenerator triangle.f) (cosineGenerator triangle.g)

end ArithmeticTriangles
