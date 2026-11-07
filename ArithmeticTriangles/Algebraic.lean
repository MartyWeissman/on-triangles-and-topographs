module

public import ArithmeticTriangles.CosineField
public import Mathlib.NumberTheory.Niven
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Algebraicity, finite degree, and integral traces

The three generators are algebraic integers: `2 cos(π/n)` is the sum of
two roots of unity. Mathlib proves this for every rational multiple of π.
Adjoining finitely many algebraic elements gives a finite extension of ℚ.

This supplies the finiteness hypothesis that was deliberately absent from
the initial definitions of degree and trace. `TotalReality.lean` proves total
reality; `Cyclotomic.lean` constructs an ambient cyclotomic field. The cosine
field degree formula (2.4) still requires further work.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The normalized cosine is an algebraic integer, including at `n=0`
under Lean's convention that division by zero is zero. -/
theorem cosineGenerator_isIntegral_int (n : ℕ) : IsIntegral ℤ (cosineGenerator n) := by
  have h := Real.isIntegral_two_mul_cos_rat_mul_pi (1 / (n : ℚ))
  simpa [cosineGenerator, div_eq_mul_inv, mul_comm] using h

/-- Over the field ℚ, being integral is equivalent to being algebraic. -/
theorem cosineGenerator_isIntegral_rat (n : ℕ) : IsIntegral ℚ (cosineGenerator n) :=
  (cosineGenerator_isIntegral_int n).tower_top

namespace Triangle

/-- Three algebraic generators produce a finite-dimensional field extension.
No admissibility assumption is required for this foundational fact. -/
instance cosineField_finiteDimensional (triangle : Triangle) :
    FiniteDimensional ℚ triangle.cosineField := by
  unfold cosineField
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> exact cosineGenerator_isIntegral_rat _

/-- With finiteness established, `deg` is a positive natural number. -/
theorem deg_pos (triangle : Triangle) : 0 < triangle.deg :=
  Module.finrank_pos

theorem firstGenerator_isIntegral (triangle : Triangle) :
    IsIntegral ℤ triangle.firstGenerator := by
  apply (isIntegral_algebraMap_iff (B := ℝ)).mp
  exact cosineGenerator_isIntegral_int triangle.e

theorem secondGenerator_isIntegral (triangle : Triangle) :
    IsIntegral ℤ triangle.secondGenerator := by
  apply (isIntegral_algebraMap_iff (B := ℝ)).mp
  exact cosineGenerator_isIntegral_int triangle.f

theorem thirdGenerator_isIntegral (triangle : Triangle) :
    IsIntegral ℤ triangle.thirdGenerator := by
  apply (isIntegral_algebraMap_iff (B := ℝ)).mp
  exact cosineGenerator_isIntegral_int triangle.g

/-- The polynomial `D` has integer coefficients, so its value is integral. -/
theorem fieldDiscriminant_isIntegral (triangle : Triangle) :
    IsIntegral ℤ triangle.fieldDiscriminant := by
  have ha := triangle.firstGenerator_isIntegral
  have hb := triangle.secondGenerator_isIntegral
  have hc := triangle.thirdGenerator_isIntegral
  have hfour : IsIntegral ℤ (4 : triangle.cosineField) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := triangle.cosineField) (x := (4 : ℤ)))
  exact (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)).add ((ha.mul hb).mul hc) |>.sub hfour

/-- A finite-extension trace of an algebraic integer is an algebraic integer. -/
theorem discriminantTrace_isIntegral (triangle : Triangle) :
    IsIntegral ℤ triangle.discriminantTrace :=
  Algebra.isIntegral_trace triangle.fieldDiscriminant_isIntegral

/-- Since the trace lies in ℚ and is integral over ℤ, it is an integer.
This is an existence statement, not yet an evaluation of that integer. -/
theorem discriminantTrace_eq_integer (triangle : Triangle) :
    ∃ z : ℤ, triangle.discriminantTrace = (z : ℚ) := by
  have h := triangle.discriminantTrace_isIntegral
  obtain ⟨z, hz⟩ := h.mem_range_ratCast_iff.mp
    (show triangle.discriminantTrace ∈ Set.range (fun q : ℚ => (q : ℚ)) from
      ⟨triangle.discriminantTrace, rfl⟩)
  exact ⟨z, hz.symm⟩

end Triangle
end ArithmeticTriangles
