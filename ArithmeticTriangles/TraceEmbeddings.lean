module

public import ArithmeticTriangles.Algebraic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Trace as a sum over complex embeddings

Finiteness and characteristic zero make the cosine field a finite separable
extension of ℚ. Mathlib's general trace theorem therefore applies, and its
number of embeddings into ℂ equals its degree.

The target here is ℂ, which is algebraically closed. Replacing this sum by a
sum over real embeddings uses total reality, proved in `TotalReality.lean`.
`RealTrace.lean` then derives `Tr(D) ≤ D` from the arithmetic sign condition.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- The degree counts complex embeddings, with each embedding counted once. -/
theorem complex_embeddings_card (triangle : Triangle) :
    Fintype.card (triangle.cosineField →ₐ[ℚ] ℂ) = triangle.deg :=
  AlgHom.card ℚ triangle.cosineField ℂ

/-- The field trace is the sum of the images under all complex embeddings. -/
theorem fieldTrace_eq_sum_complex_embeddings (triangle : Triangle)
    (value : triangle.cosineField) :
    (triangle.fieldTrace value : ℂ) =
      ∑ σ : triangle.cosineField →ₐ[ℚ] ℂ, σ value := by
  exact trace_eq_sum_embeddings (K := ℚ) (L := triangle.cosineField) (x := value) ℂ

/-- The same theorem specialized to the discriminant. Equal conjugate values
are retained with multiplicity because the sum is indexed by embeddings. -/
theorem discriminantTrace_eq_sum_complex_embeddings (triangle : Triangle) :
    (triangle.discriminantTrace : ℂ) =
      ∑ σ : triangle.cosineField →ₐ[ℚ] ℂ, σ triangle.fieldDiscriminant :=
  triangle.fieldTrace_eq_sum_complex_embeddings triangle.fieldDiscriminant

end ArithmeticTriangles.Triangle
