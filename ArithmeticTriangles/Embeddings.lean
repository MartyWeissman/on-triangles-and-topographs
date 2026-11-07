module

public import ArithmeticTriangles.Algebraic

/-!
# Working with embeddings of the cosine field

An embedding is a ℚ-algebra homomorphism: it fixes rational numbers and
preserves addition and multiplication. Two elementary tools turn this
abstract definition into usable conjugate calculations:

* embeddings agreeing on the three generators agree everywhere;
* an embedding carries a root of a rational polynomial to another root.

Neither assertion says that arbitrary choices of roots extend to an
embedding. Compatibility and existence require additional arguments.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- To compare embeddings it suffices to compare the images of `a`, `b`, `c`.
This works with any commutative algebra as target, including ℝ and ℂ. -/
theorem embedding_ext (triangle : Triangle) {K : Type*} [CommSemiring K] [Algebra ℚ K]
    (σ τ : triangle.cosineField →ₐ[ℚ] K)
    (ha : σ triangle.firstGenerator = τ triangle.firstGenerator)
    (hb : σ triangle.secondGenerator = τ triangle.secondGenerator)
    (hc : σ triangle.thirdGenerator = τ triangle.thirdGenerator) : σ = τ := by
  apply IntermediateField.adjoin_algHom_ext ℚ
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- Fixing all three real generators is exactly being the distinguished inclusion.
This spells out the identity test which precedes the congruence test (2.1). -/
theorem embedding_eq_inclusion_iff (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℝ) :
    σ = triangle.cosineField.val ↔
      σ triangle.firstGenerator = cosineGenerator triangle.e ∧
      σ triangle.secondGenerator = cosineGenerator triangle.f ∧
      σ triangle.thirdGenerator = cosineGenerator triangle.g := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc⟩
    exact triangle.embedding_ext σ triangle.cosineField.val ha hb hc

/-- Rational polynomial relations survive under every embedding. -/
theorem embedding_preserves_polynomial (triangle : Triangle) {K : Type*}
    [CommRing K] [Algebra ℚ K] (σ : triangle.cosineField →ₐ[ℚ] K)
    (p : Polynomial ℚ) (x : triangle.cosineField)
    (hx : Polynomial.aeval x p = 0) : Polynomial.aeval (σ x) p = 0 := by
  rw [Polynomial.aeval_algHom_apply, hx, map_zero]

/-- A practical quadratic specialization, starting from an equation in ℝ.
First pull the equation into the cosine field, then apply the embedding. -/
theorem embedding_preserves_square (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℝ) (x : triangle.cosineField) (k : ℕ)
    (hx : (x : ℝ) ^ 2 = (k : ℝ)) : (σ x) ^ 2 = (k : ℝ) := by
  have hfield : x ^ 2 = (k : triangle.cosineField) := by
    apply triangle.cosineField.val.injective
    simpa using hx
  simpa using congrArg σ hfield

/-- If an element has a rational integer square, each real embedding sends
it to either its original value or its negative. -/
theorem embedding_eq_or_eq_neg_of_square (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℝ) (x : triangle.cosineField) (k : ℕ)
    (hx : (x : ℝ) ^ 2 = (k : ℝ)) : σ x = (x : ℝ) ∨ σ x = -(x : ℝ) := by
  have hs : (σ x) ^ 2 = (x : ℝ) ^ 2 :=
    (triangle.embedding_preserves_square σ x k hx).trans hx.symm
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp hs

end ArithmeticTriangles.Triangle
