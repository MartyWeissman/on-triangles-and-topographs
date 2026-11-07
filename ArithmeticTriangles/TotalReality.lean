module

public import ArithmeticTriangles.Embeddings
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Total reality of the cosine field

The rescaled Chebyshev polynomial satisfies `Cₙ(2 cos θ)=2 cos(nθ)`.
Consequently our generator is a root of `Cₙ(X)+2`, a rational polynomial
whose complex roots are all real. Every embedding preserves this equation.

This proves total reality without needing the general cyclotomic Galois-group
calculation first. It does not enumerate embeddings by residue classes.
The final equivalence allows us to rewrite the complex trace as a real sum.
-/

@[expose] public section

namespace ArithmeticTriangles
open Polynomial.Chebyshev

/-- The rescaled Chebyshev identity `Cₙ(2 cos(π/n)) = -2`.
The index must be nonzero so that `n · (π/n) = π`. -/
theorem cosineGenerator_chebyshev (n : ℕ) (hn : n ≠ 0) :
    (C ℝ n).eval (cosineGenerator n) = -2 := by
  rw [cosineGenerator, C_two_mul_real_cos]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp [mul_div_cancel₀ _ hn']

/-- Every complex root of `Cₙ(X)+2` is real. Write the root as `2 cos θ`;
then `cos(nθ)=-1` forces `nθ` and hence θ to be real. -/
theorem chebyshev_root_im_zero (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (hz : (C ℂ n).eval z = -2) : z.im = 0 := by
  obtain ⟨θ, hθ⟩ := Complex.cos_surjective (z / 2)
  have hzθ : z = 2 * Complex.cos θ := by rw [hθ]; ring
  rw [hzθ, C_two_mul_complex_cos] at hz
  have hcos : Complex.cos ((n : ℂ) * θ) = -1 := by
    push_cast at hz
    linear_combination hz / 2
  obtain ⟨k, hk⟩ := Complex.cos_eq_neg_one_iff.mp hcos
  have him : θ.im = 0 := by
    have hi := congrArg Complex.im hk
    simp at hi
    exact hi.resolve_left hn
  rw [hzθ]
  have hreal : θ = (θ.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [hreal, ← Complex.ofReal_cos]
  simp

namespace Triangle

/-- Transport the rational Chebyshev equation to any complex embedding.
The harmless denominator-zero convention is handled separately. -/
theorem embedding_cosine_im_zero (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℂ) (x : triangle.cosineField) (n : ℕ)
    (hx : (x : ℝ) = cosineGenerator n) : (σ x).im = 0 := by
  by_cases hn : n = 0
  · subst n
    have hfield : x = 2 := by
      apply triangle.cosineField.val.injective
      change (x : ℝ) = 2
      simpa [cosineGenerator] using hx
    simp [hfield, map_ofNat]
  · have hfield : Polynomial.aeval x (C ℚ n + 2) = 0 := by
      apply triangle.cosineField.val.injective
      change triangle.cosineField.val (Polynomial.aeval x (C ℚ n + 2)) = (0 : ℝ)
      rw [← Polynomial.aeval_algHom_apply]
      simp only [Polynomial.aeval_add, aeval_C, map_ofNat]
      change (C ℝ n).eval (x : ℝ) + 2 = 0
      rw [hx, cosineGenerator_chebyshev n hn]
      norm_num
    have hσ := triangle.embedding_preserves_polynomial σ (C ℚ n + 2) x hfield
    simp only [Polynomial.aeval_add, aeval_C, map_ofNat] at hσ
    apply chebyshev_root_im_zero n hn (σ x)
    linear_combination hσ

/-- Complex conjugation fixes the image of each generator, so it fixes the
entire embedding. Merely being a subfield of ℝ would not suffice for this. -/
theorem complex_embedding_isReal (triangle : Triangle) (σ : triangle.cosineField →ₐ[ℚ] ℂ) :
    NumberField.ComplexEmbedding.IsReal σ.toRingHom := by
  have h : (NumberField.ComplexEmbedding.conjugate σ.toRingHom).toRatAlgHom = σ := by
    apply triangle.embedding_ext
    · exact Complex.conj_eq_iff_im.mpr (embedding_cosine_im_zero triangle σ _ triangle.e rfl)
    · exact Complex.conj_eq_iff_im.mpr (embedding_cosine_im_zero triangle σ _ triangle.f rfl)
    · exact Complex.conj_eq_iff_im.mpr (embedding_cosine_im_zero triangle σ _ triangle.g rfl)
  exact congrArg AlgHom.toRingHom h

/-- Register the previously proved finite extension as a mathlib number field. -/
instance cosineField_numberField (triangle : Triangle) : NumberField triangle.cosineField where

/-- Total reality in mathlib's standard number-field interface. -/
instance cosineField_isTotallyReal (triangle : Triangle) :
    NumberField.IsTotallyReal triangle.cosineField where
  isReal w := NumberField.InfinitePlace.isReal_iff.mpr
    (complex_embedding_isReal triangle w.embedding.toRatAlgHom)

/-- Regard a complex embedding as a real embedding using total reality. -/
noncomputable def realEmbeddingOfComplex (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℂ) : triangle.cosineField →ₐ[ℚ] ℝ :=
  (complex_embedding_isReal triangle σ).embedding.toRatAlgHom

@[simp] theorem coe_realEmbeddingOfComplex (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℂ) (x : triangle.cosineField) :
    (triangle.realEmbeddingOfComplex σ x : ℂ) = σ x :=
  NumberField.ComplexEmbedding.IsReal.coe_embedding_apply (complex_embedding_isReal triangle σ) x

/-- Real and complex embeddings correspond bijectively. The forward map
composes with ℝ → ℂ; its inverse uses the now-proved real image. -/
noncomputable def realComplexEmbeddingEquiv (triangle : Triangle) :
    (triangle.cosineField →ₐ[ℚ] ℝ) ≃ (triangle.cosineField →ₐ[ℚ] ℂ) where
  toFun σ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp σ
  invFun := triangle.realEmbeddingOfComplex
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; exact triangle.coe_realEmbeddingOfComplex σ x

@[simp] theorem realComplexEmbeddingEquiv_apply (triangle : Triangle)
    (σ : triangle.cosineField →ₐ[ℚ] ℝ) (x : triangle.cosineField) :
    triangle.realComplexEmbeddingEquiv σ x = (σ x : ℂ) := rfl

end Triangle
end ArithmeticTriangles
