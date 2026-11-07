module

public import ArithmeticTriangles.TotalReality
public import ArithmeticTriangles.TraceEmbeddings
public import ArithmeticTriangles.ArithmeticConsequences
public import ArithmeticTriangles.QuadraticCases

/-!
# Real trace formulas and arithmetic bounds

Total reality supplies the missing bridge between the complex trace formula
and the arithmetic condition, which is stated using real embeddings.
For an arithmetic triple we obtain `Tr(D) ≤ D < 16`.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- For this totally real field, the real embeddings also count the degree. -/
theorem real_embeddings_card (triangle : Triangle) :
    Fintype.card (triangle.cosineField →ₐ[ℚ] ℝ) = triangle.deg := by
  rw [Fintype.card_congr triangle.realComplexEmbeddingEquiv]
  exact triangle.complex_embeddings_card

/-- Trace as a sum over real embeddings, retaining multiplicities of values. -/
theorem fieldTrace_eq_sum_real_embeddings (triangle : Triangle) (x : triangle.cosineField) :
    (triangle.fieldTrace x : ℝ) = ∑ σ : triangle.cosineField →ₐ[ℚ] ℝ, σ x := by
  have h := triangle.fieldTrace_eq_sum_complex_embeddings x
  have hs := Fintype.sum_equiv triangle.realComplexEmbeddingEquiv
    (fun σ : triangle.cosineField →ₐ[ℚ] ℝ => (σ x : ℂ))
    (fun σ : triangle.cosineField →ₐ[ℚ] ℂ => σ x) (fun σ => rfl)
  rw [← hs] at h
  exact_mod_cast h

/-- All summands other than the distinguished inclusion are negative. -/
theorem ArithmeticHyperbolic.trace_le_discriminant {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) :
    (triangle.discriminantTrace : ℝ) ≤ triangle.discriminant := by
  classical
  rw [discriminantTrace, triangle.fieldTrace_eq_sum_real_embeddings]
  have hother : ∀ σ ∈ Finset.univ.erase triangle.cosineField.val,
      σ triangle.fieldDiscriminant ≤ 0 := by
    intro σ hσ
    have hne : σ ≠ triangle.cosineField.val := (Finset.mem_erase.mp hσ).1
    exact le_of_lt ((triangle.discriminantAt_eq_embedding σ) ▸ h.2.2 σ hne)
  have hsum := Finset.sum_nonpos hother
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (fun σ : triangle.cosineField →ₐ[ℚ] ℝ => σ triangle.fieldDiscriminant)
    (Finset.mem_univ triangle.cosineField.val)
  change _ + triangle.discriminant = _ at hsplit
  linarith

/-- The trace bound from PDF §2.3, now unconditional for arithmetic triples. -/
theorem ArithmeticHyperbolic.trace_lt_sixteen {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) : (triangle.discriminantTrace : ℝ) < 16 :=
  h.trace_le_discriminant.trans_lt (triangle.discriminant_lt_sixteen h.admissible)

/-- If the degree exceeds one, at least one negative summand occurs. -/
theorem ArithmeticHyperbolic.trace_lt_discriminant_of_one_lt_deg
    {triangle : Triangle} (h : triangle.ArithmeticHyperbolic)
    (hdeg : 1 < triangle.deg) : (triangle.discriminantTrace : ℝ) < triangle.discriminant := by
  classical
  rw [discriminantTrace, triangle.fieldTrace_eq_sum_real_embeddings]
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card
    (triangle.real_embeddings_card ▸ hdeg) triangle.cosineField.val
  have hother : ∀ τ ∈ Finset.univ.erase triangle.cosineField.val,
      τ triangle.fieldDiscriminant ≤ 0 := by
    intro τ hτ
    exact le_of_lt ((triangle.discriminantAt_eq_embedding τ) ▸
      h.2.2 τ (Finset.mem_erase.mp hτ).1)
  have hsum : (∑ τ ∈ Finset.univ.erase triangle.cosineField.val,
      τ triangle.fieldDiscriminant) < 0 :=
    Finset.sum_neg' hother ⟨σ, Finset.mem_erase.mpr ⟨hσ, Finset.mem_univ σ⟩,
      (triangle.discriminantAt_eq_embedding σ) ▸ h.2.2 σ hσ⟩
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (fun τ : triangle.cosineField →ₐ[ℚ] ℝ => τ triangle.fieldDiscriminant)
    (Finset.mem_univ triangle.cosineField.val)
  change _ + triangle.discriminant = _ at hsplit
  linarith

/-- An integer strictly below 16 is at most 15. No lower bound is asserted. -/
theorem ArithmeticHyperbolic.trace_eq_integer_le_fifteen {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) :
    ∃ z : ℤ, triangle.discriminantTrace = (z : ℚ) ∧ z ≤ 15 := by
  obtain ⟨z, hz⟩ := triangle.discriminantTrace_eq_integer
  refine ⟨z, hz, ?_⟩
  have ht := h.trace_lt_sixteen
  rw [hz] at ht
  have : z < 16 := by exact_mod_cast ht
  omega

/-- The sharper bound from PDF §2.3 when the first denominator is four. -/
theorem ArithmeticHyperbolic.trace_lt_twelve_of_first_four {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) (he : triangle.e = 4) :
    (triangle.discriminantTrace : ℝ) < 12 := by
  have hd := triangle.discriminant_lt_generator_bound h.admissible
  rw [he] at hd
  have hs := cosineGenerator_four_sq
  have ha : cosineGenerator 4 < 3 / 2 := by
    nlinarith [sq_nonneg (cosineGenerator 4 - 3 / 2)]
  have hb : triangle.discriminant < 12 := by nlinarith
  exact h.trace_le_discriminant.trans_lt hb

end ArithmeticTriangles.Triangle
