module

public import ArithmeticTriangles.IsoscelesCompleteness
public import ArithmeticTriangles.CosineDegree

/-!
# The field reduction for two equal smaller denominators

The smallest-conjugate estimate shows that an arithmetic (e,e,g), with
2<e<g, has no nonidentity embedding fixing c. We convert this embedding
statement into F=ℚ(c), using the general relation between field degree
and number of embeddings. Consequently C_e⊆C_g and [F:ℚ]=φ(2g)/2.

This does not yet prove e∣g, nor the subsequent relative-trace restrictions.
Those are remaining steps of the general isosceles completeness proof.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- In our totally real finite extension, uniqueness of the embedding fixing x
implies that x generates the field. Over K=ℚ(x), complex embeddings can be
viewed as real embeddings. There is at most one; separability says their
number is [F:K], so this degree is one. -/
theorem adjoin_eq_top_of_unique_real_embedding (t : Triangle) (x : t.cosineField)
    (hunique : ∀ σ : t.cosineField →ₐ[ℚ] ℝ, σ x = (x : ℝ) → σ = t.cosineField.val) :
    IntermediateField.adjoin ℚ ({x} : Set t.cosineField) = ⊤ := by
  let K := IntermediateField.adjoin ℚ ({x} : Set t.cosineField)
  let ι : t.cosineField →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp t.cosineField.val
  let : Algebra K ℂ := (ι.comp K.val).toAlgebra
  let : IsScalarTower ℚ K ℂ := IsScalarTower.of_algHom (ι.comp K.val)
  let : FiniteDimensional K t.cosineField := FiniteDimensional.right ℚ K t.cosineField
  let : Algebra.IsSeparable K t.cosineField := inferInstance
  have hall : ∀ σ : t.cosineField →ₐ[K] ℂ, σ.restrictScalars ℚ = ι := by
    intro σ
    let ρ := t.realEmbeddingOfComplex (σ.restrictScalars ℚ)
    have hρ : ρ x = (x : ℝ) := by
      apply Complex.ofReal_injective
      rw [t.coe_realEmbeddingOfComplex]
      have hc := σ.commutes (⟨x, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton x)⟩ : K)
      exact hc
    have heq := hunique ρ hρ
    apply AlgHom.ext
    intro y
    have hy := t.coe_realEmbeddingOfComplex (σ.restrictScalars ℚ) y
    change (ρ y : ℂ) = _ at hy
    rw [heq] at hy
    exact hy.symm
  have hsub : Subsingleton (t.cosineField →ₐ[K] ℂ) := by
    refine ⟨fun σ τ => ?_⟩
    apply AlgHom.ext
    intro y
    exact DFunLike.congr_fun ((hall σ).trans (hall τ).symm) y
  have hcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
  rw [AlgHom.card K t.cosineField ℂ] at hcard
  have hdpos := Module.finrank_pos (R := K) (M := t.cosineField)
  have hd : Module.finrank K t.cosineField = 1 := by omega
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp hd

/-- The field reduction F=C_g for the equal-smaller family. This is an actual
equality of intermediate fields of ℝ, not just equality of their degrees. -/
theorem ArithmeticHyperbolic.cosineField_eq_single_third {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hef : t.e = t.f) (hfg : t.f < t.g) :
    t.cosineField = singleCosineField t.g := by
  have htop := t.adjoin_eq_top_of_unique_real_embedding t.thirdGenerator
    (fun σ hfix => h.embedding_eq_inclusion_of_fixes_third_isosceles he hef hfg σ hfix)
  have hm := congrArg (fun K : IntermediateField ℚ t.cosineField => K.map t.cosineField.val) htop
  have hmap : (⊤ : IntermediateField ℚ t.cosineField).map t.cosineField.val = t.cosineField := by
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨y, hy⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton, hmap] at hm
  exact hm.symm

/-- In particular, C_e is a subfield of C_g. Turning this inclusion into
the integer divisibility e∣g is a separate conductor theorem. -/
theorem ArithmeticHyperbolic.single_first_le_single_third {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hef : t.e = t.f) (hfg : t.f < t.g) :
    singleCosineField t.e ≤ singleCosineField t.g := by
  rw [← h.cosineField_eq_single_third he hef hfg]
  exact t.singleCosineField_le t.e t.firstGenerator.property

/-- The full degree in this family is now the individual degree φ(2g)/2. -/
theorem ArithmeticHyperbolic.deg_eq_third_totient_of_isosceles_first {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hef : t.e = t.f) (hfg : t.f < t.g) :
    t.deg = (2 * t.g).totient / 2 := by
  unfold deg
  rw [h.cosineField_eq_single_third he hef hfg]
  exact singleCosineField_finrank t.g (h.admissible.1.trans
    (h.admissible.2.1.trans h.admissible.2.2))

end ArithmeticTriangles.Triangle
