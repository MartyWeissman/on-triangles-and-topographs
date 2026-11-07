module

public import ArithmeticTriangles.Structural
public import ArithmeticTriangles.RealTrace
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Even-denominator symmetry and vanishing trace

For even N=lcm(e,f,g), the index N+1 acts on each generator by a sign.
Its image lies in the cosine field itself, so the real embedding becomes
an automorphism of order two when e>2. The fixed-field theorem makes [F:ℚ]
even. Arithmeticity forces the automorphism to negate abc. Invariance of field
trace then gives Tr(abc)=0 without enumerating embeddings.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- If a real embedding sends the generators back into F, it sends every
field element back into F. Adjoin induction follows field operations. -/
theorem embedding_mem_of_generator_mem (t : Triangle) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (ha : σ t.firstGenerator ∈ t.cosineField)
    (hb : σ t.secondGenerator ∈ t.cosineField)
    (hc : σ t.thirdGenerator ∈ t.cosineField) (x : t.cosineField) :
    σ x ∈ t.cosineField := by
  rcases x with ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  | algebraMap q =>
    change σ (algebraMap ℚ t.cosineField q) ∈ t.cosineField
    rw [σ.commutes]
    exact t.cosineField.algebraMap_mem q
  | add x y hx hy ihx ihy =>
    change σ (⟨x, hx⟩ + ⟨y, hy⟩) ∈ t.cosineField
    rw [map_add]
    exact t.cosineField.add_mem ihx ihy
  | inv x hx ih =>
    change σ (⟨x, hx⟩⁻¹) ∈ t.cosineField
    rw [map_inv₀]
    exact t.cosineField.inv_mem ih
  | mul x y hx hy ihx ihy =>
    change σ (⟨x, hx⟩ * ⟨y, hy⟩) ∈ t.cosineField
    rw [map_mul]
    exact t.cosineField.mul_mem ihx ihy

/-- Restrict the codomain from ℝ to F using the preceding membership proof. -/
noncomputable def embeddingEndomorphism (t : Triangle) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (ha : σ t.firstGenerator ∈ t.cosineField)
    (hb : σ t.secondGenerator ∈ t.cosineField)
    (hc : σ t.thirdGenerator ∈ t.cosineField) : t.cosineField →ₐ[ℚ] t.cosineField :=
  σ.codRestrict t.cosineField.toSubalgebra (t.embedding_mem_of_generator_mem σ ha hb hc)

/-- An endomorphism of a finite extension of ℚ is automatically bijective:
it is injective as a field map and surjective by finite dimensionality. -/
noncomputable def embeddingAutomorphism (t : Triangle) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (ha : σ t.firstGenerator ∈ t.cosineField)
    (hb : σ t.secondGenerator ∈ t.cosineField)
    (hc : σ t.thirdGenerator ∈ t.cosineField) : t.cosineField ≃ₐ[ℚ] t.cosineField :=
  AlgEquiv.ofBijective (t.embeddingEndomorphism σ ha hb hc) (AlgHom.bijective _)

@[simp] theorem coe_embeddingAutomorphism (t : Triangle) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (ha : σ t.firstGenerator ∈ t.cosineField)
    (hb : σ t.secondGenerator ∈ t.cosineField)
    (hc : σ t.thirdGenerator ∈ t.cosineField) (x : t.cosineField) :
    (t.embeddingAutomorphism σ ha hb hc x : ℝ) = σ x := rfl

/-- The sign formula places the image of a cosine generator back inside F. -/
theorem even_embedding_cosine_mem (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) (n : ℕ) (hdvd : n ∣ t.commonDenominator)
    (x : t.cosineField) (hx : (x : ℝ) = cosineGenerator n) :
    t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN) x ∈
      t.cosineField := by
  rw [t.even_embedding_cosine h hN n hdvd x hx, ← hx]
  exact t.cosineField.mul_mem
    (t.cosineField.toSubalgebra.pow_mem
      (t.cosineField.neg_mem t.cosineField.one_mem) _) x.property

/-- The even-N symmetry, now an automorphism F ≃ₐ[ℚ] F. -/
noncomputable def evenAutomorphism (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) : t.cosineField ≃ₐ[ℚ] t.cosineField :=
  t.embeddingAutomorphism
    (t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN))
    (t.even_embedding_cosine_mem h hN _ (Nat.dvd_lcm_left _ _) _ rfl)
    (t.even_embedding_cosine_mem h hN _
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl)
    (t.even_embedding_cosine_mem h hN _
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl)

/-- The automorphism agrees with the real embedding after inclusion into ℝ. -/
@[simp] theorem coe_evenAutomorphism (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) (x : t.cosineField) :
    (t.evenAutomorphism h hN x : ℝ) =
      t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN) x := rfl

/-- The sign action as an equality inside F, usable with field operations. -/
theorem evenAutomorphism_cosine (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) (n : ℕ) (hdvd : n ∣ t.commonDenominator)
    (x : t.cosineField) (hx : (x : ℝ) = cosineGenerator n) :
    t.evenAutomorphism h hN x = (-1 : t.cosineField)^(t.commonDenominator/n) * x := by
  apply t.cosineField.val.injective
  simpa [hx] using t.even_embedding_cosine h hN n hdvd x hx

/-- Applying the same sign change twice fixes each generator. -/
theorem evenAutomorphism_twice_cosine (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) (n : ℕ) (hdvd : n ∣ t.commonDenominator)
    (x : t.cosineField) (hx : (x : ℝ) = cosineGenerator n) :
    t.evenAutomorphism h hN (t.evenAutomorphism h hN x) = x := by
  rw [t.evenAutomorphism_cosine h hN n hdvd x hx, map_mul, map_pow, map_neg, map_one,
    t.evenAutomorphism_cosine h hN n hdvd x hx]
  simp [← mul_assoc, ← pow_add, ← two_mul, pow_mul]

/-- Since a, b, c generate F, the automorphism is an involution on all of F. -/
theorem evenAutomorphism_involutive (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) : Function.Involutive (t.evenAutomorphism h hN) := by
  let τ := t.evenAutomorphism h hN
  have heq : τ.toAlgHom.comp τ.toAlgHom = AlgHom.id ℚ t.cosineField :=
    t.embedding_ext _ _
      (t.evenAutomorphism_twice_cosine h hN _ (Nat.dvd_lcm_left _ _) _ rfl)
      (t.evenAutomorphism_twice_cosine h hN _
        ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl)
      (t.evenAutomorphism_twice_cosine h hN _
        ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl)
  intro x
  exact DFunLike.congr_fun heq x

/-- With e>2, this involution is nonidentity. -/
theorem evenAutomorphism_ne_one (t : Triangle) (h : t.Admissible)
    (he : 2 < t.e) (hN : Even t.commonDenominator) : t.evenAutomorphism h hN ≠ 1 := by
  intro heq
  apply t.even_embedding_ne_inclusion h he hN
  ext x
  change (t.evenAutomorphism h hN x : ℝ) = (x : ℝ)
  rw [heq]
  rfl

/-- The subgroup generated by the involution has order two. Its fixed field
has index two, which divides [F:ℚ] by the tower law. Arithmeticity is not needed. -/
theorem even_deg_of_even_denominator (t : Triangle) (h : t.Admissible)
    (he : 2 < t.e) (hN : Even t.commonDenominator) : Even t.deg := by
  let τ := t.evenAutomorphism h hN
  have hs : τ ^ 2 = 1 := by
    apply AlgEquiv.ext
    intro x
    change τ (τ x) = x
    exact t.evenAutomorphism_involutive h hN x
  have ho : orderOf τ = 2 := orderOf_eq_prime hs (t.evenAutomorphism_ne_one h he hN)
  have hc : Nat.card (Subgroup.zpowers τ) = 2 := by rw [Nat.card_zpowers, ho]
  have hd := Module.finrank_dvd_finrank_left ℚ
    (IntermediateField.fixedField (Subgroup.zpowers τ)) t.cosineField
  rw [IntermediateField.finrank_fixedField_eq_card, hc] at hd
  exact even_iff_two_dvd.mpr hd

/-- The product abc, viewed as an element of the cosine field. -/
noncomputable def fieldGeneratorProduct (t : Triangle) : t.cosineField :=
  t.firstGenerator * t.secondGenerator * t.thirdGenerator

/-- Arithmeticity forces the even-N automorphism to negate abc. -/
theorem ArithmeticHyperbolic.evenAutomorphism_product {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.evenAutomorphism h.admissible hN t.fieldGeneratorProduct = -t.fieldGeneratorProduct := by
  let σ := t.cyclotomicRealEmbedding h.admissible (t.commonDenominator + 1)
    (even_index_coprime _ hN)
  have ha := t.even_embedding_cosine h.admissible hN _ (Nat.dvd_lcm_left _ _)
    t.firstGenerator rfl
  have hb := t.even_embedding_cosine h.admissible hN _
    ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) t.secondGenerator rfl
  have hc := t.even_embedding_cosine h.admissible hN _
    ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl
  have hp := t.product_neg_of_square_preserving h σ
    (t.even_embedding_ne_inclusion h.admissible he hN)
    (by rw [ha, mul_pow, sign_pow_sq, one_mul])
    (by rw [hb, mul_pow, sign_pow_sq, one_mul])
    (by rw [hc, mul_pow, sign_pow_sq, one_mul])
  apply t.cosineField.val.injective
  simpa [fieldGeneratorProduct, σ, firstGenerator, secondGenerator, thirdGenerator] using hp

/-- Trace is unchanged by an automorphism. If that automorphism negates an
element, its trace equals its own negative and must be zero in ℚ. -/
theorem fieldTrace_eq_zero_of_automorphism_neg (t : Triangle)
    (τ : t.cosineField ≃ₐ[ℚ] t.cosineField) (x : t.cosineField) (hx : τ x = -x) :
    t.fieldTrace x = 0 := by
  have ht := Algebra.trace_eq_of_algEquiv τ x
  rw [hx, map_neg] at ht
  change -t.fieldTrace x = t.fieldTrace x at ht
  linarith

/-- The trace-of-abc assertion in PDF Lemma 2.2. -/
theorem ArithmeticHyperbolic.product_trace_zero {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.fieldTrace t.fieldGeneratorProduct = 0 :=
  t.fieldTrace_eq_zero_of_automorphism_neg (t.evenAutomorphism h.admissible hN) _
    (h.evenAutomorphism_product he hN)

/-- Vanishing of Tr(abc) leaves three square traces and Tr(4)=4[F:ℚ].
The explicit Möbius/totient values of the square traces are a later step. -/
theorem ArithmeticHyperbolic.discriminantTrace_eq_square_traces {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.discriminantTrace = t.fieldTrace (t.firstGenerator ^ 2) +
      t.fieldTrace (t.secondGenerator ^ 2) + t.fieldTrace (t.thirdGenerator ^ 2) - 4 * t.deg := by
  have hp := h.product_trace_zero he hN
  have hfour : Algebra.trace ℚ t.cosineField (4 : t.cosineField) = 4 * t.deg := by
    have ht := Algebra.trace_algebraMap (R := ℚ) (S := t.cosineField) (4 : ℚ)
    simpa [deg, mul_comm] using ht
  unfold discriminantTrace fieldDiscriminant ArithmeticTriangles.discriminant fieldTrace
  rw [map_sub, map_add, map_add, map_add, hfour]
  change _ + _ + _ + t.fieldTrace t.fieldGeneratorProduct - _ = _
  rw [hp, add_zero]

/-- The numerical conclusion d≤10 in Lemma 2.3, CONDITIONAL on its trace
lower bound. With e=4, Tr(D)<12 already suffices without degree parity. -/
theorem ArithmeticHyperbolic.deg_le_ten_of_trace_lower_bound {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : t.e = 4)
    (hlower : (7 : ℝ) / 6 * t.deg ≤ (t.discriminantTrace : ℝ)) : t.deg ≤ 10 := by
  have hupper := h.trace_lt_twelve_of_first_four he
  have hd : (t.deg : ℝ) < 11 := by linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast hd)

/-- The numerical conclusion d≤12 in Lemma 2.3, CONDITIONAL on its trace
lower bound. Tr(D)<16 gives d<14, and evenness rules out d=13. -/
theorem ArithmeticHyperbolic.deg_le_twelve_of_trace_lower_bound {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator)
    (hlower : (7 : ℝ) / 6 * t.deg ≤ (t.discriminantTrace : ℝ)) : t.deg ≤ 12 := by
  have hupper := h.trace_lt_sixteen
  have hd : (t.deg : ℝ) < 14 := by linarith
  have hd' : t.deg < 14 := by exact_mod_cast hd
  obtain ⟨k, hk⟩ := t.even_deg_of_even_denominator h.admissible he hN
  omega

end ArithmeticTriangles.Triangle
