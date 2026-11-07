module

public import ArithmeticTriangles.CyclotomicAction
public import ArithmeticTriangles.Embeddings

/-!
# All embeddings and the congruence identity test

Every real embedding of the triangle's full cosine field is induced by a
coprime index k modulo 2N. It is the distinguished inclusion exactly when
k is independently ±1 modulo 2e, 2f, and 2g (PDF equation (2.1)).

This gives an equivalent finite list of sign conditions for arithmeticity.
Indices can repeat embeddings; no step identifies embeddings by D-values.
The sign conditions themselves still require exact mathematical proofs.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The quadratic equation behind the cosine identity test: a nonzero root
is determined up to inversion by its sum with its inverse. -/
theorem root_add_inv_eq_iff {K : Type*} [Field K] {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x = y⁻¹ := by
  constructor
  · intro h
    have hz : (x - y) * (x - y⁻¹) = 0 := by
      field_simp at h ⊢
      linear_combination h
    simpa only [mul_eq_zero, sub_eq_zero] using hz
  · rintro (rfl | rfl)
    · rfl
    · simp [add_comm]

/-- Fixing 2cos(π/n) is equivalent to k≡±1 modulo 2n. We represent −1
by the natural number 2n−1, avoiding truncated subtraction of k−1. -/
theorem cosine_power_eq_iff (n k : ℕ) (hn : 2 ≤ n) :
    2 * Real.cos ((k : ℝ) * Real.pi / n) = cosineGenerator n ↔
      Nat.ModEq (2 * n) k 1 ∨ Nat.ModEq (2 * n) k (2 * n - 1) := by
  have hζ := cosineRoot_primitive n (by omega)
  have hzero : cosineRoot n ≠ 0 := Complex.exp_ne_zero _
  have hinv : (cosineRoot n)⁻¹ = cosineRoot n ^ (2 * n - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hζ.pow_eq_one]
  rw [← Complex.ofReal_inj, ← root_pow_add_inv, cosineGenerator_eq_root_add_inv,
    root_add_inv_eq_iff (pow_ne_zero _ hzero) hzero, hinv]
  conv_lhs => lhs; rhs; rw [← pow_one (cosineRoot n)]
  simp only [hζ.isOfFinOrder (by omega) |>.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]

namespace Triangle

/-- The three independent congruence tests for fixing the full cosine field.
The signs need not be the same at all three denominators. -/
def FixesCosines (t : Triangle) (k : ℕ) : Prop :=
  (Nat.ModEq (2 * t.e) k 1 ∨ Nat.ModEq (2 * t.e) k (2 * t.e - 1)) ∧
  (Nat.ModEq (2 * t.f) k 1 ∨ Nat.ModEq (2 * t.f) k (2 * t.f - 1)) ∧
  (Nat.ModEq (2 * t.g) k 1 ∨ Nat.ModEq (2 * t.g) k (2 * t.g - 1))

instance (t : Triangle) (k : ℕ) : Decidable (t.FixesCosines k) := by
  unfold FixesCosines
  infer_instance

/-- PDF (2.1): identity is tested on generators, then on root exponents. -/
theorem cyclotomicRealEmbedding_eq_inclusion_iff (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2 * t.commonDenominator)) :
    t.cyclotomicRealEmbedding h k hk = t.cosineField.val ↔ t.FixesCosines k := by
  unfold FixesCosines
  rw [t.embedding_eq_inclusion_iff,
    t.cyclotomicRealEmbedding_cosine h k hk t.e (Nat.dvd_lcm_left _ _)
      t.firstGenerator rfl,
    t.cyclotomicRealEmbedding_cosine h k hk t.f
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) t.secondGenerator rfl,
    t.cyclotomicRealEmbedding_cosine h k hk t.g
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl,
    cosine_power_eq_iff _ _ h.1,
    cosine_power_eq_iff _ _ (h.1.trans h.2.1),
    cosine_power_eq_iff _ _ (h.1.trans (h.2.1.trans h.2.2))]

/-- Every real embedding comes from an index 0≤k<2N coprime to 2N.
Extend its complexification to the ambient cyclotomic field. Its primitive
root image is a coprime power of our root; agreement on that generator
identifies the extension with the previously constructed power embedding. -/
theorem exists_cyclotomicRealEmbedding (t : Triangle) (h : t.Admissible)
    (σ : t.cosineField →ₐ[ℚ] ℝ) :
    ∃ k : ℕ, k < 2 * t.commonDenominator ∧
      ∃ hk : k.Coprime (2 * t.commonDenominator),
        σ = t.cyclotomicRealEmbedding h k hk := by
  let N := t.commonDenominator
  let : NeZero N := ⟨t.commonDenominator_ne_zero h⟩
  let K := cosineCyclotomicField N
  let : Algebra t.cosineField K := (t.toCyclotomic h).toAlgebra
  let : IsScalarTower ℚ t.cosineField K := IsScalarTower.of_algHom (t.toCyclotomic h)
  let : Algebra.IsAlgebraic t.cosineField K := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let σc : t.cosineField →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp σ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (E := K) σc
  have hprim : IsPrimitiveRoot (ψ (cyclotomicRoot N)) (2 * N) :=
    (cyclotomicRoot_primitive N).map_of_injective ψ.injective
  obtain ⟨k, hklt, hkpow⟩ := (cosineRoot_primitive N (NeZero.ne N)).eq_pow_of_pow_eq_one
    hprim.pow_eq_one
  have hk : k.Coprime (2 * N) := by
    rw [← hkpow] at hprim
    exact (cosineRoot_primitive N (NeZero.ne N)).pow_iff_coprime
      (by have := NeZero.pos N; omega) k |>.mp hprim
  have heq : ψ = (cosineCyclotomicField N).val.comp (cyclotomicPowAut N k hk).toAlgHom := by
    apply (cyclotomicRoot_primitive N).powerBasis ℚ |>.algHom_ext
    change ψ (cyclotomicRoot N) = _
    simp only [IsPrimitiveRoot.powerBasis_gen, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, cyclotomicPowAut_root, map_pow]
    exact hkpow.symm
  refine ⟨k, hklt, hk, ?_⟩
  apply AlgHom.ext
  intro x
  apply Complex.ofReal_injective
  have hx := DFunLike.congr_fun hψ x
  change ψ (t.toCyclotomic h x) = (σ x : ℂ) at hx
  rw [heq] at hx
  rw [cyclotomicRealEmbedding, coe_realEmbeddingOfComplex]
  exact hx.symm

/-- The explicit real value of D at the embedding indexed by k. -/
noncomputable def cyclotomicDiscriminant (t : Triangle) (k : ℕ) : ℝ :=
  ArithmeticTriangles.discriminant (2 * Real.cos ((k : ℝ) * Real.pi / t.e))
    (2 * Real.cos ((k : ℝ) * Real.pi / t.f))
    (2 * Real.cos ((k : ℝ) * Real.pi / t.g))

/-- The formula for D is obtained by substituting the three generator images. -/
theorem discriminantAt_cyclotomic (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2 * t.commonDenominator)) :
    t.discriminantAt (t.cyclotomicRealEmbedding h k hk) = t.cyclotomicDiscriminant k := by
  unfold discriminantAt cyclotomicDiscriminant
  rw [t.cyclotomicRealEmbedding_cosine h k hk t.e (Nat.dvd_lcm_left _ _)
      t.firstGenerator rfl,
    t.cyclotomicRealEmbedding_cosine h k hk t.f
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) t.secondGenerator rfl,
    t.cyclotomicRealEmbedding_cosine h k hk t.g
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl]

/-- A finite, exhaustive sign criterion. Only indices coprime to 2N and
failing the identity test require a negative discriminant. This is an
exact equivalence, not a numerical approximation or a decidability claim
for arbitrary real inequalities. -/
theorem arithmeticHyperbolic_iff_cyclotomic (t : Triangle) (h : t.Admissible) :
    t.ArithmeticHyperbolic ↔ t.Hyperbolic ∧
      ∀ k : Fin (2 * t.commonDenominator),
        (k : ℕ).Coprime (2 * t.commonDenominator) →
        ¬t.FixesCosines k → t.cyclotomicDiscriminant k < 0 := by
  constructor
  · intro ha
    refine ⟨ha.hyperbolic, fun k hk hfix => ?_⟩
    rw [← t.discriminantAt_cyclotomic h k hk]
    exact ha.2.2 _ (fun he => hfix ((t.cyclotomicRealEmbedding_eq_inclusion_iff h k hk).mp he))
  · rintro ⟨hhyp, hsign⟩
    refine ⟨h, hhyp, fun σ hne => ?_⟩
    obtain ⟨k, hklt, hk, rfl⟩ := t.exists_cyclotomicRealEmbedding h σ
    rw [t.discriminantAt_cyclotomic h k hk]
    exact hsign ⟨k, hklt⟩ hk
      (fun hfix => hne ((t.cyclotomicRealEmbedding_eq_inclusion_iff h k hk).mpr hfix))

end Triangle
end ArithmeticTriangles
