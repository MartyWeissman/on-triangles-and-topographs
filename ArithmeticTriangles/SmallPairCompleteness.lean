module

public import ArithmeticTriangles.SmallPairTrace
public import ArithmeticTriangles.VerifiedCandidates
public import ArithmeticTriangles.IntegerSigns

@[expose] public section
namespace ArithmeticTriangles

/-- The constant part of the initial-pair trace is uniformly positive. -/
theorem small_pair_constant_trace : ∀ e : Fin 11, 4 ≤ (e : ℕ) →
    (1 : ℚ) ≤ 2 + 4 * moebiusRatio e := by decide +kernel

namespace Triangle

/-- When 4≤e=f≤10 and g>210, the normalized discriminant trace is at least 1/2.
The variable root orders are large because 2g≤e·order for each cross term. -/
theorem ArithmeticHyperbolic.small_pair_trace_ge_half {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he4 : 4 ≤ t.e) (he10 : t.e ≤ 10)
    (hef : t.e = t.f) (hg : 210 < t.g) : (1 : ℚ) / 2 ≤ t.normalizedDiscriminantTrace := by
  let N := t.commonDenominator
  let : NeZero N := ⟨t.commonDenominator_ne_zero h.admissible⟩
  let K := cosineCyclotomicField N
  let ζ := cyclotomicRoot N
  let φ := t.toCyclotomic h.admissible
  let u := N / t.e
  let w := N / t.g
  have hN : 0 < N := NeZero.pos N
  have heD : t.e ∣ N := Nat.dvd_lcm_left _ _
  have hgD : t.g ∣ N := (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
  have heu : t.e * u = N := Nat.mul_div_cancel' heD
  have hgw : t.g * w = N := Nat.mul_div_cancel' hgD
  have hw : 0 < w := Nat.div_pos (Nat.le_of_dvd hN hgD) (by omega)
  have hwu : w ≤ u := Nat.div_le_div_left (by omega : t.e ≤ t.g) (by omega)
  have hwu2 : w ≤ 2*u := by omega
  have hζ := cyclotomicRoot_primitive N
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have ha : φ t.firstGenerator = rootPair ζ (u : ℕ) :=
    cyclotomic_cosine_eq_rootPair N t.e heD _ rfl
  have hc : φ t.thirdGenerator = rootPair ζ (w : ℕ) :=
    cyclotomic_cosine_eq_rootPair N t.g hgD _ rfl
  have hab : t.secondGenerator = t.firstGenerator := by
    apply Subtype.ext
    change cosineGenerator t.f = cosineGenerator t.e
    rw [hef]
  have htwo : Algebra.normalizedTrace ℚ K (2 : K) = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ K (2 : ℚ)
  have hta : Algebra.normalizedTrace ℚ K (rootPair ζ (2 * (u : ℤ))) = 2 * moebiusRatio t.e := by
    have ht := cyclotomic_normalizedTrace_cosine_sq N t.e heD (φ t.firstGenerator) rfl
    rw [ha, rootPair_sq ζ hz, map_add, htwo] at ht
    unfold moebiusRatio
    rw [mul_div_assoc] at ht
    dsimp only [K] at *
    linarith
  have htc : Algebra.normalizedTrace ℚ K (rootPair ζ (2 * (w : ℤ))) = 2 * moebiusRatio t.g := by
    have ht := cyclotomic_normalizedTrace_cosine_sq N t.g hgD (φ t.thirdGenerator) rfl
    rw [hc, rootPair_sq ζ hz, map_add, htwo] at ht
    unfold moebiusRatio
    rw [mul_div_assoc] at ht
    dsimp only [K] at *
    linarith
  have horder : ∀ q : ℕ, (q = 2*u+w ∨ q+w = 2*u) → 42 < 2*N / (2*N).gcd q := by
    intro q hq
    have hh := cross_root_order_bound N t.e t.g u w q hN (by omega) hw heu hgw hq
    nlinarith
  have hp := normalizedTrace_rootPair_ge_neg_tenth (2*N) (by omega) ζ hζ (2*u+w)
    (horder _ (Or.inl rfl))
  have hm := normalizedTrace_rootPair_ge_neg_tenth (2*N) (by omega) ζ hζ (2*u-w)
    (horder _ (Or.inr (Nat.sub_add_cancel hwu2)))
  have how : 2*N / (2*N).gcd w = 2*t.g := by
    have hd : w ∣ 2*N := ⟨2*t.g, by nlinarith [hgw]⟩
    rw [Nat.gcd_eq_right hd, ← hgw, show 2 * (t.g * w) = (2*t.g)*w by ring,
      Nat.mul_div_cancel _ hw]
  have hv := normalizedTrace_rootPair_ge_neg_tenth (2*N) (by omega) ζ hζ w (by rw [how]; omega)
  have hbase := small_pair_constant_trace ⟨t.e, by omega⟩ he4
  have hratio := moebiusRatio_ge_neg_twentieth t.g (by omega)
  have hD : φ t.fieldDiscriminant =
      2 + rootPair ζ (2*(u:ℤ)) + rootPair ζ (2*(u:ℤ)) + rootPair ζ (2*(w:ℤ)) +
        rootPair ζ ((2*u+w : ℕ) : ℤ) + rootPair ζ ((2*u-w : ℕ) : ℤ) +
        rootPair ζ (w : ℕ) + rootPair ζ (w : ℕ) := by
    have heq : φ t.fieldDiscriminant = ArithmeticTriangles.discriminant (φ t.firstGenerator)
        (φ t.firstGenerator) (φ t.thirdGenerator) := by
      simp [fieldDiscriminant, ArithmeticTriangles.discriminant, hab, map_ofNat]
    rw [heq, ha, hc, discriminant_rootPairs ζ hz]
    push_cast [Nat.cast_sub hwu2]
    congr 2 <;> congr 1 <;> ring_nf
  have heq : t.normalizedDiscriminantTrace = Algebra.normalizedTrace ℚ K (φ t.fieldDiscriminant) := by
    rw [Algebra.normalizedTrace_map, Algebra.normalizedTrace_eq_of_finiteDimensional_apply]
    simp [normalizedDiscriminantTrace, discriminantTrace, fieldTrace, deg, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, hD]
  simp only [map_add, htwo, hta, htc]
  linarith

/-- The remaining small initial-pair families have a genuine unbounded-to-finite
reduction: arithmeticity forces g≤210. -/
theorem ArithmeticHyperbolic.last_le_210_of_small_initial_pair {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he4 : 4 ≤ t.e) (he10 : t.e ≤ 10)
    (hef : t.e = t.f) : t.g ≤ 210 := by
  by_contra hg
  have ht := h.small_pair_trace_ge_half he4 he10 hef (by omega)
  have hdpos : (0 : ℚ) < t.deg := by exact_mod_cast t.deg_pos
  rw [normalizedDiscriminantTrace, le_div_iff₀ hdpos] at ht
  have hupper : t.discriminantTrace < 16 := by exact_mod_cast h.trace_lt_sixteen
  have hd : t.deg ≤ 31 := by
    have : (t.deg : ℚ) < 32 := by linarith
    have : t.deg < 32 := by exact_mod_cast this
    omega
  have hφ := t.cosine_totient_le_twice_degree t.g
    (h.admissible.1.trans (h.admissible.2.1.trans h.admissible.2.2)) t.thirdGenerator.property
  have := denominator_le_105_of_totient_le_62 t.g (by omega)
  omega

end Triangle

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Exact completion of the bounded initial-pair box. -/
theorem small_initial_pair_sign_certificates :
    ∀ e : Fin 11, 4 ≤ (e : ℕ) →
    ∀ g : Fin 211, (e : ℕ) ≤ g →
      (⟨e, e, g⟩ : Triangle) ∈ expectedArithmeticTriples ∨
      ∃ k : Fin 32,
        (k : ℕ).Coprime (2 * (⟨e, e, g⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, e, g⟩ : Triangle).FixesCosines k ∧
        (⟨e, e, g⟩ : Triangle).integerDiscriminantSignCertificate k = 1 := by
  decide +kernel

namespace Triangle

/-- Complete necessity for the initial-pair branch with 4≤e≤10. -/
theorem ArithmeticHyperbolic.mem_expected_of_small_initial_pair {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he4 : 4 ≤ t.e) (he10 : t.e ≤ 10)
    (hef : t.e = t.f) : t ∈ expectedArithmeticTriples := by
  have hg := h.last_le_210_of_small_initial_pair he4 he10 hef
  have hle : t.e ≤ t.g := h.admissible.2.1.trans h.admissible.2.2
  rcases t with ⟨e, f, g⟩
  change e = f at hef
  subst f
  rcases small_initial_pair_sign_certificates ⟨e, by exact Nat.lt_succ_of_le he10⟩ he4
    ⟨g, by exact Nat.lt_succ_of_le hg⟩ hle with hm | ⟨k, hk, hfix, hcert⟩
  · exact hm
  · exact False.elim ((⟨e,e,g⟩ : Triangle).not_arithmeticHyperbolic_of_integer_sign_certificate
      h.admissible k hk hfix hcert h)

end Triangle
end ArithmeticTriangles
