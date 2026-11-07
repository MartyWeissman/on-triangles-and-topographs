module

public import ArithmeticTriangles.VerifiedCandidates
public import ArithmeticTriangles.QuadraticCases
public import ArithmeticTriangles.SmallUnits

/-!
# Complete classification of the diagonal and initial-(3,3) families

The arithmetic triples (n,n,n) and (3,3,n) are exactly those with n in
S={4,5,6,7,8,9,12,15}. Sufficiency follows from the verified candidate list.
Necessity uses the small unit from Lemma 4.1: its cosine image is strictly
between 1 and the principal generator, so it gives a nonidentity embedding
with positive discriminant.

For (3,3,n), an index coprime to 2n need not be coprime to the common
ambient conductor. We explicitly replace it by k or k+2n to obtain an
ambient unit without changing its action on the nth cosine. This avoids
assuming that an arbitrary small-field index acts on the larger field.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- For 1<k<n/3, the kth cosine image remains above 1 but is strictly
below the principal generator. Monotonicity gives both strict inequalities. -/
theorem small_index_cosine_bounds (n k : ℕ) (hk1 : 1 < k) (hk3 : 3 * k < n) :
    1 < 2 * Real.cos ((k : ℝ) * Real.pi / n) ∧
      2 * Real.cos ((k : ℝ) * Real.pi / n) < cosineGenerator n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk : (1 : ℝ) < k := by exact_mod_cast hk1
  have hkn : 3 * (k : ℝ) < n := by exact_mod_cast hk3
  have hangle : (k : ℝ) * Real.pi / n < Real.pi / 3 := by
    apply (div_lt_iff₀ hn).mpr
    nlinarith [Real.pi_pos]
  have hpos : 0 ≤ (k : ℝ) * Real.pi / n := by positivity
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hpos
    (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hangle
  rw [Real.cos_pi_div_three] at hcos
  have hangle' : Real.pi / n < (k : ℝ) * Real.pi / n := by
    apply (div_lt_div_iff_of_pos_right hn).mpr
    nlinarith [Real.pi_pos]
  have hcos' := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / n)
    (show (k : ℝ) * Real.pi / n ≤ Real.pi by linarith [Real.pi_pos]) hangle'
  unfold cosineGenerator
  constructor <;> linarith

/-- A small coprime index is a forbidden embedding for the diagonal family:
D=(u−1)(u+2)² is positive, and the generator has changed. -/
theorem not_equilateral_arithmetic_of_small_unit (n k : ℕ)
    (hk1 : 1 < k) (hk3 : 3 * k < n) (hk : k.Coprime (2 * n)) :
    ¬(⟨n, n, n⟩ : Triangle).ArithmeticHyperbolic := by
  intro h
  let t : Triangle := ⟨n, n, n⟩
  have hk' : k.Coprime (2 * t.commonDenominator) := by
    simpa [t, Triangle.commonDenominator] using hk
  let σ := t.cyclotomicRealEmbedding h.admissible k hk'
  have hu := small_index_cosine_bounds n k hk1 hk3
  have hc : σ t.thirdGenerator = 2 * Real.cos ((k : ℝ) * Real.pi / n) :=
    t.cyclotomicRealEmbedding_cosine h.admissible k hk' n
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl
  have hne : σ ≠ t.cosineField.val := by
    intro heq
    have he := DFunLike.congr_fun heq t.thirdGenerator
    rw [hc] at he
    exact (ne_of_lt hu.2) he
  have hneg := h.2.2 σ hne
  change discriminant (σ t.thirdGenerator) (σ t.thirdGenerator) (σ t.thirdGenerator) < 0 at hneg
  rw [discriminant_equilateral, hc] at hneg
  have hp : 0 < (2 * Real.cos ((k : ℝ) * Real.pi / n) - 1) *
      (2 * Real.cos ((k : ℝ) * Real.pi / n) + 2) ^ 2 :=
    mul_pos (by linarith [hu.1]) (sq_pos_of_pos (by linarith [hu.1]))
  exact (not_lt_of_gt hp) hneg

/-- Lift a unit modulo 2n to the conductor for (3,3,n). If 3 divides k,
then coprimality implies 3 does not divide n, so k+2n avoids the prime 3.
Otherwise k itself works. Both choices have the same nth cosine image. -/
theorem lift_unit_for_three_pair (n k : ℕ) (hk : k.Coprime (2 * n)) :
    ∃ j : ℕ, j.Coprime (2 * (⟨3, 3, n⟩ : Triangle).commonDenominator) ∧
      (j = k ∨ j = k + 2 * n) := by
  have hdvd : 2 * (⟨3, 3, n⟩ : Triangle).commonDenominator ∣ 3 * (2 * n) := by
    have hN : (⟨3, 3, n⟩ : Triangle).commonDenominator ∣ 3 * n := by
      apply Nat.lcm_dvd (Nat.dvd_mul_right 3 n)
      exact Nat.lcm_dvd (Nat.dvd_mul_right 3 n) (Nat.dvd_mul_left n 3)
    convert Nat.mul_dvd_mul_left 2 hN using 1
    ring
  by_cases h3 : 3 ∣ k
  · have h3n : ¬3 ∣ n := by
      intro hn
      have hd : 3 ∣ Nat.gcd k (2 * n) := Nat.dvd_gcd h3 (dvd_mul_of_dvd_right hn 2)
      rw [hk.gcd_eq_one] at hd
      omega
    have hj3 : (k + 2 * n).Coprime 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)).symm
    have hjn : (k + 2 * n).Coprime (2 * n) := by
      simpa using (Nat.coprime_add_mul_right_left k (2 * n) 1).mpr hk
    exact ⟨k + 2 * n, (hj3.mul_right hjn).of_dvd_right hdvd, Or.inr rfl⟩
  · have hk3 : k.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
    exact ⟨k, (hk3.mul_right hk).of_dvd_right hdvd, Or.inl rfl⟩

/-- Adding 2n to an index adds 2π to the nth cosine angle. -/
theorem cosine_index_add_two_mul (n k : ℕ) (hn : n ≠ 0) :
    Real.cos (((k + 2 * n : ℕ) : ℝ) * Real.pi / n) =
      Real.cos ((k : ℝ) * Real.pi / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : ((k + 2 * n : ℕ) : ℝ) * Real.pi / n =
      (k : ℝ) * Real.pi / n + 2 * Real.pi := by
    push_cast
    field_simp
  rw [he, Real.cos_add_two_pi]

/-- A lifted small unit is a forbidden embedding for (3,3,n).
The first two generators equal 1, and D=(u+2)(u−1) stays positive. -/
theorem not_initial_three_pair_arithmetic_of_small_unit (n k : ℕ)
    (hk1 : 1 < k) (hk3 : 3 * k < n) (hk : k.Coprime (2 * n)) :
    ¬(⟨3, 3, n⟩ : Triangle).ArithmeticHyperbolic := by
  intro h
  let t : Triangle := ⟨3, 3, n⟩
  obtain ⟨j, hj, hchoice⟩ := lift_unit_for_three_pair n k hk
  let σ := t.cyclotomicRealEmbedding h.admissible j hj
  have hu := small_index_cosine_bounds n k hk1 hk3
  have hc : σ t.thirdGenerator = 2 * Real.cos ((k : ℝ) * Real.pi / n) := by
    rw [t.cyclotomicRealEmbedding_cosine h.admissible j hj n
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl]
    rcases hchoice with rfl | rfl
    · rfl
    · rw [cosine_index_add_two_mul n k (by omega)]
  have ha : t.firstGenerator = 1 := by
    apply t.cosineField.val.injective
    exact cosineGenerator_three
  have hb : t.secondGenerator = 1 := by
    apply t.cosineField.val.injective
    exact cosineGenerator_three
  have hne : σ ≠ t.cosineField.val := by
    intro heq
    have he := DFunLike.congr_fun heq t.thirdGenerator
    rw [hc] at he
    exact (ne_of_lt hu.2) he
  have hneg := h.2.2 σ hne
  change discriminant (σ t.firstGenerator) (σ t.secondGenerator) (σ t.thirdGenerator) < 0 at hneg
  rw [ha, hb, map_one, hc, discriminant_two_unit_generators] at hneg
  have hp : 0 < (2 * Real.cos ((k : ℝ) * Real.pi / n) + 2) *
      (2 * Real.cos ((k : ℝ) * Real.pi / n) - 1) :=
    mul_pos (by linarith [hu.1]) (by linarith [hu.1])
  exact (not_lt_of_gt hp) hneg

/-- Necessity for the diagonal family, including the small geometric boundary.
Admissibility and hyperbolicity force n≥4 before the unit lemma applies. -/
theorem equilateral_denominator_mem_of_arithmetic (n : ℕ)
    (h : (⟨n, n, n⟩ : Triangle).ArithmeticHyperbolic) : n ∈ repeatedDenominators := by
  have hn4 : 4 ≤ n := by
    have hn2 := h.admissible.1
    have hh := h.hyperbolic
    change 2 ≤ n at hn2
    by_contra hn
    have hn3 : n ≤ 3 := by omega
    interval_cases n <;> norm_num [Triangle.Hyperbolic] at hh
  by_contra hnot
  obtain ⟨k, hk1, hk3, hk⟩ := exists_small_unit_of_not_mem n hn4 hnot
  exact not_equilateral_arithmetic_of_small_unit n k hk1 hk3 hk h

/-- Necessity for the initial pair (3,3); n=3 is Euclidean, not hyperbolic. -/
theorem initial_three_pair_denominator_mem_of_arithmetic (n : ℕ)
    (h : (⟨3, 3, n⟩ : Triangle).ArithmeticHyperbolic) : n ∈ repeatedDenominators := by
  have hn4 : 4 ≤ n := by
    have hn3 := h.admissible.2.2
    have hh := h.hyperbolic
    change 3 ≤ n at hn3
    by_contra hn
    have heq : n = 3 := by omega
    subst n
    norm_num [Triangle.Hyperbolic] at hh
  by_contra hnot
  obtain ⟨k, hk1, hk3, hk⟩ := exists_small_unit_of_not_mem n hn4 hnot
  exact not_initial_three_pair_arithmetic_of_small_unit n k hk1 hk3 hk h

/-- Complete classification of all diagonal triples, with no prior bound on n. -/
theorem equilateral_arithmetic_iff (n : ℕ) :
    (⟨n, n, n⟩ : Triangle).ArithmeticHyperbolic ↔ n ∈ repeatedDenominators := by
  constructor
  · exact equilateral_denominator_mem_of_arithmetic n
  · intro hn
    apply expectedArithmeticTriples_arithmeticHyperbolic
    unfold repeatedDenominators at hn
    fin_cases hn <;> decide

/-- Complete classification of all triples (3,3,n), with no prior bound on n. -/
theorem initial_three_pair_arithmetic_iff (n : ℕ) :
    (⟨3, 3, n⟩ : Triangle).ArithmeticHyperbolic ↔ n ∈ repeatedDenominators := by
  constructor
  · exact initial_three_pair_denominator_mem_of_arithmetic n
  · intro hn
    apply expectedArithmeticTriples_arithmeticHyperbolic
    unfold repeatedDenominators at hn
    fin_cases hn <;> decide

namespace Triangle

/-- The diagonal branch of the final completeness argument is closed. -/
theorem ArithmeticHyperbolic.mem_expected_of_equilateral {t : Triangle}
    (h : t.ArithmeticHyperbolic) (heq : t.Equilateral) : t ∈ expectedArithmeticTriples := by
  rcases t with ⟨e, f, g⟩
  obtain ⟨hef, hfg⟩ := heq
  change e = f at hef
  change f = g at hfg
  subst f
  subst g
  have hn := equilateral_denominator_mem_of_arithmetic e h
  unfold repeatedDenominators at hn
  fin_cases hn <;> decide

/-- The branch with initial entries (3,3) is also closed. -/
theorem ArithmeticHyperbolic.mem_expected_of_initial_three_pair {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : t.e = 3) (hf : t.f = 3) : t ∈ expectedArithmeticTriples := by
  rcases t with ⟨e, f, g⟩
  change e = 3 at he
  change f = 3 at hf
  subst e
  subst f
  have hn := initial_three_pair_denominator_mem_of_arithmetic g h
  unfold repeatedDenominators at hn
  fin_cases hn <;> decide

end Triangle
end ArithmeticTriangles
