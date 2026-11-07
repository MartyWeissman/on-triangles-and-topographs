module

public import ArithmeticTriangles.CyclotomicTrace
public import Mathlib.Data.Nat.Squarefree

/-!
# The even-conductor degree bound

This proves PDF Lemma 2.3: for a scalene arithmetic triple with e≥4 and
N=lcm(e,f,g) even, the normalized discriminant trace is at least 7/6.
Consequently d≤10 when e=4, and d≤12 otherwise.

The estimate for arbitrary large denominators is reduced to a finite check
by proving that squarefree n with φ(n)<8 divides 210. The two finite checks
use `decide +kernel`: exact reduction in Lean's kernel, not native execution.
A local recursion-depth allowance accommodates these bounded reductions.
-/

@[expose] public section

namespace ArithmeticTriangles

set_option maxRecDepth 4096 in
/-- Among divisors of 210, every n≥6 other than 7 with μ(n)=−1 has
φ(n)≥8. The finite index includes all n≤210; divisibility restricts the
relevant values to the sixteen divisors. This is exact kernel reduction. -/
theorem small_totient_check : ∀ n : Fin 211, 6 ≤ (n : ℕ) → (n : ℕ) ≠ 7 →
    (n : ℕ) ∣ 210 → ArithmeticFunction.moebius n = -1 → 8 ≤ Nat.totient n := by
  simp only [ArithmeticFunction.moebius, ArithmeticFunction.coe_mk,
    ArithmeticFunction.cardFactors_apply]
  decide +kernel

/-- A squarefree n with φ(n)<8 divides 2*3*5*7. For each prime p∣n,
p−1=φ(p) divides φ(n), hence p<9. The only such primes are 2,3,5,7.
Squarefreeness lets us recover n from its set of prime factors. -/
theorem squarefree_dvd_210_of_totient_lt_eight (n : ℕ) (hs : Squarefree n)
    (ht : n.totient < 8) : n ∣ 210 := by
  rw [← Nat.prod_primeFactors_of_squarefree hs, Nat.prod_primeFactors_dvd_iff (by decide)]
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hφ := Nat.totient_dvd_of_dvd hpdvd
  rw [Nat.totient_prime hprime] at hφ
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hs.ne_zero)) hφ
  have hp8 : p < 9 := by omega
  have hsmall : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have hfinite : ∀ q : Fin 9, Nat.Prime q →
        (q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 5 ∨ (q : ℕ) = 7 := by decide
    exact hfinite ⟨p, hp8⟩ hprime
  apply Nat.mem_primeFactors.mpr
  refine ⟨hprime, ?_, by decide⟩
  rcases hsmall with rfl | rfl | rfl | rfl <;> decide

/-- The rational ratio μ(n)/φ(n) appearing in the normalized trace formula. -/
def moebiusRatio (n : ℕ) : ℚ := (ArithmeticFunction.moebius n : ℚ) / n.totient

set_option maxRecDepth 4096 in
/-- The bounded e=4,5 part of Lemma 2.3. Structural bounds will place
f below 10 and g below 30. This finite theorem assumes strict ordering and
even least common multiple, but does not assume arithmeticity. -/
theorem small_denominator_ratio_sum :
    ∀ e : Fin 6, 4 ≤ (e : ℕ) → ∀ f : Fin 10, (e : ℕ) < f →
      ∀ g : Fin 30, (f : ℕ) < g → Even ((e : ℕ).lcm ((f : ℕ).lcm g)) →
      -(5 : ℚ) / 12 ≤ moebiusRatio e + moebiusRatio f + moebiusRatio g := by
  decide +kernel

/-- The general negative-ratio estimate reduces to the bounded check:
μ(n)=−1 implies squarefreeness, and φ(n)<8 would force n∣210. -/
theorem totient_ge_eight_of_moebius_neg (n : ℕ) (hn : 6 ≤ n) (hne : n ≠ 7)
    (hμ : ArithmeticFunction.moebius n = -1) : 8 ≤ n.totient := by
  by_contra ht
  have hs : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (by omega)
  have hd := squarefree_dvd_210_of_totient_lt_eight n hs (by omega)
  have hle := Nat.le_of_dvd (by decide : 0 < 210) hd
  exact ht (small_totient_check ⟨n, by omega⟩ hn hne hd hμ)

/-- Away from n=7, all ratios for n≥6 are at least −1/8. Nonnegative μ
is immediate; μ=−1 uses the totient bound just proved. -/
theorem moebiusRatio_ge_neg_eighth (n : ℕ) (hn : 6 ≤ n) (hne : n ≠ 7) :
    -(1 : ℚ) / 8 ≤ moebiusRatio n := by
  rcases ArithmeticFunction.moebius_eq_or n with hμ | hμ | hμ
  · norm_num [moebiusRatio, hμ]
  · have hnonneg : 0 ≤ moebiusRatio n := by simp [moebiusRatio, hμ]
    linarith
  · have hφ := totient_ge_eight_of_moebius_neg n hn hne hμ
    have hφ' : (8 : ℚ) ≤ n.totient := by exact_mod_cast hφ
    have hpos : (0 : ℚ) < n.totient := by linarith
    unfold moebiusRatio
    rw [le_div_iff₀ hpos, hμ]
    norm_num
    linarith

/-- The weaker uniform bound includes n=7, where the ratio is exactly −1/6. -/
theorem moebiusRatio_ge_neg_sixth (n : ℕ) (hn : 6 ≤ n) :
    -(1 : ℚ) / 6 ≤ moebiusRatio n := by
  by_cases h7 : n = 7
  · subst n
    norm_num [moebiusRatio, ArithmeticFunction.moebius_apply_prime Nat.prime_seven,
      show Nat.totient 7 = 6 by decide]
  · linarith [moebiusRatio_ge_neg_eighth n hn h7]

/-- For three strictly increasing denominators at least 6, at most one
can be 7. Two ratios are therefore at least −1/8 and the third at least −1/6. -/
theorem large_denominator_ratio_sum (e f g : ℕ) (he : 6 ≤ e) (hef : e < f) (hfg : f < g) :
    -(5 : ℚ) / 12 ≤ moebiusRatio e + moebiusRatio f + moebiusRatio g := by
  have hf : 6 ≤ f := by omega
  have hg : 6 ≤ g := by omega
  by_cases he7 : e = 7
  · have ha := moebiusRatio_ge_neg_sixth e he
    have hb := moebiusRatio_ge_neg_eighth f hf (by omega)
    have hc := moebiusRatio_ge_neg_eighth g hg (by omega)
    linarith
  · have ha := moebiusRatio_ge_neg_eighth e he he7
    by_cases hf7 : f = 7
    · have hb := moebiusRatio_ge_neg_sixth f hf
      have hc := moebiusRatio_ge_neg_eighth g hg (by omega)
      linarith
    · have hb := moebiusRatio_ge_neg_eighth f hf hf7
      have hc := moebiusRatio_ge_neg_sixth g hg
      linarith

namespace Triangle

/-- The lower bound τ≥7/6 in PDF Lemma 2.3. Split at e=6: the small
case uses the structural bounds to enter a finite range; the large case uses
the uniform ratio estimates. Equation (2.10) converts the sum bound to τ. -/
theorem ArithmeticHyperbolic.normalizedTrace_ge_seven_sixths {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : 4 ≤ t.e)
    (hN : Even t.commonDenominator) : (7 : ℚ) / 6 ≤ t.normalizedDiscriminantTrace := by
  have he2 : 2 < t.e := by omega
  have hord := (t.strictly_ordered_iff_scalene h.admissible).mpr hs
  have hr : -(5 : ℚ) / 12 ≤ moebiusRatio t.e + moebiusRatio t.f + moebiusRatio t.g := by
    by_cases he6 : 6 ≤ t.e
    · exact large_denominator_ratio_sum _ _ _ he6 hord.1 hord.2
    · have hf := h.middle_lt_twice_first he2
      have hg := h.last_lt_first_mul_succ he2 hs
      have hg30 : t.g < 30 := by interval_cases t.e <;> norm_num at hg ⊢ <;> omega
      exact small_denominator_ratio_sum ⟨t.e, by omega⟩ he ⟨t.f, by omega⟩ hord.1
        ⟨t.g, hg30⟩ hord.2 hN
  rw [h.normalizedDiscriminantTrace_even he2 hN]
  unfold moebiusRatio at hr
  linarith

/-- Multiply the normalized lower bound by the positive field degree,
then include ℚ into ℝ to match the earlier upper-bound theorems. -/
theorem ArithmeticHyperbolic.trace_ge_degree_mul_seven_sixths {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : 4 ≤ t.e)
    (hN : Even t.commonDenominator) :
    (7 : ℝ) / 6 * t.deg ≤ (t.discriminantTrace : ℝ) := by
  have ht := h.normalizedTrace_ge_seven_sixths hs he hN
  have hd : (0 : ℚ) < t.deg := by exact_mod_cast t.deg_pos
  rw [normalizedDiscriminantTrace, le_div_iff₀ hd] at ht
  have ht' : (((7 : ℚ) / 6 * t.deg : ℚ) : ℝ) ≤ (t.discriminantTrace : ℝ) :=
    Rat.cast_le.mpr ht
  push_cast at ht'
  exact ht'

/-- The d≤10 conclusion of Lemma 2.3, with no extra trace hypothesis.
When e=4, evenness of N follows automatically because e divides N. -/
theorem ArithmeticHyperbolic.deg_le_ten_of_first_four {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : t.e = 4) : t.deg ≤ 10 := by
  have heven : 2 ∣ t.e := by rw [he]; decide
  have hN : Even t.commonDenominator :=
    even_iff_two_dvd.mpr (heven.trans (Nat.dvd_lcm_left _ _))
  exact h.deg_le_ten_of_trace_lower_bound he
    (h.trace_ge_degree_mul_seven_sixths hs (by omega) hN)

/-- The d≤12 conclusion of Lemma 2.3. This also holds for e=4, where
the preceding theorem gives the sharper bound. The proof uses degree parity. -/
theorem ArithmeticHyperbolic.deg_le_twelve_of_scalene_even {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : 4 ≤ t.e)
    (hN : Even t.commonDenominator) : t.deg ≤ 12 :=
  h.deg_le_twelve_of_trace_lower_bound (by omega) hN
    (h.trace_ge_degree_mul_seven_sixths hs he hN)

end Triangle
end ArithmeticTriangles
