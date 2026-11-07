module

public import ArithmeticTriangles.EvenSymmetry
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# The number of maximal 2-adic valuations is odd

The even-N symmetry changes the sign at position n exactly when N/n is odd.
For a divisor n of positive N, that is equivalent to ν₂(n)=ν₂(N).
Arithmeticity forces the product of the three signs to be -1, so an odd
number of positions attain the maximal valuation. Positions are counted
separately, including when two or all three denominators coincide.

Together with Structural and EvenSymmetry, this finishes the conclusions
of PDF Lemma 2.2. The explicit Möbius/totient trace evaluations remain open.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- A divisor n of positive N carries the full power of two in N exactly
when the remaining quotient is odd. -/
theorem odd_quotient_iff_twoAdic_eq (N n : ℕ) (hN : N ≠ 0) (hdvd : n ∣ N) :
    Odd (N / n) ↔ padicValNat 2 n = padicValNat 2 N := by
  obtain ⟨k, rfl⟩ := hdvd
  obtain ⟨hn, hk⟩ := mul_ne_zero_iff.mp hN
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), padicValNat.mul hn hk]
  have hzero : padicValNat 2 k = 0 ↔ Odd k := by
    simp [padicValNat.eq_zero_iff, hk, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  rw [← hzero]
  omega

namespace Triangle

/-- The product of the three signs is (-1) to the sum of the three quotients. -/
theorem evenAutomorphism_product_eq_sign (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) :
    t.evenAutomorphism h hN t.fieldGeneratorProduct =
      (-1 : t.cosineField) ^ (t.commonDenominator / t.e + t.commonDenominator / t.f +
        t.commonDenominator / t.g) * t.fieldGeneratorProduct := by
  unfold fieldGeneratorProduct
  rw [map_mul, map_mul,
    t.evenAutomorphism_cosine h hN _ (Nat.dvd_lcm_left _ _) t.firstGenerator rfl,
    t.evenAutomorphism_cosine h hN _
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) t.secondGenerator rfl,
    t.evenAutomorphism_cosine h hN _
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl]
  simp only [pow_add]
  ring

/-- For ordered denominators with e>2, all three generators are positive. -/
theorem fieldGeneratorProduct_pos (t : Triangle) (h : t.Admissible) (he : 2 < t.e) :
    0 < (t.fieldGeneratorProduct : ℝ) := by
  exact mul_pos (mul_pos (cosineGenerator_pos he)
    (cosineGenerator_pos (by have := h.2.1; omega)))
    (cosineGenerator_pos (by have := h.2.1; have := h.2.2; omega))

/-- Since abc is nonzero and its image is -abc, the sign exponent is odd. -/
theorem ArithmeticHyperbolic.odd_quotient_sum {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    Odd (t.commonDenominator / t.e + t.commonDenominator / t.f +
      t.commonDenominator / t.g) := by
  have hp := h.evenAutomorphism_product he hN
  rw [t.evenAutomorphism_product_eq_sign h.admissible hN] at hp
  have hp' := congrArg t.cosineField.val hp
  simp only [map_mul, map_pow, map_neg, map_one] at hp'
  have hpos := t.fieldGeneratorProduct_pos h.admissible he
  have hs : (-1 : ℝ) ^ (t.commonDenominator / t.e + t.commonDenominator / t.f +
      t.commonDenominator / t.g) = -1 := by
    change _ * (t.fieldGeneratorProduct : ℝ) = -(t.fieldGeneratorProduct : ℝ) at hp'
    nlinarith
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)).mp hs

/-- The 2-adic valuation of the common denominator is the maximum of the
three denominator valuations, as in the paper. -/
theorem twoAdic_commonDenominator_eq_max (t : Triangle) (h : t.Admissible) :
    padicValNat 2 t.commonDenominator =
      max (padicValNat 2 t.e) (max (padicValNat 2 t.f) (padicValNat 2 t.g)) := by
  have hlcm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      padicValNat 2 (a.lcm b) = max (padicValNat 2 a) (padicValNat 2 b) := by
    intro a b ha hb
    rw [← Nat.factorization_def _ Nat.prime_two, Nat.factorization_lcm ha hb]
    simp [Finsupp.sup_apply, Nat.factorization_def _ Nat.prime_two]
  have he : t.e ≠ 0 := by have := h.1; omega
  have hf : t.f ≠ 0 := by have := h.1; have := h.2.1; omega
  have hg : t.g ≠ 0 := by have := h.1; have := h.2.1; have := h.2.2; omega
  rw [commonDenominator, hlcm _ _ he (Nat.lcm_ne_zero hf hg), hlcm _ _ hf hg]

/-- Number of positions attaining ν₂(N). For admissible triples this is
the maximal denominator valuation, by `twoAdic_commonDenominator_eq_max`.
The index type Fin 3 ensures repeated denominators count with multiplicity. -/
def maximalTwoAdicCount (t : Triangle) : ℕ :=
  (Finset.univ.filter fun i : Fin 3 =>
    padicValNat 2 (![t.e, t.f, t.g] i) = padicValNat 2 t.commonDenominator).card

/-- The parity assertion of PDF Lemma 2.2, with repeated denominators
counted with their multiplicities. -/
theorem ArithmeticHyperbolic.odd_maximalTwoAdicCount {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    Odd t.maximalTwoAdicCount := by
  have hsum : Odd (∑ i : Fin 3, t.commonDenominator / (![t.e, t.f, t.g] i)) := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using h.odd_quotient_sum he hN
  have hcount := (Finset.odd_sum_iff_odd_card_odd
    (s := Finset.univ) (fun i : Fin 3 => t.commonDenominator / (![t.e, t.f, t.g] i))).mp hsum
  have hequiv : ∀ i : Fin 3, Odd (t.commonDenominator / (![t.e, t.f, t.g] i)) ↔
      padicValNat 2 (![t.e, t.f, t.g] i) = padicValNat 2 t.commonDenominator := by
    intro i
    apply odd_quotient_iff_twoAdic_eq _ _ (t.commonDenominator_ne_zero h.admissible)
    fin_cases i
    · exact Nat.dvd_lcm_left _ _
    · exact (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
    · exact (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
  simpa only [hequiv, maximalTwoAdicCount] using hcount

end Triangle
end ArithmeticTriangles
