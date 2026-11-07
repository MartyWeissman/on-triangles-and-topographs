module

public import ArithmeticTriangles.EvenSymmetry
public import Mathlib.FieldTheory.NormalizedTrace

/-!
# Exact square traces and the even-N discriminant formula

The normalized trace of a primitive nth root of unity is μ(n)/φ(n).
We obtain this by combining the cyclotomic minimal polynomial with Möbius
inversion of its next-to-leading coefficient. Mathlib's normalized trace
is invariant under algebra embeddings, so the calculation transfers from
the common cyclotomic field to the full cosine field.

For a=2cos(π/n), the resulting square average is 2+2μ(n)/φ(n). Together
with Tr(abc)=0 for arithmetic triples with e>2 and even N, this proves
PDF equation (2.10). TraceBounds proves the estimates for Lemma 2.3.
The general product trace in (2.7) remains open.
-/

@[expose] public section

open Polynomial

namespace ArithmeticTriangles

/-- The negative next-to-leading coefficient of Xⁿ−1 is 1 when n=1
and 0 for larger n. This is the divisor sum that Möbius inversion will invert. -/
theorem neg_nextCoeff_X_pow_sub_one (n : ℕ) (hn : 0 < n) :
    -((X : ℚ[X]) ^ n - 1).nextCoeff = if n = 1 then 1 else 0 := by
  by_cases h : n = 1
  · subst n
    simp only [pow_one, ite_true]
    change -(X - C (1 : ℚ)).nextCoeff = 1
    rw [nextCoeff_X_sub_C]
    norm_num
  · have hdeg : ((X : ℚ[X]) ^ n - 1).natDegree = n :=
      natDegree_X_pow_sub_C
    rw [nextCoeff, hdeg, ite_eq_right (by omega)]
    simp [coeff_sub, coeff_X_pow, coeff_one, h, show n - 1 ≠ 0 by omega,
      show n - 1 ≠ n by omega]

/-- The negative next-to-leading coefficient of Φₙ is μ(n).
For monic polynomials this coefficient is additive under multiplication.
Apply it to ∏_{d∣n} Φ_d=Xⁿ−1, then use Möbius inversion. Comparing two
inversions of the same divisor sum avoids a separate antidiagonal calculation. -/
theorem cyclotomic_neg_nextCoeff (n : ℕ) (hn : 0 < n) :
    -(cyclotomic n ℚ).nextCoeff = (ArithmeticFunction.moebius n : ℚ) := by
  have hc : ∀ m > 0, ∑ d ∈ m.divisors, -(cyclotomic d ℚ).nextCoeff =
      if m = 1 then 1 else 0 := by
    intro m hm
    rw [Finset.sum_neg_distrib, ← Monic.nextCoeff_prod m.divisors
      (fun d => cyclotomic d ℚ) (fun d _ => cyclotomic.monic d ℚ),
      prod_cyclotomic_eq_X_pow_sub_one hm, neg_nextCoeff_X_pow_sub_one m hm]
  have hμ : ∀ m > 0, ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) =
      if m = 1 then 1 else 0 := by
    intro m hm
    have ht := congrArg (fun f : ArithmeticFunction ℤ => f m)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at ht
    exact_mod_cast ht
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hc) n hn).symm.trans
    ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hμ) n hn)

/-- A primitive nth root has normalized trace μ(n)/φ(n), in any algebraic
extension of ℚ containing it. Its minimal polynomial is Φₙ, of degree φ(n).
No assertion that the chosen root generates the entire ambient field is needed. -/
theorem normalizedTrace_primitiveRoot {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsIntegral ℚ K] (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Algebra.normalizedTrace ℚ K ζ = (ArithmeticFunction.moebius n : ℚ) / n.totient := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [Algebra.normalizedTrace_minpoly,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hn),
    natDegree_cyclotomic, cyclotomic_neg_nextCoeff n hn, smul_eq_mul]
  ring

/-- For ζ primitive of order 2n, the square of ζ+ζ⁻¹ has average
2+2μ(n)/φ(n): expand the square and use that ζ² and its inverse have order n. -/
theorem normalizedTrace_cosine_sq {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsIntegral ℚ K] (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    Algebra.normalizedTrace ℚ K ((ζ + ζ⁻¹)^2) =
      2 + 2 * (ArithmeticFunction.moebius n : ℚ) / n.totient := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hs : (ζ + ζ⁻¹)^2 = 2 + ζ^2 + (ζ^2)⁻¹ := by field_simp; ring
  have hp : IsPrimitiveRoot (ζ^2) n := IsPrimitiveRoot.pow (by omega) hζ rfl
  have htwo : Algebra.normalizedTrace ℚ K (2 : K) = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ K (2 : ℚ)
  rw [hs, map_add, map_add, htwo, normalizedTrace_primitiveRoot n hn _ hp,
    normalizedTrace_primitiveRoot n hn _ hp.inv]
  ring

/-- Evaluate the square trace in the common cyclotomic field. If N=n*m,
the mth power of the ambient root is our chosen primitive 2n-th root. -/
theorem cyclotomic_normalizedTrace_cosine_sq (N : ℕ) [NeZero N]
    (n : ℕ) (hdvd : n ∣ N) (x : cosineCyclotomicField N)
    (hx : (x : ℂ) = (cosineGenerator n : ℂ)) :
    Algebra.normalizedTrace ℚ (cosineCyclotomicField N) (x ^ 2) =
      2 + 2 * (ArithmeticFunction.moebius n : ℚ) / n.totient := by
  obtain ⟨m, rfl⟩ := hdvd
  have hn : n ≠ 0 := by have := NeZero.ne (n * m); aesop
  have hm : m ≠ 0 := by have := NeZero.ne (n * m); aesop
  let ζ : cosineCyclotomicField (n * m) := cyclotomicRoot (n * m) ^ m
  have hζ : (ζ : ℂ) = cosineRoot n := cosineRoot_pow_mul n m hn hm
  have hprim : IsPrimitiveRoot ζ (2 * n) := by
    have hc : IsPrimitiveRoot ((cosineCyclotomicField (n * m)).val ζ) (2 * n) := by
      change IsPrimitiveRoot (ζ : ℂ) (2 * n)
      rw [hζ]
      exact cosineRoot_primitive n hn
    exact hc.of_map_of_injective (cosineCyclotomicField (n * m)).val.injective
  have hx' : x = ζ + ζ⁻¹ := by
    apply Subtype.ext
    change (x : ℂ) = (ζ : ℂ) + (ζ : ℂ)⁻¹
    rw [hx, hζ, cosineGenerator_eq_root_add_inv]
  rw [hx']
  exact normalizedTrace_cosine_sq n (Nat.pos_of_ne_zero hn) ζ hprim

namespace Triangle

/-- The square-trace evaluation in the full triangle field F. Mathlib
transports normalized trace along the embedding F→ℚ(ζ₂N); hence the ambient
field degree cancels without needing our still-unproved formula for [F:ℚ].
This holds for admissible triples, without arithmeticity or a parity assumption. -/
theorem generator_square_trace (t : Triangle) (h : t.Admissible)
    (n : ℕ) (hdvd : n ∣ t.commonDenominator) (x : t.cosineField)
    (hx : (x : ℝ) = cosineGenerator n) :
    t.fieldTrace (x ^ 2) / t.deg = 2 + 2 * (ArithmeticFunction.moebius n : ℚ) / n.totient := by
  let : NeZero t.commonDenominator := ⟨t.commonDenominator_ne_zero h⟩
  have ht := cyclotomic_normalizedTrace_cosine_sq t.commonDenominator n hdvd
    (t.toCyclotomic h x) (by simpa using congrArg Complex.ofReal hx)
  rw [← map_pow, Algebra.normalizedTrace_map,
    Algebra.normalizedTrace_eq_of_finiteDimensional_apply] at ht
  simpa [fieldTrace, deg, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht

/-- The normalized discriminant trace τ=Tr(D)/[F:ℚ] used in the PDF. -/
noncomputable def normalizedDiscriminantTrace (t : Triangle) : ℚ :=
  t.discriminantTrace / t.deg

/-- Equation (2.10) in the PDF. For arithmetic triples with e>2 and even N,
the product term has trace zero. The three evaluated square traces then give τ.
Repeated denominators contribute once for each of their positions. -/
theorem ArithmeticHyperbolic.normalizedDiscriminantTrace_even {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.normalizedDiscriminantTrace = 2 + 2 *
      ((ArithmeticFunction.moebius t.e : ℚ) / t.e.totient +
       (ArithmeticFunction.moebius t.f : ℚ) / t.f.totient +
       (ArithmeticFunction.moebius t.g : ℚ) / t.g.totient) := by
  have ha := t.generator_square_trace h.admissible _ (Nat.dvd_lcm_left _ _) t.firstGenerator rfl
  have hb := t.generator_square_trace h.admissible _
    ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) t.secondGenerator rfl
  have hc := t.generator_square_trace h.admissible _
    ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl
  have hd : (t.deg : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr t.deg_pos.ne'
  unfold normalizedDiscriminantTrace
  rw [h.discriminantTrace_eq_square_traces he hN, sub_div, add_div, add_div, ha, hb, hc,
    mul_div_cancel_right₀ 4 hd]
  ring

/-- The ordinary trace version of (2.10), obtained by multiplying by d.
The explicit field-degree formula and the lower bound in Lemma 2.3 remain separate. -/
theorem ArithmeticHyperbolic.discriminantTrace_even {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.discriminantTrace = 2 * t.deg *
      (1 + (ArithmeticFunction.moebius t.e : ℚ) / t.e.totient +
       (ArithmeticFunction.moebius t.f : ℚ) / t.f.totient +
       (ArithmeticFunction.moebius t.g : ℚ) / t.g.totient) := by
  have ht := h.normalizedDiscriminantTrace_even he hN
  have hd : (t.deg : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr t.deg_pos.ne'
  rw [normalizedDiscriminantTrace, div_eq_iff hd] at ht
  rw [ht]
  ring

end Triangle
end ArithmeticTriangles
