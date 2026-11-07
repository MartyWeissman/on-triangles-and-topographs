module

public import ArithmeticTriangles.TotientBounds

/-!
# Trace bounds for short cyclotomic angles

A root with angle strictly between 0 and 2π/7 has order at least eight.
Its normalized trace is therefore at least −1/8. Expanding the discriminant
as a sum of seven root/inverse pairs gives an effective bound without the
full three-generator field-degree formula.
-/

@[expose] public section
namespace ArithmeticTriangles

/-- A root together with its inverse, with an integer exponent. -/
noncomputable def rootPair {K : Type*} [Field K] (ζ : K) (i : ℤ) : K :=
  ζ ^ i + ζ ^ (-i)

/-- Reversing the index does not change the real root pair. -/
theorem rootPair_neg {K : Type*} [Field K] (ζ : K) (i : ℤ) :
    rootPair ζ (-i) = rootPair ζ i := by simp [rootPair, add_comm]

/-- The product-to-sum identity, expressed algebraically in a root of unity. -/
theorem rootPair_mul {K : Type*} [Field K] (ζ : K) (hz : ζ ≠ 0) (i j : ℤ) :
    rootPair ζ i * rootPair ζ j = rootPair ζ (i + j) + rootPair ζ (i - j) := by
  simp only [rootPair, zpow_add₀ hz, zpow_sub₀ hz, zpow_neg, neg_add_rev]
  field_simp
  ring

/-- Squaring a root pair leaves the rational term 2 and one doubled pair. -/
theorem rootPair_sq {K : Type*} [Field K] (ζ : K) (hz : ζ ≠ 0) (i : ℤ) :
    rootPair ζ i ^ 2 = 2 + rootPair ζ (2 * i) := by
  rw [pow_two, rootPair_mul ζ hz]
  norm_num [show i + i = 2 * i by ring, rootPair, add_comm]

/-- The discriminant has seven nonconstant root pairs, each with coefficient one. -/
theorem discriminant_rootPairs {K : Type*} [Field K] (ζ : K) (hz : ζ ≠ 0) (u v w : ℤ) :
    discriminant (rootPair ζ u) (rootPair ζ v) (rootPair ζ w) =
      2 + rootPair ζ (2 * u) + rootPair ζ (2 * v) + rootPair ζ (2 * w) +
        rootPair ζ (u + v + w) + rootPair ζ (u + v - w) +
        rootPair ζ (u - v + w) + rootPair ζ (-u + v + w) := by
  unfold discriminant
  rw [rootPair_sq ζ hz, rootPair_sq ζ hz, rootPair_sq ζ hz,
    rootPair_mul ζ hz, add_mul, rootPair_mul ζ hz, rootPair_mul ζ hz]
  have he : u - v - w = -(-u + v + w) := by ring
  rw [he, rootPair_neg]
  ring

/-- A positive exponent q with 7q<M has root order at least eight. -/
theorem root_order_ge_eight (M q : ℕ) (hM : 0 < M) (hq : 0 < q) (hsmall : 7 * q < M) :
    8 ≤ M / M.gcd q := by
  have hdpos : 0 < M.gcd q := Nat.gcd_pos_of_pos_left q hM
  have hdq : M.gcd q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right M q)
  have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left M q)
  nlinarith

/-- The normalized trace of a root of sufficiently large order has the
uniform lower bound already proved from the Möbius/totient formula. -/
theorem normalizedTrace_rootPair_ge_neg_quarter {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsIntegral ℚ K] (M : ℕ) (hM : 0 < M) (ζ : K)
    (hζ : IsPrimitiveRoot ζ M) (q : ℤ) (hq : 0 < q) (hsmall : 7 * q < M) :
    -(1 : ℚ) / 4 ≤ Algebra.normalizedTrace ℚ K (rootPair ζ q) := by
  have hqn : 0 < q.toNat := by omega
  have hsn : 7 * q.toNat < M := by omega
  have hd : M.gcd q.toNat ≠ 0 := (Nat.gcd_pos_of_pos_left q.toNat hM).ne'
  have hm := root_order_ge_eight M q.toNat hM hqn hsn
  have hp := hζ.pow_div_gcd q.toNat hd
  have hqe : (q.toNat : ℤ) = q := by omega
  have hr := moebiusRatio_ge_neg_eighth (M / M.gcd q.toNat) (by omega) (by omega)
  rw [rootPair, ← hqe, zpow_natCast, zpow_neg, zpow_natCast, map_add,
    normalizedTrace_primitiveRoot _ (by omega) _ hp,
    normalizedTrace_primitiveRoot _ (by omega) _ hp.inv]
  unfold moebiusRatio at hr
  linarith

end ArithmeticTriangles
