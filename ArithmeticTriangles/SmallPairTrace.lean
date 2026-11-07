module

public import ArithmeticTriangles.LargeTrace

/-!
# Bounding the remaining small initial pairs by traces

For (e,e,g) with 4≤e≤10 and g>210, all the variable root terms have
order greater than 42. Their Möbius ratios are at least −1/20. Together with
the fixed terms this forces τ≥1/2. The resulting degree bound forces g≤105,
a contradiction. SmallPairCompleteness implements the final reduction.
-/

@[expose] public section
namespace ArithmeticTriangles

set_option maxRecDepth 8192 in
/-- The finite negative-Möbius exceptions below totient 20. -/
theorem negative_moebius_totient_check : ∀ a : Fin 3, ∀ b : Fin 256,
    42 < 256 * (a : ℕ) + b → ArithmeticFunction.moebius (256 * (a : ℕ) + b) = -1 →
      20 ≤ fastTotient (256 * (a : ℕ) + b) := by
  decide +kernel

/-- Beyond order 42, every normalized root trace is at least −1/20. -/
theorem moebiusRatio_ge_neg_twentieth (n : ℕ) (hn : 42 < n) :
    -(1 : ℚ) / 20 ≤ moebiusRatio n := by
  rcases ArithmeticFunction.moebius_eq_or n with hμ | hμ | hμ
  · norm_num [moebiusRatio, hμ]
  · have : 0 ≤ moebiusRatio n := by simp [moebiusRatio, hμ]
    linarith
  · have hφ : 20 ≤ n.totient := by
      by_contra hh
      have hb := le_two_totient_sq n
      have hnB : n < 768 := by nlinarith
      have hc := negative_moebius_totient_check ⟨n / 256, by omega⟩
        ⟨n % 256, Nat.mod_lt _ (by decide)⟩
      simp only [Nat.div_add_mod, fastTotient_eq] at hc
      omega
    have hφ' : (20 : ℚ) ≤ n.totient := by exact_mod_cast hφ
    unfold moebiusRatio
    rw [le_div_iff₀ (by linarith : (0 : ℚ) < n.totient), hμ]
    norm_num
    linarith

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- The sharper denominator bound required by the small-pair trace argument. -/
theorem small_totient_62_check : ∀ a : Fin 16, ∀ b : Fin 256,
    fastTotient (2 * (256 * (a : ℕ) + b)) ≤ 62 → 256 * (a : ℕ) + b ≤ 105 := by
  decide +kernel

/-- Individual cosine degree at most 31 forces denominator at most 105. -/
theorem denominator_le_105_of_totient_le_62 (n : ℕ) (h : (2 * n).totient ≤ 62) : n ≤ 105 := by
  have hn := denominator_le_totient_bound_sq n 62 h
  have hc := small_totient_62_check ⟨n / 256, by omega⟩ ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.div_add_mod, fastTotient_eq] at hc
  exact hc h

/-- The exact normalized trace of a root pair at any nonnegative index. -/
theorem normalizedTrace_rootPair_eq {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsIntegral ℚ K] (M : ℕ) (hM : 0 < M) (ζ : K)
    (hζ : IsPrimitiveRoot ζ M) (q : ℕ) :
    Algebra.normalizedTrace ℚ K (rootPair ζ q) = 2 * moebiusRatio (M / M.gcd q) := by
  have hdpos := Nat.gcd_pos_of_pos_left q hM
  have hm : 0 < M / M.gcd q := Nat.div_pos (Nat.le_of_dvd hM (Nat.gcd_dvd_left M q)) hdpos
  have hp := hζ.pow_div_gcd q hdpos.ne'
  rw [rootPair, zpow_natCast, zpow_neg, zpow_natCast, map_add,
    normalizedTrace_primitiveRoot _ hm _ hp, normalizedTrace_primitiveRoot _ hm _ hp.inv]
  unfold moebiusRatio
  ring

/-- Consequently a root pair of order greater than 42 has trace at least −1/10. -/
theorem normalizedTrace_rootPair_ge_neg_tenth {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsIntegral ℚ K] (M : ℕ) (hM : 0 < M) (ζ : K)
    (hζ : IsPrimitiveRoot ζ M) (q : ℕ) (horder : 42 < M / M.gcd q) :
    -(1 : ℚ) / 10 ≤ Algebra.normalizedTrace ℚ K (rootPair ζ q) := by
  rw [normalizedTrace_rootPair_eq M hM ζ hζ q]
  linarith [moebiusRatio_ge_neg_twentieth _ horder]

/-- If q=2u±w, e*u=N=g*w, then gcd(2N,q) divides e*w. Hence its
root order is at least 2g/e. This avoids a relative cyclotomic trace formula. -/
theorem cross_root_order_bound (N e g u w q : ℕ) (_hN : 0 < N)
    (he : 0 < e) (hw : 0 < w) (heu : e * u = N) (hgw : g * w = N)
    (hq : q = 2 * u + w ∨ q + w = 2 * u) :
    2 * g ≤ e * (2 * N / (2 * N).gcd q) := by
  let d := (2 * N).gcd q
  have hdN : d ∣ 2 * N := Nat.gcd_dvd_left _ _
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hdw : d ∣ e * w := by
    rcases hq with hq | hq
    · have heq : e * q = 2 * N + e * w := by rw [hq, ← heu]; ring
      have hx := dvd_mul_of_dvd_right hdq e
      rw [heq] at hx
      exact (Nat.dvd_add_right hdN).mp hx
    · have heq : e * q + e * w = 2 * N := by rw [← mul_add, hq, ← heu]; ring
      have hx : d ∣ e * q + e * w := by rw [heq]; exact hdN
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hdq e)).mp hx
  have hdle : d ≤ e * w := Nat.le_of_dvd (Nat.mul_pos he hw) hdw
  have hm := Nat.div_mul_cancel hdN
  have hh := Nat.mul_le_mul_left (2 * N / d) hdle
  rw [hm] at hh
  apply (Nat.mul_le_mul_right_iff hw).mp
  nlinarith [hgw]

end ArithmeticTriangles
