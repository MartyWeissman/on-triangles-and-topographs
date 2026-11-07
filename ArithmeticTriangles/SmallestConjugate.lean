module

public import ArithmeticTriangles.CyclotomicEmbeddings
public import ArithmeticTriangles.Structural

/-!
# Bounds for every cosine conjugate

For n≥3, every conjugate v of uₙ=2cos(π/n) satisfies v²≥2−uₙ.
The proof is elementary: reduce a coprime index k modulo n. The integer
2(k mod n) cannot equal n, so its angle stays at least π/n away from π.
Monotonicity of cosine then bounds the doubled-angle cosine from below.

The bounds are transported to arbitrary real embeddings using the previously
proved exhaustiveness of the cyclotomic embeddings.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- Cosine generators strictly increase with the denominator, for n≥2. -/
theorem cosineGenerator_lt_of_lt (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m) :
    cosineGenerator n < cosineGenerator m := by
  have hn' : (0 : ℝ) < n := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnm' : (n : ℝ) < m := by exact_mod_cast hnm
  have hangle : Real.pi / m < Real.pi / n := by
    exact (div_lt_div_iff₀ hm' hn').mpr (by nlinarith [Real.pi_pos])
  have hle := angle_le_pi_div_two hn
  change Real.pi / n ≤ Real.pi / 2 at hle
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / m)
    (show Real.pi / n ≤ Real.pi by linarith [Real.pi_pos]) hangle
  unfold cosineGenerator
  linarith

/-- The squared smallest-conjugate bound, without trigonometric approximations.
Coprimality excludes the zero cosine that would invalidate the bound. -/
theorem cosine_power_sq_lower_bound (n k : ℕ) (hn : 3 ≤ n) (hk : k.Coprime n) :
    2 - cosineGenerator n ≤ (2 * Real.cos ((k : ℝ) * Real.pi / n)) ^ 2 := by
  let r := k % n
  have hr : r < n := Nat.mod_lt _ (by omega)
  have hcop : n.Coprime r := by
    change Nat.gcd n (k % n) = 1
    rw [Nat.gcd_comm n (k % n), ← Nat.gcd_rec]
    exact hk.symm.gcd_eq_one
  have hne : 2 * r ≠ n := by
    intro heq
    have hd : n ∣ 2 := hcop.dvd_of_dvd_mul_right (by rw [heq])
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hn' : (0 : ℝ) < n := by positivity
  have hr' : (r : ℝ) < n := by exact_mod_cast hr
  have hcancel : Real.pi / n * n = Real.pi := div_mul_cancel₀ _ (ne_of_gt hn')
  have hcancel' : 2 * (r : ℝ) * Real.pi / n * n = 2 * r * Real.pi :=
    div_mul_cancel₀ _ (ne_of_gt hn')
  have hcos : -Real.cos (Real.pi / n) ≤ Real.cos (2 * (r : ℝ) * Real.pi / n) := by
    by_cases hlt : 2 * r < n
    · have hi : 2 * (r : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * r + 1 ≤ n by omega)
      have hangle : 2 * (r : ℝ) * Real.pi / n ≤ Real.pi - Real.pi / n := by
        apply (div_le_iff₀ hn').mpr
        nlinarith [mul_le_mul_of_nonneg_right hi Real.pi_pos.le]
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity : 0 ≤ 2 * (r : ℝ) * Real.pi / n)
        (show Real.pi - Real.pi / n ≤ Real.pi from sub_le_self _ (by positivity)) hangle
      simpa only [Real.cos_pi_sub] using hc
    · have hi : (n : ℝ) + 1 ≤ 2 * r := by exact_mod_cast (show n + 1 ≤ 2 * r by omega)
      have hangle : 2 * Real.pi - 2 * (r : ℝ) * Real.pi / n ≤ Real.pi - Real.pi / n := by
        apply (mul_le_mul_iff_left₀ hn').mp
        nlinarith [mul_le_mul_of_nonneg_right hi Real.pi_pos.le]
      have hnonneg : 0 ≤ 2 * Real.pi - 2 * (r : ℝ) * Real.pi / n := by
        have hb : 2 * (r : ℝ) * Real.pi / n ≤ 2 * Real.pi := by
          apply (div_le_iff₀ hn').mpr
          nlinarith [Real.pi_pos]
        linarith
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi hnonneg
        (show Real.pi - Real.pi / n ≤ Real.pi from sub_le_self _ (by positivity)) hangle
      simpa only [Real.cos_pi_sub, Real.cos_two_pi_sub] using hc
  have hs := congrArg (fun x : ℝ => x ^ 2)
    (cosine_index_shift n (k / n) (k % n) (by omega))
  rw [Nat.div_add_mod] at hs
  rw [mul_pow ((-1 : ℝ) ^ (k / n)), sign_pow_sq, one_mul] at hs
  rw [hs, mul_pow, Real.cos_sq]
  rw [show 2 * ((k % n : ℕ) : ℝ) * Real.pi / n = 2 * ((r : ℝ) * Real.pi / n) by ring] at hcos
  unfold cosineGenerator
  nlinarith

namespace Triangle

/-- Every cosine generator has all its real conjugates strictly between −2
and 2. Weak bounds come from cosine; injectivity excludes the rational endpoints. -/
theorem embedding_cosine_mem_Ioo (t : Triangle) (h : t.Admissible)
    (σ : t.cosineField →ₐ[ℚ] ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hdvd : n ∣ t.commonDenominator) (x : t.cosineField)
    (hx : (x : ℝ) = cosineGenerator n) : σ x ∈ Set.Ioo (-2) 2 := by
  have hbounds : -2 ≤ σ x ∧ σ x ≤ 2 := by
    obtain ⟨k, _, hk, rfl⟩ := t.exists_cyclotomicRealEmbedding h σ
    rw [t.cyclotomicRealEmbedding_cosine h k hk n hdvd x hx]
    constructor
    · linarith [Real.neg_one_le_cos ((k : ℝ) * Real.pi / n)]
    · linarith [Real.cos_le_one ((k : ℝ) * Real.pi / n)]
  have hneMinus : σ x ≠ -2 := by
    intro heq
    have hx' : x = -2 := by
      apply σ.injective
      rw [map_neg, map_ofNat]
      exact heq
    have hv := congrArg t.cosineField.val hx'
    change (x : ℝ) = -2 at hv
    rw [hx] at hv
    linarith [cosineGenerator_nonneg hn]
  have hnePlus : σ x ≠ 2 := by
    intro heq
    have hx' : x = 2 := by
      apply σ.injective
      rw [map_ofNat]
      exact heq
    have hv := congrArg t.cosineField.val hx'
    change (x : ℝ) = 2 at hv
    rw [hx] at hv
    linarith [cosineGenerator_lt_two hn]
  exact ⟨lt_of_le_of_ne hbounds.1 (Ne.symm hneMinus), lt_of_le_of_ne hbounds.2 hnePlus⟩

/-- The smallest-conjugate estimate for any cosine lying in the triangle field.
It applies to every real embedding, not only explicitly presented indices. -/
theorem embedding_cosine_sq_lower_bound (t : Triangle) (h : t.Admissible)
    (σ : t.cosineField →ₐ[ℚ] ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hdvd : n ∣ t.commonDenominator) (x : t.cosineField)
    (hx : (x : ℝ) = cosineGenerator n) : 2 - cosineGenerator n ≤ (σ x) ^ 2 := by
  obtain ⟨k, _, hk, rfl⟩ := t.exists_cyclotomicRealEmbedding h σ
  rw [t.cyclotomicRealEmbedding_cosine h k hk n hdvd x hx]
  exact cosine_power_sq_lower_bound n k hn
    (hk.of_dvd_right (hdvd.trans (dvd_mul_left t.commonDenominator 2)))

end Triangle
end ArithmeticTriangles
