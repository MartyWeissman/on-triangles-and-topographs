module

public import ArithmeticTriangles.CyclotomicAction
public import ArithmeticTriangles.ArithmeticConsequences
public import ArithmeticTriangles.Identities

/-!
# The structural inequality for arithmetic triples

This proves the central conclusion of PDF Lemma 2.2: if `e > 2`, arithmetic
hyperbolicity forces `E < 0`, hence `1/e < 1/f + 1/g`.

For even N, the index N + 1 changes signs and preserves all three squares.
At least one sign changes because N is the least common multiple. The image
of D is either D or E; the arithmetic sign rule excludes D.

For odd N, the index N + 2 sends each generator u to 2-u². If this fixed the
whole field, positivity would force every generator to equal 1, contradicting
D>0. The polynomial identity σ(D)=D*E then forces E<0.

The final corollaries remove the structural hypothesis from the arithmetic
versions of our earlier denominator bounds. The remaining 2-adic parity and
trace-of-abc assertions in Lemma 2.2 are proved in EvenParity and EvenSymmetry.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The even-N index is a unit modulo 2N. -/
theorem even_index_coprime (N : ℕ) (hN : Even N) : (N + 1).Coprime (2 * N) := by
  rw [Nat.coprime_mul_iff_right]
  constructor
  · apply Nat.coprime_two_right.mpr
    obtain ⟨r, rfl⟩ := hN
    exact ⟨r, by omega⟩
  · simp [Nat.coprime_self_add_left]

/-- The odd-N index is a unit modulo 2N. -/
theorem odd_index_coprime (N : ℕ) (hN : Odd N) : (N + 2).Coprime (2 * N) := by
  rw [Nat.coprime_mul_iff_right]
  constructor
  · apply Nat.coprime_two_right.mpr
    obtain ⟨r, rfl⟩ := hN
    exact ⟨r + 1, by omega⟩
  · simpa [Nat.coprime_self_add_left, Nat.coprime_two_left] using hN

/-- Adding n*m to the index shifts the angle by mπ. -/
theorem cosine_index_shift (n m k : ℕ) (hn : n ≠ 0) :
    2 * Real.cos (((n * m + k : ℕ) : ℝ) * Real.pi / n) =
      (-1 : ℝ)^m * (2 * Real.cos ((k : ℝ) * Real.pi / n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have heq : ((n * m + k : ℕ) : ℝ) * Real.pi / n =
      (k : ℝ) * Real.pi / n + (m : ℝ) * Real.pi := by push_cast; field_simp; ring
  rw [heq, Real.cos_add_nat_mul_pi]
  ring

/-- Every quotient N / n is odd when N is odd, so the double-angle identity
turns the index N + 2 into the polynomial u ↦ 2-u². -/
theorem cosine_odd_index (N n : ℕ) (hN : Odd N) (hdvd : n ∣ N) :
    2 * Real.cos (((N + 2 : ℕ):ℝ) * Real.pi / n) = 2 - cosineGenerator n ^ 2 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hn : n ≠ 0 := by intro h; simp [h] at hN
  have hm : Odd m := (Nat.odd_mul.mp hN).2
  rw [cosine_index_shift n m 2 hn, hm.neg_one_pow]
  push_cast
  rw [show (2 : ℝ)*Real.pi/n = 2*(Real.pi/n) by ring, Real.cos_two_mul]
  unfold cosineGenerator
  ring

/-- A positive fixed point of u ↦ 2-u² is 1. -/
theorem eq_one_of_pos_of_eq_two_sub_sq {a : ℝ} (ha : 0 < a) (h : a = 2 - a ^ 2) : a = 1 := by
  have hp : (a - 1) * (a + 2) = 0 := by nlinarith
  have hz : a - 1 = 0 := (mul_eq_zero.mp hp).resolve_right (by linarith)
  linarith

/-- If N / n is even, n already divides N / 2. -/
theorem dvd_half_of_even_quotient (N n : ℕ) (hN : N ≠ 0) (hdvd : n ∣ N) (h : Even (N / n)) : n ∣ N / 2 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hn : n ≠ 0 := by aesop
  have hm : Even m := by simpa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)] using h
  obtain ⟨r, hr⟩ := hm
  refine ⟨r, ?_⟩
  rw [hr, show n * (r + r) = (n * r) * 2 by ring, Nat.mul_div_left]
  norm_num

/-- Squaring removes the sign introduced by a multiple of π. -/
theorem sign_pow_sq (m : ℕ) : ((-1 : ℝ)^m)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
  norm_num

namespace Triangle

/-- At least one of N/e, N/f, N/g is odd. Otherwise each denominator
would divide N / 2, forcing their least common multiple N to divide N / 2.
This avoids introducing 2-adic valuations merely to find a sign change. -/
theorem exists_odd_quotient (t : Triangle) (h : t.Admissible) :
    Odd (t.commonDenominator / t.e) ∨ Odd (t.commonDenominator / t.f) ∨ Odd (t.commonDenominator / t.g) := by
  by_contra hnot
  push Not at hnot
  have hN := t.commonDenominator_ne_zero h
  have he : t.e ∣ t.commonDenominator := Nat.dvd_lcm_left _ _
  have hf : t.f ∣ t.commonDenominator := (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
  have hg : t.g ∣ t.commonDenominator := (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
  have he2 := dvd_half_of_even_quotient _ _ hN he (Nat.not_odd_iff_even.mp hnot.1)
  have hf2 := dvd_half_of_even_quotient _ _ hN hf (Nat.not_odd_iff_even.mp hnot.2.1)
  have hg2 := dvd_half_of_even_quotient _ _ hN hg (Nat.not_odd_iff_even.mp hnot.2.2)
  have hdiv : t.commonDenominator ∣ t.commonDenominator / 2 :=
    Nat.lcm_dvd_iff.mpr ⟨he2, Nat.lcm_dvd_iff.mpr ⟨hf2, hg2⟩⟩
  have hNe := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) he
  have hege := h.1
  have hle := Nat.le_of_dvd (by omega : 0 < t.commonDenominator / 2) hdiv
  have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by omega : 1 < 2)
  omega

/-- The odd-N embedding acts polynomially on each generator. -/
theorem odd_embedding_cosine (t : Triangle) (h : t.Admissible)
    (hN : Odd t.commonDenominator) (n : ℕ) (hdvd : n ∣ t.commonDenominator)
    (x : t.cosineField) (hx : (x : ℝ) = cosineGenerator n) :
    t.cyclotomicRealEmbedding h (t.commonDenominator + 2) (odd_index_coprime _ hN) x =
      2 - cosineGenerator n ^ 2 := by
  rw [t.cyclotomicRealEmbedding_cosine h _ _ n hdvd x hx]
  exact cosine_odd_index _ _ hN hdvd

/-- The odd case of the structural lemma, using σ(D)=D*E. -/
theorem ArithmeticHyperbolic.companion_neg_of_odd {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Odd t.commonDenominator) :
    t.companionDiscriminant < 0 := by
  let σ := t.cyclotomicRealEmbedding h.admissible (t.commonDenominator + 2) (odd_index_coprime _ hN)
  have ha : σ t.firstGenerator = 2 - cosineGenerator t.e ^ 2 :=
    t.odd_embedding_cosine h.admissible hN _ (Nat.dvd_lcm_left _ _) _ rfl
  have hb : σ t.secondGenerator = 2 - cosineGenerator t.f ^ 2 :=
    t.odd_embedding_cosine h.admissible hN _
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hc : σ t.thirdGenerator = 2 - cosineGenerator t.g ^ 2 :=
    t.odd_embedding_cosine h.admissible hN _
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hne : σ ≠ t.cosineField.val := by
    intro heq
    rw [heq] at ha hb hc
    have ha1 := eq_one_of_pos_of_eq_two_sub_sq (cosineGenerator_pos he) ha
    have hb1 := eq_one_of_pos_of_eq_two_sub_sq
      (cosineGenerator_pos (by have := h.admissible.2.1; omega)) hb
    have hc1 := eq_one_of_pos_of_eq_two_sub_sq
      (cosineGenerator_pos (by have := h.admissible.2.1; have := h.admissible.2.2; omega)) hc
    have hD := h.discriminant_pos
    change 0 < ArithmeticTriangles.discriminant (cosineGenerator t.e) (cosineGenerator t.f) (cosineGenerator t.g) at hD
    norm_num [ha1, hb1, hc1, ArithmeticTriangles.discriminant] at hD
  have hneg := h.2.2 σ hne
  change ArithmeticTriangles.discriminant (σ t.firstGenerator) (σ t.secondGenerator) (σ t.thirdGenerator) < 0 at hneg
  rw [ha, hb, hc, discriminant_companion_product] at hneg
  change t.discriminant * t.companionDiscriminant < 0 at hneg
  nlinarith [h.discriminant_pos]

/-- The even-N embedding changes a generator by the sign (-1)^(N / n). -/
theorem even_embedding_cosine (t : Triangle) (h : t.Admissible)
    (hN : Even t.commonDenominator) (n : ℕ) (hdvd : n ∣ t.commonDenominator)
    (x : t.cosineField) (hx : (x : ℝ) = cosineGenerator n) :
    t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN) x =
      (-1 : ℝ)^(t.commonDenominator/n) * cosineGenerator n := by
  rw [t.cyclotomicRealEmbedding_cosine h _ _ n hdvd x hx]
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact t.commonDenominator_ne_zero h (Nat.zero_dvd.mp hdvd)
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, cosine_index_shift n m 1 hn]
  simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), cosineGenerator]

/-- The arithmetic sign rule forces a square-preserving nonidentity embedding
to negate the product abc. This will also give its vanishing trace. -/
theorem product_neg_of_square_preserving (t : Triangle) (h : t.ArithmeticHyperbolic)
    (σ : t.cosineField →ₐ[ℚ] ℝ) (hne : σ ≠ t.cosineField.val)
    (ha : (σ t.firstGenerator)^2 = cosineGenerator t.e ^ 2)
    (hb : (σ t.secondGenerator)^2 = cosineGenerator t.f ^ 2)
    (hc : (σ t.thirdGenerator)^2 = cosineGenerator t.g ^ 2) :
    σ t.firstGenerator * σ t.secondGenerator * σ t.thirdGenerator =
      -(cosineGenerator t.e * cosineGenerator t.f * cosineGenerator t.g) := by
  have hp : (σ t.firstGenerator * σ t.secondGenerator * σ t.thirdGenerator)^2 =
      (cosineGenerator t.e * cosineGenerator t.f * cosineGenerator t.g)^2 := by
    simp only [mul_pow, ha, hb, hc]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp with hp | hp
  · have hneg := h.2.2 σ hne
    change ArithmeticTriangles.discriminant (σ t.firstGenerator) (σ t.secondGenerator)
      (σ t.thirdGenerator) < 0 at hneg
    unfold ArithmeticTriangles.discriminant at hneg
    rw [ha, hb, hc, hp] at hneg
    exact False.elim ((not_lt_of_ge h.discriminant_pos.le) hneg)
  · exact hp

/-- A nonidentity embedding preserving the three squares sends D to E,
so arithmeticity forces E<0. -/
theorem companion_neg_of_square_preserving (t : Triangle) (h : t.ArithmeticHyperbolic)
    (σ : t.cosineField →ₐ[ℚ] ℝ) (hne : σ ≠ t.cosineField.val)
    (ha : (σ t.firstGenerator)^2 = cosineGenerator t.e ^ 2)
    (hb : (σ t.secondGenerator)^2 = cosineGenerator t.f ^ 2)
    (hc : (σ t.thirdGenerator)^2 = cosineGenerator t.g ^ 2) :
    t.companionDiscriminant < 0 := by
  have hp := t.product_neg_of_square_preserving h σ hne ha hb hc
  have hneg := h.2.2 σ hne
  change ArithmeticTriangles.discriminant (σ t.firstGenerator) (σ t.secondGenerator)
    (σ t.thirdGenerator) < 0 at hneg
  unfold ArithmeticTriangles.discriminant at hneg
  rw [ha, hb, hc, hp] at hneg
  exact hneg

/-- Negating a positive element detects a nonidentity embedding. -/
theorem ne_inclusion_of_neg (t : Triangle) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (x : t.cosineField) (hpos : 0 < (x : ℝ)) (hx : σ x = -(x : ℝ)) : σ ≠ t.cosineField.val := by
  intro heq
  rw [heq] at hx
  change (x : ℝ) = -(x : ℝ) at hx
  linarith

/-- For e>2, at least one positive generator changes sign. Arithmeticity
is not needed to detect that this embedding is nonidentity. -/
theorem even_embedding_ne_inclusion (t : Triangle) (h : t.Admissible)
    (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN) ≠
      t.cosineField.val := by
  let σ := t.cyclotomicRealEmbedding h (t.commonDenominator + 1) (even_index_coprime _ hN)
  have ha : σ t.firstGenerator = (-1 : ℝ)^(t.commonDenominator / t.e) * cosineGenerator t.e :=
    t.even_embedding_cosine h hN _ (Nat.dvd_lcm_left _ _) _ rfl
  have hb : σ t.secondGenerator = (-1 : ℝ)^(t.commonDenominator / t.f) * cosineGenerator t.f :=
    t.even_embedding_cosine h hN _
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hc : σ t.thirdGenerator = (-1 : ℝ)^(t.commonDenominator / t.g) * cosineGenerator t.g :=
    t.even_embedding_cosine h hN _
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  rcases t.exists_odd_quotient h with hodd | hodd | hodd
  · apply t.ne_inclusion_of_neg σ t.firstGenerator (cosineGenerator_pos he)
    change σ t.firstGenerator = -cosineGenerator t.e
    simpa [hodd.neg_one_pow] using ha
  · apply t.ne_inclusion_of_neg σ t.secondGenerator
      (cosineGenerator_pos (by have := h.2.1; omega))
    change σ t.secondGenerator = -cosineGenerator t.f
    simpa [hodd.neg_one_pow] using hb
  · apply t.ne_inclusion_of_neg σ t.thirdGenerator
      (cosineGenerator_pos (by have := h.2.1; have := h.2.2; omega))
    change σ t.thirdGenerator = -cosineGenerator t.g
    simpa [hodd.neg_one_pow] using hc

/-- The even case of the structural lemma. -/
theorem ArithmeticHyperbolic.companion_neg_of_even {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hN : Even t.commonDenominator) :
    t.companionDiscriminant < 0 := by
  let σ := t.cyclotomicRealEmbedding h.admissible (t.commonDenominator + 1) (even_index_coprime _ hN)
  have ha : σ t.firstGenerator = (-1 : ℝ)^(t.commonDenominator / t.e) * cosineGenerator t.e :=
    t.even_embedding_cosine h.admissible hN _ (Nat.dvd_lcm_left _ _) _ rfl
  have hb : σ t.secondGenerator = (-1 : ℝ)^(t.commonDenominator / t.f) * cosineGenerator t.f :=
    t.even_embedding_cosine h.admissible hN _
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hc : σ t.thirdGenerator = (-1 : ℝ)^(t.commonDenominator / t.g) * cosineGenerator t.g :=
    t.even_embedding_cosine h.admissible hN _
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hne := t.even_embedding_ne_inclusion h.admissible he hN
  apply t.companion_neg_of_square_preserving h σ hne
  · rw [ha, mul_pow, sign_pow_sq, one_mul]
  · rw [hb, mul_pow, sign_pow_sq, one_mul]
  · rw [hc, mul_pow, sign_pow_sq, one_mul]

/-- The central algebraic conclusion of Lemma 2.2, in both parity cases. -/
theorem ArithmeticHyperbolic.companion_neg {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) : t.companionDiscriminant < 0 := by
  rcases Nat.even_or_odd t.commonDenominator with hN | hN
  · exact h.companion_neg_of_even he hN
  · exact h.companion_neg_of_odd he hN

/-- The reciprocal inequality (2.8), now a consequence of arithmeticity. -/
theorem ArithmeticHyperbolic.structural {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) : t.StructuralInequality :=
  (t.companionDiscriminant_neg_iff_structural h.admissible).mp (h.companion_neg he)

/-- The unconditional arithmetic form of the middle-denominator bound. -/
theorem ArithmeticHyperbolic.middle_lt_twice_first {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) : t.f < 2 * t.e :=
  t.middle_lt_twice_first h.admissible (h.structural he)

/-- For scalene arithmetic triples with e>2, the last denominator is below e(e+1). -/
theorem ArithmeticHyperbolic.last_lt_first_mul_succ {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hs : t.Scalene) : t.g < t.e * (t.e + 1) :=
  t.last_lt_first_mul_succ h.admissible hs (h.structural he)

/-- The nine initial scalene possibilities at e=3, without an extra structural hypothesis. -/
theorem ArithmeticHyperbolic.scalene_first_three_ranges {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : t.e = 3) :
    (t.f = 4 ∧ 5 ≤ t.g ∧ t.g ≤ 11) ∨ (t.f = 5 ∧ 6 ≤ t.g ∧ t.g ≤ 7) :=
  t.scalene_first_three_ranges h.admissible hs (h.structural (by omega)) he

/-- The initial scalene ranges at e=4, without an extra structural hypothesis. -/
theorem ArithmeticHyperbolic.scalene_first_four_ranges {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : t.e = 4) :
    (t.f = 5 ∧ 6 ≤ t.g ∧ t.g ≤ 19) ∨ (t.f = 6 ∧ 7 ≤ t.g ∧ t.g ≤ 11) ∨
      (t.f = 7 ∧ 8 ≤ t.g ∧ t.g ≤ 9) :=
  t.scalene_first_four_ranges h.admissible hs (h.structural (by omega)) he

/-- The more precise arithmetic bound g < ef/(f-e) for scalene triples. -/
theorem ArithmeticHyperbolic.last_lt_quotient {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hs : t.Scalene) :
    (t.g : ℝ) < (t.e : ℝ) * t.f / (t.f - t.e) :=
  t.last_lt_quotient h.admissible hs (h.structural he)

end Triangle
end ArithmeticTriangles
