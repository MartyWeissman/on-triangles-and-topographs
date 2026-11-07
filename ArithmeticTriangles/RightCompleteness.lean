module

public import ArithmeticTriangles.RepeatedCompleteness
public import ArithmeticTriangles.Structural

/-!
# Complete classification of right triangles

For an arithmetic triple (2,f,g), both f and g must be odd. A sign-changing
embedding proves this without using the general cosine-field degree formula.
Writing L=lcm(f,g), the index L+2 then gives a second useful embedding. Its
negative discriminant bounds f and g, leaving a finite exact sign check.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- A right hyperbolic triangle has no second right angle. -/
theorem right_middle_gt_two (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) : 2 < f := by
  have hf : 2 ≤ f := h.admissible.2.1
  by_contra hnot
  have heq : f = 2 := by omega
  subst f
  have hh := h.hyperbolic
  change 1 / (2 : ℝ) + 1 / 2 + 1 / g < 1 at hh
  have hp : (0 : ℝ) ≤ 1 / g := by positivity
  linarith

/-- In a right arithmetic triangle, the sign-changing embedding must be the
identity: the first generator is zero and the other two squares determine D.
If lcm(f,g) were even, at least one nonzero generator would change sign. -/
theorem right_denominators_odd (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) : Odd f ∧ Odd g := by
  let t : Triangle := ⟨2, f, g⟩
  have hf := right_middle_gt_two f g h
  have hfg : f ≤ g := h.admissible.2.2
  have hN : Even t.commonDenominator := even_iff_two_dvd.mpr (Nat.dvd_lcm_left _ _)
  let σ := t.cyclotomicRealEmbedding h.admissible (t.commonDenominator + 1)
    (even_index_coprime _ hN)
  have ha : t.firstGenerator = 0 := by
    apply t.cosineField.val.injective
    exact cosineGenerator_two
  have hb : σ t.secondGenerator = (-1 : ℝ) ^ (t.commonDenominator / f) * cosineGenerator f :=
    t.even_embedding_cosine h.admissible hN f
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hc : σ t.thirdGenerator = (-1 : ℝ) ^ (t.commonDenominator / g) * cosineGenerator g :=
    t.even_embedding_cosine h.admissible hN g
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hid : σ = t.cosineField.val := by
    apply h.embedding_eq_inclusion_of_nonneg
    change 0 ≤ discriminant (σ t.firstGenerator) (σ t.secondGenerator) (σ t.thirdGenerator)
    rw [ha, map_zero, discriminant_right, hb, hc, mul_pow, mul_pow, sign_pow_sq,
      sign_pow_sq, one_mul, one_mul]
    have hp := h.discriminant_pos
    simpa [Triangle.discriminant, cosineGenerator_two, discriminant_right] using hp.le
  have hfe : Even (t.commonDenominator / f) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    rw [ho.neg_one_pow, hid] at hb
    change cosineGenerator f = -1 * cosineGenerator f at hb
    linarith [cosineGenerator_pos hf]
  have hge : Even (t.commonDenominator / g) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    rw [ho.neg_one_pow, hid] at hc
    change cosineGenerator g = -1 * cosineGenerator g at hc
    linarith [cosineGenerator_pos (show 2 < g by omega)]
  have hL : Odd (f.lcm g) := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    have hNL : t.commonDenominator = f.lcm g := by
      exact Nat.lcm_eq_right (even_iff_two_dvd.mp heven)
    have hNz := t.commonDenominator_ne_zero h.admissible
    have hfd := dvd_half_of_even_quotient _ f hNz
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) hfe
    have hgd := dvd_half_of_even_quotient _ g hNz
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) hge
    have hd : t.commonDenominator ∣ t.commonDenominator / 2 := by
      rw [hNL] at *
      exact Nat.lcm_dvd hfd hgd
    have htwo : 2 ≤ t.commonDenominator :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hNz) (Nat.dvd_lcm_left _ _)
    have := Nat.le_of_dvd (by omega : 0 < t.commonDenominator / 2) hd
    have := Nat.div_lt_self (Nat.pos_of_ne_zero hNz) (by omega : 1 < 2)
    omega
  exact ⟨hL.of_dvd_nat (Nat.dvd_lcm_left _ _), hL.of_dvd_nat (Nat.dvd_lcm_right _ _)⟩

/-- The odd-conductor substitution u↦2−u² squares to a fourth-angle cosine. -/
theorem right_doubled_discriminant (f g : ℕ) :
    discriminant 0 (2 - cosineGenerator f ^ 2) (2 - cosineGenerator g ^ 2) =
      2 * Real.cos (4 * Real.pi / f) + 2 * Real.cos (4 * Real.pi / g) := by
  have hf := Real.cos_two_mul (Real.pi / f)
  have hg := Real.cos_two_mul (Real.pi / g)
  have hf' := Real.cos_two_mul (2 * (Real.pi / f))
  have hg' := Real.cos_two_mul (2 * (Real.pi / g))
  rw [show 2 * (2 * (Real.pi / f)) = 4 * Real.pi / f by ring] at hf'
  rw [show 2 * (2 * (Real.pi / g)) = 4 * Real.pi / g by ring] at hg'
  rw [discriminant_right, cosineGenerator, cosineGenerator, hf', hg', hf, hg]
  ring

/-- The index L+2, with L=lcm(f,g) odd, is a nonidentity embedding. The
arithmetic sign rule therefore gives this elementary cosine inequality. -/
theorem right_fourth_angle_sum_neg (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) :
    Real.cos (4 * Real.pi / f) + Real.cos (4 * Real.pi / g) < 0 := by
  let t : Triangle := ⟨2, f, g⟩
  have hf := right_middle_gt_two f g h
  have hfg : f ≤ g := h.admissible.2.2
  obtain ⟨hfo, hgo⟩ := right_denominators_odd f g h
  have hg5 : 5 ≤ g := by
    by_contra hn
    have hg3 : g = 3 := by obtain ⟨r, hr⟩ := hgo; omega
    have hf3 : f = 3 := by omega
    have hh := h.hyperbolic
    norm_num [Triangle.Hyperbolic, hg3, hf3] at hh
  let L := f.lcm g
  have hL : Odd L := (hfo.mul hgo).of_dvd_nat (Nat.lcm_dvd_mul f g)
  have hk : (L + 2).Coprime (2 * t.commonDenominator) := by
    have hbase := odd_index_coprime L hL
    have hd : 2 * t.commonDenominator ∣ 2 * (2 * L) := by
      apply Nat.mul_dvd_mul_left
      exact Nat.lcm_dvd (dvd_mul_right 2 L) (dvd_mul_left L 2)
    exact ((hbase.of_dvd_right (dvd_mul_right 2 L)).mul_right hbase).of_dvd_right hd
  let σ := t.cyclotomicRealEmbedding h.admissible (L + 2) hk
  have ha : t.firstGenerator = 0 := by
    apply t.cosineField.val.injective
    exact cosineGenerator_two
  have hb : σ t.secondGenerator = 2 - cosineGenerator f ^ 2 := by
    rw [t.cyclotomicRealEmbedding_cosine h.admissible (L + 2) hk f
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl]
    exact cosine_odd_index L f hL (Nat.dvd_lcm_left _ _)
  have hc : σ t.thirdGenerator = 2 - cosineGenerator g ^ 2 := by
    rw [t.cyclotomicRealEmbedding_cosine h.admissible (L + 2) hk g
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl]
    exact cosine_odd_index L g hL (Nat.dvd_lcm_right _ _)
  have hnegc : σ t.thirdGenerator < 0 := by
    have hgr : (4 : ℝ) < g := by exact_mod_cast (show 4 < g by omega)
    have hang : 2 * (Real.pi / g) < Real.pi / 2 := by
      rw [show 2 * (Real.pi / g) = 2 * Real.pi / g by ring]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < g)).mpr
      nlinarith [Real.pi_pos]
    have hp := Real.cos_pos_of_mem_Ioo
      (show 2 * (Real.pi / g) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by
          have : 0 ≤ 2 * (Real.pi / g) := by positivity
          linarith [Real.pi_pos], hang⟩)
    rw [Real.cos_two_mul] at hp
    rw [hc, cosineGenerator]
    nlinarith
  have hne : σ ≠ t.cosineField.val := by
    intro heq
    rw [heq] at hnegc
    exact (not_lt_of_gt (cosineGenerator_pos (show 2 < g by omega))) hnegc
  have hneg := h.2.2 σ hne
  change discriminant (σ t.firstGenerator) (σ t.secondGenerator) (σ t.thirdGenerator) < 0 at hneg
  rw [ha, map_zero, hb, hc, right_doubled_discriminant] at hneg
  linarith

/-- The fourth-angle inequality forces f≤7. For f≥8 both cosine terms
are nonnegative, including the boundary value cos(π/2)=0. -/
theorem right_middle_le_seven (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) : f ≤ 7 := by
  by_contra hn
  have hf : 8 ≤ f := by omega
  have hfg : f ≤ g := h.admissible.2.2
  have hnonneg : ∀ n : ℕ, 8 ≤ n → 0 ≤ Real.cos (4 * Real.pi / n) := by
    intro n hn
    have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ 4 * Real.pi / n := by positivity
      linarith [Real.pi_pos]
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
      nlinarith [Real.pi_pos]
  have := right_fourth_angle_sum_neg f g h
  linarith [hnonneg f hf, hnonneg g (by omega)]

/-- A convenient uniform bound g<20. The paper's sharper bounds can be
recovered, but this common finite box keeps the exact final check simple. -/
theorem right_last_lt_twenty (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) : g < 20 := by
  have hf := right_middle_gt_two f g h
  obtain ⟨hfo, _⟩ := right_denominators_odd f g h
  have hn := right_fourth_angle_sum_neg f g h
  by_contra hnot
  have hg : 20 ≤ g := by omega
  have hgr : (20 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by positivity
  have hangle : 4 * Real.pi / g ≤ Real.pi / 5 := by
    apply (div_le_iff₀ hgpos).mpr
    nlinarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ 4 * Real.pi / g)
    (show Real.pi / 5 ≤ Real.pi by linarith [Real.pi_pos]) hangle
  by_cases hf3 : f = 3
  · have heq : 4 * Real.pi / (3 : ℝ) = Real.pi + Real.pi / 3 := by ring
    have hc' := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ Real.pi / 5)
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos])
      (show Real.pi / 5 ≤ Real.pi / 3 by linarith [Real.pi_pos])
    rw [hf3] at hn
    norm_num only [Nat.cast_ofNat] at hn
    rw [heq, add_comm Real.pi, Real.cos_add_pi, Real.cos_pi_div_three] at hn
    rw [Real.cos_pi_div_three] at hc'
    linarith
  · have hf5 : 5 ≤ f := by obtain ⟨r, hr⟩ := hfo; omega
    have hfr : (5 : ℝ) ≤ f := by exact_mod_cast hf5
    have hanglef : 4 * Real.pi / f ≤ 4 * Real.pi / 5 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < f)).mpr
      nlinarith [Real.pi_pos]
    have hc' := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ 4 * Real.pi / f)
      (show 4 * Real.pi / 5 ≤ Real.pi by linarith [Real.pi_pos]) hanglef
    rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub] at hc'
    linarith

set_option maxRecDepth 16384 in
/-- Every geometric possibility in the bounded odd box is either listed or
has an explicit forbidden conjugate. All tests use exact rational arithmetic. -/
theorem right_sign_certificates :
    ∀ f : Fin 8, 3 ≤ (f : ℕ) → Odd (f : ℕ) →
    ∀ g : Fin 20, (f : ℕ) ≤ g → Odd (g : ℕ) → ((f : ℕ) = 3 → 6 < (g : ℕ)) →
      (⟨2, f, g⟩ : Triangle) ∈ expectedArithmeticTriples ∨
      ∃ k : Fin 40,
        (k : ℕ).Coprime (2 * (⟨2, f, g⟩ : Triangle).commonDenominator) ∧
        ¬(⟨2, f, g⟩ : Triangle).FixesCosines k ∧
        (⟨2, f, g⟩ : Triangle).discriminantSignCertificate k = 1 := by
  decide +kernel

/-- Necessity for all right triangles, with no prior denominator bound. -/
theorem right_mem_expected (f g : ℕ)
    (h : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) :
    (⟨2, f, g⟩ : Triangle) ∈ expectedArithmeticTriples := by
  have hf := right_middle_gt_two f g h
  have hf7 := right_middle_le_seven f g h
  have hg20 := right_last_lt_twenty f g h
  have hfg : f ≤ g := h.admissible.2.2
  obtain ⟨hfo, hgo⟩ := right_denominators_odd f g h
  have hthree : f = 3 → 6 < g := by
    intro heq
    subst f
    by_contra hn
    have hg6 : g ≤ 6 := by omega
    have hh := h.hyperbolic
    interval_cases g <;> norm_num [Triangle.Hyperbolic] at hh
  rcases right_sign_certificates ⟨f, by omega⟩ hf hfo ⟨g, hg20⟩ hfg hgo hthree with
    hmem | ⟨k, hk, hfix, hcert⟩
  · exact hmem
  · exact False.elim ((⟨2, f, g⟩ : Triangle).not_arithmeticHyperbolic_of_sign_certificate
      h.admissible k hk hfix hcert h)

/-- The five and only five right arithmetic triples in our full cosine-field
convention. This is an equivalence for arbitrary natural f and g. -/
theorem right_arithmetic_iff (f g : ℕ) :
    (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic ↔
      (f = 3 ∧ (g = 7 ∨ g = 9 ∨ g = 11)) ∨ (f = 5 ∧ g = 5) ∨ (f = 7 ∧ g = 7) := by
  constructor
  · intro h
    have hm := right_mem_expected f g h
    simp [expectedArithmeticTriples, Triangle.mk.injEq] at hm
    tauto
  · intro h
    apply expectedArithmeticTriples_arithmeticHyperbolic
    rcases h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

namespace Triangle

/-- The right branch of the final completeness proof is closed. -/
theorem ArithmeticHyperbolic.mem_expected_of_right {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hr : t.Right) : t ∈ expectedArithmeticTriples := by
  rcases t with ⟨e, f, g⟩
  change e = 2 at hr
  subst e
  exact right_mem_expected f g h

end Triangle
end ArithmeticTriangles
