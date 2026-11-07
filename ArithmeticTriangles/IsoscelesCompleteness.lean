module

public import ArithmeticTriangles.RightCompleteness
public import ArithmeticTriangles.EvenParity
public import ArithmeticTriangles.SmallestConjugate

/-!
# Further completeness results for the isosceles families

For two equal smaller entries, the subfamilies (4,4,n) and (6,6,n) admit
an elementary argument: the repeated cosine has rational square. A small
unit for n, lifted to the ambient conductor, gives a forbidden embedding.
This completely settles both subfamilies without bounding n in advance.

For two equal larger entries, the structural inequality gives f<2e.
We combine it with exact sign certificates to classify the range e≤15.
The unbounded remaining isosceles cases are kept explicit.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- Lift a unit for the nth cosine to either ambient conductor. For e=4
oddness already suffices; for e=6 we reuse the lift that avoids the prime 3. -/
theorem lift_unit_for_four_or_six_pair (e n k : ℕ) (he : e = 4 ∨ e = 6)
    (hk : k.Coprime (2 * n)) :
    ∃ j : ℕ, j.Coprime (2 * (⟨e, e, n⟩ : Triangle).commonDenominator) ∧
      (j = k ∨ j = k + 2 * n) := by
  rcases he with rfl | rfl
  · have hk2 : k.Coprime 2 := hk.of_dvd_right (dvd_mul_right 2 n)
    have hk4 : k.Coprime 4 := by simpa using hk2.pow_right 2
    have hd : 2 * (⟨4, 4, n⟩ : Triangle).commonDenominator ∣ 4 * (2 * n) := by
      have hN : (⟨4, 4, n⟩ : Triangle).commonDenominator ∣ 4 * n :=
        Nat.lcm_dvd (dvd_mul_right 4 n)
          (Nat.lcm_dvd (dvd_mul_right 4 n) (dvd_mul_left n 4))
      convert Nat.mul_dvd_mul_left 2 hN using 1
      ring
    exact ⟨k, (hk4.mul_right hk).of_dvd_right hd, Or.inl rfl⟩
  · obtain ⟨j, hj, hchoice⟩ := lift_unit_for_three_pair n k hk
    let M := (⟨3, 3, n⟩ : Triangle).commonDenominator
    have h3 : 3 ∣ M := Nat.dvd_lcm_left _ _
    have hn : n ∣ M := (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
    have h6 : 6 ∣ 2 * M := by convert Nat.mul_dvd_mul_left 2 h3
    have hN : (⟨6, 6, n⟩ : Triangle).commonDenominator ∣ 2 * M :=
      Nat.lcm_dvd h6 (Nat.lcm_dvd h6 (hn.trans (dvd_mul_left M 2)))
    have hj2 : j.Coprime 2 := hj.of_dvd_right (dvd_mul_right 2 M)
    exact ⟨j, (hj2.mul_right hj).of_dvd_right (Nat.mul_dvd_mul_left 2 hN), hchoice⟩

/-- A rational square ≥2 makes the isosceles factor H=a²+c−2 positive
whenever c>1. A small unit gives just such a nonprincipal value of c. -/
theorem not_rational_square_pair_arithmetic_of_small_unit (e n d k j : ℕ)
    (hsq : cosineGenerator e ^ 2 = (d : ℝ)) (hd : 2 ≤ d)
    (hk1 : 1 < k) (hk3 : 3 * k < n)
    (hj : j.Coprime (2 * (⟨e, e, n⟩ : Triangle).commonDenominator))
    (hchoice : j = k ∨ j = k + 2 * n) :
    ¬(⟨e, e, n⟩ : Triangle).ArithmeticHyperbolic := by
  intro h
  let t : Triangle := ⟨e, e, n⟩
  let σ := t.cyclotomicRealEmbedding h.admissible j hj
  have hu := small_index_cosine_bounds n k hk1 hk3
  have hc : σ t.thirdGenerator = 2 * Real.cos ((k : ℝ) * Real.pi / n) := by
    rw [t.cyclotomicRealEmbedding_cosine h.admissible j hj n
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl]
    rcases hchoice with rfl | rfl
    · rfl
    · rw [cosine_index_add_two_mul n k (by omega)]
  have ha : (σ t.firstGenerator) ^ 2 = (d : ℝ) :=
    t.embedding_preserves_square σ t.firstGenerator d hsq
  have hne : σ ≠ t.cosineField.val := by
    intro heq
    have he := DFunLike.congr_fun heq t.thirdGenerator
    rw [hc] at he
    exact (ne_of_lt hu.2) he
  have hneg := h.2.2 σ hne
  change discriminant (σ t.firstGenerator) (σ t.firstGenerator) (σ t.thirdGenerator) < 0 at hneg
  rw [discriminant_isosceles_first, ha, hc] at hneg
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (2 * Real.cos ((k : ℝ) * Real.pi / n) + 2) *
      ((d : ℝ) + 2 * Real.cos ((k : ℝ) * Real.pi / n) - 2) :=
    mul_pos (by linarith [hu.1]) (by linarith [hu.1])
  linarith

/-- Arithmeticity in either rational-square subfamily forces n into the
same eight-element set used for the diagonal classification. -/
theorem four_or_six_pair_denominator_mem (e n : ℕ) (he : e = 4 ∨ e = 6)
    (h : (⟨e, e, n⟩ : Triangle).ArithmeticHyperbolic) : n ∈ repeatedDenominators := by
  have hen : e ≤ n := h.admissible.2.2
  have hn4 : 4 ≤ n := by omega
  by_contra hnot
  obtain ⟨k, hk1, hk3, hk⟩ := exists_small_unit_of_not_mem n hn4 hnot
  obtain ⟨j, hj, hchoice⟩ := lift_unit_for_four_or_six_pair e n k he hk
  rcases he with rfl | rfl
  · exact not_rational_square_pair_arithmetic_of_small_unit 4 n 2 k j
      cosineGenerator_four_sq (by decide) hk1 hk3 hj hchoice h
  · exact not_rational_square_pair_arithmetic_of_small_unit 6 n 3 k j
      cosineGenerator_six_sq (by decide) hk1 hk3 hj hchoice h

set_option maxRecDepth 16384 in
/-- The remaining finite possibilities have a forbidden conjugate unless
all three denominators coincide. -/
theorem four_or_six_pair_sign_certificates :
    ∀ e : Fin 7, ((e : ℕ) = 4 ∨ (e : ℕ) = 6) →
    ∀ n : Fin 16, (e : ℕ) ≤ n → (n : ℕ) ∈ repeatedDenominators → (n : ℕ) ≠ e →
      ∃ k : Fin 40,
        (k : ℕ).Coprime (2 * (⟨e, e, n⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, e, n⟩ : Triangle).FixesCosines k ∧
        (⟨e, e, n⟩ : Triangle).discriminantSignCertificate k = 1 := by
  decide +kernel

/-- The only arithmetic triples in the entire (4,4,n) and (6,6,n)
subfamilies are their diagonal members. No bound on n is assumed. -/
theorem four_or_six_pair_arithmetic_iff (e n : ℕ) (he : e = 4 ∨ e = 6) :
    (⟨e, e, n⟩ : Triangle).ArithmeticHyperbolic ↔ n = e := by
  constructor
  · intro h
    have hm := four_or_six_pair_denominator_mem e n he h
    have hn : n < 16 := by
      unfold repeatedDenominators at hm
      fin_cases hm <;> omega
    by_contra hne
    obtain ⟨k, hk, hfix, hcert⟩ := four_or_six_pair_sign_certificates
      ⟨e, by omega⟩ he ⟨n, hn⟩ h.admissible.2.2 hm hne
    exact (⟨e, e, n⟩ : Triangle).not_arithmeticHyperbolic_of_sign_certificate
      h.admissible k hk hfix hcert h
  · rintro rfl
    apply expectedArithmeticTriples_arithmeticHyperbolic
    rcases he with rfl | rfl <;> decide

set_option maxRecDepth 32768 in
/-- The structural range for e<f=g, with 3≤e≤15. Every triple other than
the two listed survivors has a kernel-checked positive conjugate. -/
theorem equal_larger_sign_certificates :
    ∀ e : Fin 16, 3 ≤ (e : ℕ) →
    ∀ f : Fin 30, (e : ℕ) < f → (f : ℕ) < 2 * e →
      (⟨e, f, f⟩ : Triangle) ∈ expectedArithmeticTriples ∨
      ∃ k : Fin 80,
        (k : ℕ).Coprime (2 * (⟨e, f, f⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, f, f⟩ : Triangle).FixesCosines k ∧
        (⟨e, f, f⟩ : Triangle).discriminantSignCertificate k = 1 := by
  decide +kernel

/-- A complete classification of the equal-larger family with smallest
entry at most 15. The second entry is initially unbounded. -/
theorem equal_larger_arithmetic_iff_of_first_le_fifteen (e f : ℕ)
    (he : 2 < e) (hef : e < f) (he15 : e ≤ 15) :
    (⟨e, f, f⟩ : Triangle).ArithmeticHyperbolic ↔ (e = 3 ∨ e = 4) ∧ f = 5 := by
  constructor
  · intro h
    have hf : f < 2 * e := h.middle_lt_twice_first he
    rcases equal_larger_sign_certificates ⟨e, by omega⟩ he ⟨f, by omega⟩ hef hf with
      hm | ⟨k, hk, hfix, hcert⟩
    · simp [expectedArithmeticTriples, Triangle.mk.injEq] at hm
      omega
    · exact False.elim ((⟨e, f, f⟩ : Triangle).not_arithmeticHyperbolic_of_sign_certificate
        h.admissible k hk hfix hcert h)
  · rintro ⟨rfl | rfl, rfl⟩ <;>
      exact expectedArithmeticTriples_arithmeticHyperbolic _ (by decide)

namespace Triangle

/-- The factorization D=(c+2)(a²+c−2) persists under every embedding. -/
theorem discriminantAt_isosceles_first (t : Triangle) (hef : t.e = t.f)
    (σ : t.cosineField →ₐ[ℚ] ℝ) :
    t.discriminantAt σ = (σ t.thirdGenerator + 2) *
      ((σ t.firstGenerator) ^ 2 + σ t.thirdGenerator - 2) := by
  have hab : t.firstGenerator = t.secondGenerator := by
    apply Subtype.ext
    change cosineGenerator t.e = cosineGenerator t.f
    rw [hef]
  unfold discriminantAt
  rw [← hab, discriminant_isosceles_first]

/-- Likewise D=(a+2)(a+b²−2) when the larger entries coincide. -/
theorem discriminantAt_isosceles_last (t : Triangle) (hfg : t.f = t.g)
    (σ : t.cosineField →ₐ[ℚ] ℝ) :
    t.discriminantAt σ = (σ t.firstGenerator + 2) *
      (σ t.firstGenerator + (σ t.secondGenerator) ^ 2 - 2) := by
  have hbc : t.secondGenerator = t.thirdGenerator := by
    apply Subtype.ext
    change cosineGenerator t.f = cosineGenerator t.g
    rw [hfg]
  unfold discriminantAt
  rw [← hbc, discriminant_isosceles_last]

/-- Since every conjugate c is strictly above −2, the reduced factor H
has exactly the same sign as D in the equal-smaller family. -/
theorem discriminantAt_neg_iff_isosceles_first (t : Triangle) (hadm : t.Admissible)
    (hef : t.e = t.f) (σ : t.cosineField →ₐ[ℚ] ℝ) :
    t.discriminantAt σ < 0 ↔ (σ t.firstGenerator) ^ 2 + σ t.thirdGenerator - 2 < 0 := by
  have hc := t.embedding_cosine_mem_Ioo hadm σ t.g
    (hadm.1.trans (hadm.2.1.trans hadm.2.2))
    ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) t.thirdGenerator rfl
  rw [t.discriminantAt_isosceles_first hef σ]
  have hp : 0 < σ t.thirdGenerator + 2 := by linarith [hc.1]
  simp only [mul_neg_iff, not_lt_of_ge hp.le, hp, false_and, true_and, or_false]

/-- The corresponding reduced-factor criterion for the equal-larger family. -/
theorem discriminantAt_neg_iff_isosceles_last (t : Triangle) (hadm : t.Admissible)
    (hfg : t.f = t.g) (σ : t.cosineField →ₐ[ℚ] ℝ) :
    t.discriminantAt σ < 0 ↔ σ t.firstGenerator + (σ t.secondGenerator) ^ 2 - 2 < 0 := by
  have ha := t.embedding_cosine_mem_Ioo hadm σ t.e hadm.1
    (Nat.dvd_lcm_left _ _) t.firstGenerator rfl
  rw [t.discriminantAt_isosceles_last hfg σ]
  have hp : 0 < σ t.firstGenerator + 2 := by linarith [ha.1]
  simp only [mul_neg_iff, not_lt_of_ge hp.le, hp, false_and, true_and, or_false]

/-- For e=f<g and e>2, an embedding fixing c has H≥c−a>0.
Arithmeticity therefore forces it to fix the whole field. This is the
embedding-theoretic step behind the paper's reduction F=C_g. -/
theorem ArithmeticHyperbolic.embedding_eq_inclusion_of_fixes_third_isosceles
    {t : Triangle} (h : t.ArithmeticHyperbolic) (he : 2 < t.e)
    (hef : t.e = t.f) (hfg : t.f < t.g) (σ : t.cosineField →ₐ[ℚ] ℝ)
    (hfix : σ t.thirdGenerator = cosineGenerator t.g) : σ = t.cosineField.val := by
  have hsq := t.embedding_cosine_sq_lower_bound h.admissible σ t.e he
    (Nat.dvd_lcm_left _ _) t.firstGenerator rfl
  have hlt := cosineGenerator_lt_of_lt t.e t.g h.admissible.1 (by omega)
  apply h.embedding_eq_inclusion_of_nonneg σ
  rw [t.discriminantAt_isosceles_first hef σ, hfix]
  exact (mul_pos (by linarith [cosineGenerator_nonneg (h.admissible.1.trans
    (h.admissible.2.1.trans h.admissible.2.2))]) (by linarith)).le

/-- For e<f=g, a nonidentity embedding fixing a must send b into the
short interval |σ(b)|<sqrt(2−a). The squared form avoids square-root bookkeeping. -/
theorem ArithmeticHyperbolic.square_lt_of_fixes_first_isosceles {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hfg : t.f = t.g)
    (σ : t.cosineField →ₐ[ℚ] ℝ) (hne : σ ≠ t.cosineField.val)
    (hfix : σ t.firstGenerator = cosineGenerator t.e) :
    (σ t.secondGenerator) ^ 2 < 2 - cosineGenerator t.e := by
  have hh := (t.discriminantAt_neg_iff_isosceles_last h.admissible hfg σ).mp (h.2.2 σ hne)
  rw [hfix] at hh
  linarith

/-- In the even-conductor equal-smaller case, the unrepeated denominator
carries the full power of two in the conductor. Repeated positions cancel in parity. -/
theorem ArithmeticHyperbolic.odd_last_quotient_of_isosceles_first {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hef : t.e = t.f)
    (hN : Even t.commonDenominator) : Odd (t.commonDenominator / t.g) := by
  have hs := h.odd_quotient_sum he hN
  rw [← hef] at hs
  simp only [Nat.odd_iff] at hs ⊢
  omega

/-- In the even-conductor equal-larger case, the first denominator carries
the full power of two in the conductor. -/
theorem ArithmeticHyperbolic.odd_first_quotient_of_isosceles_last {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hfg : t.f = t.g)
    (hN : Even t.commonDenominator) : Odd (t.commonDenominator / t.e) := by
  have hs := h.odd_quotient_sum he hN
  rw [← hfg] at hs
  simp only [Nat.odd_iff] at hs ⊢
  omega

/-- The equal-larger branch is closed through first denominator 15. -/
theorem ArithmeticHyperbolic.mem_expected_of_isosceles_last_small {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) (hef : t.e < t.f) (hfg : t.f = t.g)
    (he15 : t.e ≤ 15) : t ∈ expectedArithmeticTriples := by
  rcases t with ⟨e, f, g⟩
  change f = g at hfg
  subst g
  have hm := (equal_larger_arithmetic_iff_of_first_le_fifteen e f he hef he15).mp h
  rcases hm with ⟨rfl | rfl, rfl⟩ <;> decide

/-- An unequal initial pair of 4s or 6s is impossible. -/
theorem ArithmeticHyperbolic.not_four_or_six_of_isosceles_first {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hef : t.e = t.f) (hfg : t.f < t.g) :
    t.e ≠ 4 ∧ t.e ≠ 6 := by
  rcases t with ⟨e, f, g⟩
  change e = f at hef
  change f < g at hfg
  subst f
  have hh : ¬(e = 4 ∨ e = 6) := by
    intro he
    have := (four_or_six_pair_arithmetic_iff e g he).mp h
    omega
  tauto

end Triangle
end ArithmeticTriangles
