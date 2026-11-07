module

public import ArithmeticTriangles.CyclotomicEmbeddings
public import ArithmeticTriangles.Trigonometry

/-!
# Exact signs from rational angles

The four-cosine factorization of D reduces its sign at a cyclotomic embedding
to signs of cos(qπ) for rational q. Periodicity and monotonicity justify
certificates taking values +1 or -1. All certificate computations use exact
rationals and integers; they never approximate π or evaluate a real cosine.

The certificate returns 0 when neither strict sign is certified. No theorem
uses that result as evidence of positivity or negativity. Successful negative
certificates at every nonidentity embedding prove arithmeticity; a single
positive certificate at a nonidentity embedding disproves it.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- Subtract an even integer from q. The chosen representative is centered
around zero, and periodicity preserves cos(qπ). Soundness below checks the
needed interval explicitly, so it does not need a theorem about floor bounds. -/
def reducedCosineAngle (q : ℚ) : ℚ := q - 2 * (⌊(q + 1) / 2⌋ : ℚ)

/-- A decidable strict-sign certificate for cos(qπ). Reflection replaces the
reduced angle by its absolute value. At the boundary 1/2, neither sign passes. -/
def cosineSignCertificate (q : ℚ) : ℤ :=
  if |reducedCosineAngle q| < 1 / 2 then 1
  else if |reducedCosineAngle q| ≤ 1 ∧ 1 / 2 < |reducedCosineAngle q| then -1 else 0

/-- Reduction changes the angle by an integer multiple of 2π. -/
theorem cos_reducedCosineAngle (q : ℚ) :
    Real.cos ((reducedCosineAngle q : ℝ) * Real.pi) = Real.cos ((q : ℝ) * Real.pi) := by
  unfold reducedCosineAngle
  push_cast
  rw [sub_mul]
  have he : (2 * (⌊(q + 1) / 2⌋ : ℝ)) * Real.pi =
      (⌊(q + 1) / 2⌋ : ℝ) * (2 * Real.pi) := by ring
  rw [he, Real.cos_sub_int_mul_two_pi]

/-- Soundness of a nonzero sign certificate: multiplying the cosine by
its certified sign gives a strictly positive real number. -/
theorem cosineSignCertificate_pos (q : ℚ) (h : cosineSignCertificate q ≠ 0) :
    0 < (cosineSignCertificate q : ℝ) * Real.cos ((q : ℝ) * Real.pi) := by
  rw [← cos_reducedCosineAngle]
  have habs : Real.cos ((reducedCosineAngle q : ℝ) * Real.pi) =
      Real.cos ((|reducedCosineAngle q| : ℚ) * Real.pi) := by
    rw [← Real.cos_abs ((reducedCosineAngle q : ℝ) * Real.pi),
      abs_mul, abs_of_pos Real.pi_pos, Rat.cast_abs]
  rw [habs]
  unfold cosineSignCertificate at h ⊢
  split_ifs with hp hn
  · have hp' : ((|reducedCosineAngle q| : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hp
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hp'
    have h0 : 0 ≤ (|reducedCosineAngle q| : ℚ) * Real.pi := by positivity
    have hlt : (|reducedCosineAngle q| : ℚ) * Real.pi < Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hc := Real.cos_pos_of_mem_Ioo (show (|reducedCosineAngle q| : ℚ) * Real.pi ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    simpa using hc
  · have hn1 : (|reducedCosineAngle q| : ℚ) ≤ (1 : ℝ) := by exact_mod_cast hn.1
    have hn2 : ((1 / 2 : ℚ) : ℝ) < ((|reducedCosineAngle q| : ℚ) : ℝ) := Rat.cast_lt.mpr hn.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hn2
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2)
      (show (|reducedCosineAngle q| : ℚ) * Real.pi ≤ Real.pi by nlinarith [Real.pi_pos])
      (show Real.pi / 2 < (|reducedCosineAngle q| : ℚ) * Real.pi by nlinarith [Real.pi_pos])
    rw [Real.cos_pi_div_two] at hc
    simpa using neg_pos.mpr hc
  · simp only [ite_eq_right hp, ite_eq_right hn, ne_eq, not_true_eq_false] at h

/-- Multiply the four certified cosine signs in the factorization of D.
The inputs a,b,c represent angles aπ,bπ,cπ and need not lie in (0,1). -/
def rationalDiscriminantSign (a b c : ℚ) : ℤ :=
  cosineSignCertificate ((a + b + c) / 2) * cosineSignCertificate ((a + b - c) / 2) *
    cosineSignCertificate ((a - b + c) / 2) * cosineSignCertificate ((-a + b + c) / 2)

/-- A nonzero product certificate gives the sign of the real discriminant.
The factor 16 in the trigonometric identity is positive. -/
theorem rationalDiscriminantSign_pos (a b c : ℚ) (h : rationalDiscriminantSign a b c ≠ 0) :
    0 < (rationalDiscriminantSign a b c : ℝ) *
      discriminant (2 * Real.cos ((a : ℝ) * Real.pi))
        (2 * Real.cos ((b : ℝ) * Real.pi)) (2 * Real.cos ((c : ℝ) * Real.pi)) := by
  have h1 : cosineSignCertificate ((a + b + c) / 2) ≠ 0 := by
    intro hz; simp [rationalDiscriminantSign, hz] at h
  have h2 : cosineSignCertificate ((a + b - c) / 2) ≠ 0 := by
    intro hz; simp [rationalDiscriminantSign, hz] at h
  have h3 : cosineSignCertificate ((a - b + c) / 2) ≠ 0 := by
    intro hz; simp [rationalDiscriminantSign, hz] at h
  have h4 : cosineSignCertificate ((-a + b + c) / 2) ≠ 0 := by
    intro hz; simp [rationalDiscriminantSign, hz] at h
  have hp := mul_pos (mul_pos (mul_pos (cosineSignCertificate_pos _ h1)
    (cosineSignCertificate_pos _ h2)) (cosineSignCertificate_pos _ h3))
    (cosineSignCertificate_pos _ h4)
  have hp16 := mul_pos (by norm_num : (0 : ℝ) < 16) hp
  convert hp16 using 1
  unfold rationalDiscriminantSign
  rw [discriminant_cos_product]
  push_cast
  ring_nf

namespace Triangle

/-- The exact arithmetic certificate for the cyclotomic index k. -/
def discriminantSignCertificate (t : Triangle) (k : ℕ) : ℤ :=
  rationalDiscriminantSign ((k : ℚ) / t.e) ((k : ℚ) / t.f) ((k : ℚ) / t.g)

/-- Specialize the rational-angle soundness theorem to a triangle embedding. -/
theorem discriminantSignCertificate_pos (t : Triangle) (k : ℕ)
    (h : t.discriminantSignCertificate k ≠ 0) :
    0 < (t.discriminantSignCertificate k : ℝ) * t.cyclotomicDiscriminant k := by
  have hp := rationalDiscriminantSign_pos ((k : ℚ) / t.e) ((k : ℚ) / t.f) ((k : ℚ) / t.g) h
  convert hp using 1
  simp only [discriminantSignCertificate, cyclotomicDiscriminant, Rat.cast_div, Rat.cast_natCast,
      div_mul_eq_mul_div]

/-- Certificate −1 proves the required strict negativity. -/
theorem cyclotomicDiscriminant_neg_of_certificate (t : Triangle) (k : ℕ)
    (h : t.discriminantSignCertificate k = -1) : t.cyclotomicDiscriminant k < 0 := by
  have hp := t.discriminantSignCertificate_pos k (by omega)
  rw [h] at hp
  simpa using hp

/-- Certificate +1 proves strict positivity, useful for forbidden embeddings. -/
theorem cyclotomicDiscriminant_pos_of_certificate (t : Triangle) (k : ℕ)
    (h : t.discriminantSignCertificate k = 1) : 0 < t.cyclotomicDiscriminant k := by
  have hp := t.discriminantSignCertificate_pos k (by omega)
  rw [h] at hp
  simpa using hp

/-- A finite family of rational sign certificates proves full arithmeticity.
Exhaustiveness and the identity test come from CyclotomicEmbeddings. -/
theorem arithmeticHyperbolic_of_sign_certificates (t : Triangle) (h : t.Admissible)
    (hhyp : t.Hyperbolic)
    (hcert : ∀ k : Fin (2 * t.commonDenominator),
      (k : ℕ).Coprime (2 * t.commonDenominator) → ¬t.FixesCosines k →
      t.discriminantSignCertificate k = -1) : t.ArithmeticHyperbolic := by
  apply (t.arithmeticHyperbolic_iff_cyclotomic h).mpr
  exact ⟨hhyp, fun k hk hfix => t.cyclotomicDiscriminant_neg_of_certificate k (hcert k hk hfix)⟩

/-- A single coprime, nonidentity index with certificate +1 excludes a triple.
The index need not be reduced modulo 2N for this one-witness argument. -/
theorem not_arithmeticHyperbolic_of_sign_certificate (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2 * t.commonDenominator)) (hfix : ¬t.FixesCosines k)
    (hcert : t.discriminantSignCertificate k = 1) : ¬t.ArithmeticHyperbolic := by
  intro ha
  have hneg := ha.2.2 (t.cyclotomicRealEmbedding h k hk)
    (fun he => hfix ((t.cyclotomicRealEmbedding_eq_inclusion_iff h k hk).mp he))
  rw [t.discriminantAt_cyclotomic h k hk] at hneg
  exact (not_lt_of_gt (t.cyclotomicDiscriminant_pos_of_certificate k hcert)) hneg

end Triangle
end ArithmeticTriangles
