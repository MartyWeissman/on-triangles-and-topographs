module

public import ArithmeticTriangles.ExactSigns

/-!
# Integer-only sign certificates

The four cosine factors can share denominator 2efg. Reducing their integer
numerators modulo 4efg avoids constructing and reducing rational numbers
inside large finite checks. The proof below establishes soundness directly
from periodicity and the same trigonometric factorization as ExactSigns.
-/

@[expose] public section
namespace ArithmeticTriangles

/-- Center an integer numerator by subtracting a multiple of the period 4P. -/
def centeredNumerator (P q : ℤ) : ℤ := q - 4 * P * ((q + 2 * P) / (4 * P))

/-- Strict sign of cos(qπ/(2P)), checked entirely with integers. -/
def integerCosineSign (P q : ℤ) : ℤ :=
  if |centeredNumerator P q| < P then 1
  else if |centeredNumerator P q| ≤ 2*P ∧ P < |centeredNumerator P q| then -1 else 0

/-- Centering the numerator preserves the cosine by 2π-periodicity. -/
theorem cos_centeredNumerator (P q : ℤ) (hP : 0 < P) :
    Real.cos ((centeredNumerator P q : ℝ) / (2*P) * Real.pi) =
      Real.cos ((q : ℝ) / (2*P) * Real.pi) := by
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  have he : (centeredNumerator P q : ℝ) / (2*P) * Real.pi =
      (q : ℝ) / (2*P) * Real.pi - (((q+2*P)/(4*P) : ℤ) : ℝ) * (2*Real.pi) := by
    unfold centeredNumerator
    push_cast
    field_simp
    ring
  rw [he, Real.cos_sub_int_mul_two_pi]

/-- A nonzero integer sign is a sound strict cosine sign. -/
theorem integerCosineSign_pos (P q : ℤ) (hP : 0 < P) (h : integerCosineSign P q ≠ 0) :
    0 < (integerCosineSign P q : ℝ) * Real.cos ((q : ℝ) / (2*P) * Real.pi) := by
  rw [← cos_centeredNumerator P q hP]
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have habs : Real.cos ((centeredNumerator P q : ℝ) / (2*P) * Real.pi) =
      Real.cos ((|centeredNumerator P q| : ℤ) / (2*P) * Real.pi) := by
    rw [← Real.cos_abs ((centeredNumerator P q : ℝ) / (2*P) * Real.pi),
      abs_mul, abs_div, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2*P), Int.cast_abs]
  rw [habs]
  unfold integerCosineSign at h ⊢
  split_ifs with hpos hneg
  · have hr : ((|centeredNumerator P q| : ℤ) : ℝ) < P := by exact_mod_cast hpos
    have hangle : ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) * Real.pi < Real.pi/2 := by
      have hd : ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) < 1/2 :=
        (div_lt_iff₀ (by positivity)).mpr (by linarith)
      nlinarith [Real.pi_pos]
    have h0 : 0 ≤ ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) * Real.pi := by positivity
    have hc := Real.cos_pos_of_mem_Ioo
      (show ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) * Real.pi ∈
        Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [Real.pi_pos], hangle⟩)
    simpa using hc
  · have hr1 : ((|centeredNumerator P q| : ℤ) : ℝ) ≤ 2*P := by exact_mod_cast hneg.1
    have hr2 : (P : ℝ) < ((|centeredNumerator P q| : ℤ) : ℝ) := by exact_mod_cast hneg.2
    have hd1 : ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    have hd2 : (1 : ℝ)/2 < ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) :=
      (lt_div_iff₀ (by positivity)).mpr (by linarith)
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi/2)
      (show ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) * Real.pi ≤ Real.pi by nlinarith [Real.pi_pos])
      (show Real.pi/2 < ((|centeredNumerator P q| : ℤ) : ℝ) / (2*P) * Real.pi by nlinarith [Real.pi_pos])
    rw [Real.cos_pi_div_two] at hc
    simpa using neg_pos.mpr hc
  · simp only [ite_eq_right hpos, ite_eq_right hneg, ne_eq, not_true_eq_false] at h

/-- Clear the shared denominator in each of the four signed angle sums. -/
theorem shared_cosine_angle (e f g k : ℕ) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (a b c : ℤ) :
    ((k : ℤ) * (a*(f*g) + b*(e*g) + c*(e*f)) : ℤ) / (2*((e*f*g : ℕ) : ℝ)) * Real.pi =
      ((a : ℝ)*((k : ℝ)*Real.pi/e) + (b : ℝ)*((k : ℝ)*Real.pi/f) +
        (c : ℝ)*((k : ℝ)*Real.pi/g))/2 := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  push_cast
  field_simp

namespace Triangle

/-- An integer-only version of the four-factor discriminant certificate. -/
def integerDiscriminantSignCertificate (t : Triangle) (k : ℕ) : ℤ :=
  let P : ℤ := t.e*t.f*t.g
  let A : ℤ := t.f*t.g
  let B : ℤ := t.e*t.g
  let C : ℤ := t.e*t.f
  integerCosineSign P (k*(A+B+C)) * integerCosineSign P (k*(A+B-C)) *
    integerCosineSign P (k*(A-B+C)) * integerCosineSign P (k*(-A+B+C))

/-- The integer certificate has the same required soundness as the rational one. -/
theorem integerDiscriminantSignCertificate_pos (t : Triangle) (h : t.Admissible) (k : ℕ)
    (hc : t.integerDiscriminantSignCertificate k ≠ 0) :
    0 < (t.integerDiscriminantSignCertificate k : ℝ) * t.cyclotomicDiscriminant k := by
  let P : ℤ := t.e*t.f*t.g
  let A : ℤ := t.f*t.g
  let B : ℤ := t.e*t.g
  let C : ℤ := t.e*t.f
  have he0 : 0 < t.e := by have := h.1; omega
  have hf0 : 0 < t.f := by have := h.2.1; omega
  have hg0 : 0 < t.g := by have := h.2.2; omega
  have hP : 0 < P := by dsimp [P]; positivity
  have hn1 : integerCosineSign P (k*(A+B+C)) ≠ 0 := by
    intro hz; simp [integerDiscriminantSignCertificate, P, A, B, C] at hz hc; simp [hz] at hc
  have hn2 : integerCosineSign P (k*(A+B-C)) ≠ 0 := by
    intro hz; simp [integerDiscriminantSignCertificate, P, A, B, C] at hz hc; simp [hz] at hc
  have hn3 : integerCosineSign P (k*(A-B+C)) ≠ 0 := by
    intro hz; simp [integerDiscriminantSignCertificate, P, A, B, C] at hz hc; simp [hz] at hc
  have hn4 : integerCosineSign P (k*(-A+B+C)) ≠ 0 := by
    intro hz; simp [integerDiscriminantSignCertificate, P, A, B, C] at hz hc; simp [hz] at hc
  have hp := mul_pos (mul_pos (mul_pos (integerCosineSign_pos P _ hP hn1)
    (integerCosineSign_pos P _ hP hn2)) (integerCosineSign_pos P _ hP hn3))
    (integerCosineSign_pos P _ hP hn4)
  have he : t.e ≠ 0 := by have := h.1; omega
  have hf : t.f ≠ 0 := by have := h.1; have := h.2.1; omega
  have hg : t.g ≠ 0 := by have := h.1; have := h.2.1; have := h.2.2; omega
  have ha := shared_cosine_angle t.e t.f t.g k he hf hg 1 1 1
  have hb := shared_cosine_angle t.e t.f t.g k he hf hg 1 1 (-1)
  have hd := shared_cosine_angle t.e t.f t.g k he hf hg 1 (-1) 1
  have he' := shared_cosine_angle t.e t.f t.g k he hf hg (-1) 1 1
  simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at ha hb hd he'
  dsimp [P, A, B, C] at hp
  push_cast at ha hb hd he' hp
  simp only [← sub_eq_add_neg] at ha hb hd he'
  rw [ha, hb, hd, he'] at hp
  have hp16 := mul_pos (by norm_num : (0 : ℝ) < 16) hp
  convert hp16 using 1
  unfold integerDiscriminantSignCertificate cyclotomicDiscriminant
  rw [discriminant_cos_product]
  push_cast
  ring

/-- A positive integer certificate at a nonidentity unit excludes arithmeticity. -/
theorem not_arithmeticHyperbolic_of_integer_sign_certificate (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2*t.commonDenominator)) (hfix : ¬t.FixesCosines k)
    (hcert : t.integerDiscriminantSignCertificate k = 1) : ¬t.ArithmeticHyperbolic := by
  intro hh
  have hp := t.integerDiscriminantSignCertificate_pos h k (by omega)
  rw [hcert] at hp
  norm_num at hp
  have hn := hh.2.2 (t.cyclotomicRealEmbedding h k hk)
    (fun he => hfix ((t.cyclotomicRealEmbedding_eq_inclusion_iff h k hk).mp he))
  rw [t.discriminantAt_cyclotomic h k hk] at hn
  linarith

end Triangle
end ArithmeticTriangles
