module

public import ArithmeticTriangles.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Trigonometric foundations (PDF, §2.1)

The paper's discriminants are polynomials in `2 cos A`, `2 cos B`, `2 cos C`.
We first factor them for arbitrary real angles. Only the subsequent sign
theorems require geometric hypotheses. This separation is important: the
identities will also apply to conjugate angles, which need not be acute.

The two-factor versions below are convenient for sign comparisons, while
the four-factor versions are exactly the product identities in (2.2).
-/

@[expose] public section

namespace ArithmeticTriangles

/-- An intermediate form of the cosine factorization in PDF (2.2). -/
theorem discriminant_cos_factor (A B C : ℝ) :
    discriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) =
      4 * (Real.cos C + Real.cos (A + B)) *
        (Real.cos C + Real.cos (A - B)) := by
  have hA := Real.sin_sq_add_cos_sq A
  have hB := Real.sin_sq_add_cos_sq B
  have hAB : Real.sin A ^ 2 * Real.sin B ^ 2 =
      (1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2) := by
    rw [show Real.sin A ^ 2 = 1 - Real.cos A ^ 2 by linarith,
      show Real.sin B ^ 2 = 1 - Real.cos B ^ 2 by linarith]
  rw [Real.cos_add, Real.cos_sub]
  unfold discriminant
  nlinarith [hAB]

/-- The corresponding two-factor expression for the companion `E`. -/
theorem companionDiscriminant_cos_factor (A B C : ℝ) :
    companionDiscriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) =
      4 * (Real.cos C - Real.cos (A + B)) *
        (Real.cos C - Real.cos (A - B)) := by
  have hA := Real.sin_sq_add_cos_sq A
  have hB := Real.sin_sq_add_cos_sq B
  have hAB : Real.sin A ^ 2 * Real.sin B ^ 2 =
      (1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2) := by
    rw [show Real.sin A ^ 2 = 1 - Real.cos A ^ 2 by linarith,
      show Real.sin B ^ 2 = 1 - Real.cos B ^ 2 by linarith]
  rw [Real.cos_add, Real.cos_sub]
  unfold companionDiscriminant
  nlinarith [hAB]

/-- PDF (2.2), the four cosine factors of `D`, for arbitrary real angles. -/
theorem discriminant_cos_product (A B C : ℝ) :
    discriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) =
      16 * Real.cos ((A + B + C) / 2) * Real.cos ((A + B - C) / 2) *
        Real.cos ((A - B + C) / 2) * Real.cos ((-A + B + C) / 2) := by
  rw [discriminant_cos_factor, Real.cos_add_cos, Real.cos_add_cos]
  have h₁ : (C + (A + B)) / 2 = (A + B + C) / 2 := by ring
  have h₂ : (C - (A + B)) / 2 = -((A + B - C) / 2) := by ring
  have h₃ : (C + (A - B)) / 2 = (A - B + C) / 2 := by ring
  have h₄ : (C - (A - B)) / 2 = (-A + B + C) / 2 := by ring
  rw [h₁, h₂, h₃, h₄, Real.cos_neg]
  ring

/-- PDF (2.2), the four sine factors of `E`, including its minus sign. -/
theorem companionDiscriminant_sin_product (A B C : ℝ) :
    companionDiscriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) =
      -16 * Real.sin ((A + B + C) / 2) * Real.sin ((A + B - C) / 2) *
        Real.sin ((A - B + C) / 2) * Real.sin ((-A + B + C) / 2) := by
  rw [companionDiscriminant_cos_factor, Real.cos_sub_cos, Real.cos_sub_cos]
  have h₁ : (C + (A + B)) / 2 = (A + B + C) / 2 := by ring
  have h₂ : (C - (A + B)) / 2 = -((A + B - C) / 2) := by ring
  have h₃ : (C + (A - B)) / 2 = (A - B + C) / 2 := by ring
  have h₄ : (C - (A - B)) / 2 = (-A + B + C) / 2 := by ring
  rw [h₁, h₂, h₃, h₄, Real.sin_neg]
  ring

/-- For positive, non-obtuse angles, `D > 0` exactly when their sum is below π.

The second factor is positive. For the first, compare `cos C` with
`cos (π - (A + B))`, using that cosine is strictly decreasing on `[0, π]`.
This avoids dividing by a trigonometric expression whose sign is unknown. -/
theorem discriminant_pos_iff_angle_sum_lt_pi (A B C : ℝ)
    (hA : 0 < A) (hA' : A ≤ Real.pi / 2)
    (hB : 0 < B) (hB' : B ≤ Real.pi / 2)
    (hC : 0 < C) (hC' : C ≤ Real.pi / 2) :
    0 < discriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) ↔
      A + B + C < Real.pi := by
  have hfactor : 0 < Real.cos C + Real.cos (A - B) := by
    have hcosC := Real.cos_nonneg_of_mem_Icc
      (show C ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith)
    have hcosAB := Real.cos_pos_of_mem_Ioo
      (show A - B ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith)
    linarith
  have hcompare : Real.cos (Real.pi - (A + B)) < Real.cos C ↔
      C < Real.pi - (A + B) :=
    Real.strictAntiOn_cos.lt_iff_gt
      (show Real.pi - (A + B) ∈ Set.Icc 0 Real.pi by constructor <;> linarith)
      (show C ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
  rw [Real.cos_pi_sub] at hcompare
  rw [discriminant_cos_factor, mul_pos_iff_of_pos_right hfactor,
    mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)]
  constructor
  · intro h
    have := hcompare.mp (by linarith)
    linarith
  · intro h
    have := hcompare.mpr (by linarith)
    linarith

/-- The geometric part of PDF Lemma 2.2: `E < 0` means `A < B + C`.

This theorem does not assert that qualifying triples have `E < 0`; that
requires the arithmetic embedding argument, which is a separate milestone. -/
theorem companionDiscriminant_neg_iff_angle_lt (A B C : ℝ)
    (hA : A ≤ Real.pi / 2) (hB : 0 < B) (hBA : B ≤ A)
    (hC : 0 ≤ C) (hCB : C ≤ B) :
    companionDiscriminant (2 * Real.cos A) (2 * Real.cos B) (2 * Real.cos C) < 0 ↔
      A < B + C := by
  have hfactor : 0 < 4 * (Real.cos C - Real.cos (A + B)) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hC
      (show A + B ≤ Real.pi by linarith) (show C < A + B by linarith)
    linarith
  have hcompare : Real.cos C < Real.cos (A - B) ↔ A - B < C :=
    Real.strictAntiOn_cos.lt_iff_gt
      (show C ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
      (show A - B ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
  rw [companionDiscriminant_cos_factor]
  simp only [mul_neg_iff, not_lt_of_ge hfactor.le, hfactor, false_and, true_and, or_false]
  constructor
  · intro h
    have := hcompare.mp (by linarith)
    linarith
  · intro h
    have := hcompare.mpr (by linarith)
    linarith

end ArithmeticTriangles
