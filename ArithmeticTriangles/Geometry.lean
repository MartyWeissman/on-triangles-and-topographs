module

public import ArithmeticTriangles.Trigonometry

/-!
# From integer triples to geometric inequalities

This file bridges the definitions in `Basic.lean` and PDF §§2.1–2.4.
The natural-number hypothesis `2 ≤ n` is used explicitly to place `π/n`
in `(0, π/2]`. Lean's real division is defined even at zero, so such
hypotheses must be proved rather than left implicit.

Main results:
* `Triangle.discriminant_pos_iff_hyperbolic`: the sign criterion in §2.1;
* `Triangle.companionDiscriminant_neg_iff_structural`: the geometric part
  of Lemma 2.2, without assuming its still-unproved embedding argument.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The angle belonging to a denominator. It is measured in radians. -/
noncomputable def angle (n : ℕ) : ℝ := Real.pi / (n : ℝ)

theorem angle_pos {n : ℕ} (hn : 0 < n) : 0 < angle n := by
  exact div_pos Real.pi_pos (by exact_mod_cast hn)

theorem angle_le_pi_div_two {n : ℕ} (hn : 2 ≤ n) : angle n ≤ Real.pi / 2 := by
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast hn)

/-- Larger denominators give smaller angles. -/
theorem angle_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) : angle n ≤ angle m := by
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by exact_mod_cast hm)
    (by exact_mod_cast hmn)

/-- The normalized cosine generators lie in `[0,2)`, including zero at `n=2`. -/
theorem cosineGenerator_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ cosineGenerator n := by
  have hpos := angle_pos (show 0 < n by omega)
  have hbound := angle_le_pi_div_two hn
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show angle n ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
  unfold cosineGenerator
  change 0 ≤ 2 * Real.cos (angle n)
  linarith

theorem cosineGenerator_lt_two {n : ℕ} (hn : 2 ≤ n) : cosineGenerator n < 2 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    (show angle n ≤ Real.pi by linarith [angle_le_pi_div_two hn, Real.pi_pos])
    (angle_pos (show 0 < n by omega))
  rw [Real.cos_zero] at h
  change 2 * Real.cos (angle n) < 2
  linarith

/-- The right-angle case is the only possible zero generator among `n ≥ 2`. -/
theorem cosineGenerator_pos {n : ℕ} (hn : 2 < n) : 0 < cosineGenerator n := by
  have hpos := angle_pos (show 0 < n by omega)
  have hbound : angle n < Real.pi / 2 :=
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by exact_mod_cast hn)
  have hcos := Real.cos_pos_of_mem_Ioo
    (show angle n ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
  change 0 < 2 * Real.cos (angle n)
  linarith

@[simp] theorem cosineGenerator_two : cosineGenerator 2 = 0 := by
  simp [cosineGenerator, Real.cos_pi_div_two]

namespace Triangle

/-- Convenient real-valued version of the companion polynomial `E`.
The field-valued version lives in `CosineField.lean`. -/
noncomputable def companionDiscriminant (triangle : Triangle) : ℝ :=
  ArithmeticTriangles.companionDiscriminant (cosineGenerator triangle.e)
    (cosineGenerator triangle.f) (cosineGenerator triangle.g)

/-- The reciprocal inequality (2.8), named independently of arithmeticity.
We will later prove that qualifying triples with `e > 2` satisfy it. -/
def StructuralInequality (triangle : Triangle) : Prop :=
  1 / (triangle.e : ℝ) < 1 / (triangle.f : ℝ) + 1 / (triangle.g : ℝ)

/-- The assertion just after PDF (2.2): positive `D` means hyperbolic angles. -/
theorem discriminant_pos_iff_hyperbolic (triangle : Triangle)
    (hadm : triangle.Admissible) :
    0 < triangle.discriminant ↔ triangle.Hyperbolic := by
  obtain ⟨he, hef, hfg⟩ := hadm
  have hf : 2 ≤ triangle.f := le_trans he hef
  have hg : 2 ≤ triangle.g := le_trans hf hfg
  have h := discriminant_pos_iff_angle_sum_lt_pi
    (angle triangle.e) (angle triangle.f) (angle triangle.g)
    (angle_pos (by omega)) (angle_le_pi_div_two he)
    (angle_pos (by omega)) (angle_le_pi_div_two hf)
    (angle_pos (by omega)) (angle_le_pi_div_two hg)
  change 0 < ArithmeticTriangles.discriminant
    (2 * Real.cos (angle triangle.e)) (2 * Real.cos (angle triangle.f))
    (2 * Real.cos (angle triangle.g)) ↔ triangle.Hyperbolic
  rw [h]
  unfold angle Hyperbolic
  have hscale : Real.pi / (triangle.e : ℝ) + Real.pi / (triangle.f : ℝ) +
      Real.pi / (triangle.g : ℝ) = Real.pi *
      (1 / (triangle.e : ℝ) + 1 / (triangle.f : ℝ) + 1 / (triangle.g : ℝ)) := by ring
  rw [hscale]
  constructor <;> intro hsum <;> nlinarith [Real.pi_pos]

/-- The final geometric step of Lemma 2.2. This is an equivalence for every
admissible triple; arithmeticity is not needed for this step. -/
theorem companionDiscriminant_neg_iff_structural (triangle : Triangle)
    (hadm : triangle.Admissible) :
    triangle.companionDiscriminant < 0 ↔ triangle.StructuralInequality := by
  obtain ⟨he, hef, hfg⟩ := hadm
  have hf : 2 ≤ triangle.f := le_trans he hef
  have hg : 2 ≤ triangle.g := le_trans hf hfg
  have h := companionDiscriminant_neg_iff_angle_lt
    (angle triangle.e) (angle triangle.f) (angle triangle.g)
    (angle_le_pi_div_two he) (angle_pos (by omega))
    (angle_antitone (by omega) hef) (angle_pos (by omega)).le
    (angle_antitone (by omega) hfg)
  change ArithmeticTriangles.companionDiscriminant
    (2 * Real.cos (angle triangle.e)) (2 * Real.cos (angle triangle.f))
    (2 * Real.cos (angle triangle.g)) < 0 ↔ triangle.StructuralInequality
  rw [h]
  unfold angle StructuralInequality
  have heq (n : ℕ) : Real.pi / (n : ℝ) = Real.pi * (1 / (n : ℝ)) := by ring
  simp only [heq]
  constructor <;> intro hsum <;> nlinarith [Real.pi_pos]

end Triangle
end ArithmeticTriangles
