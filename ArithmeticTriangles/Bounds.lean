module

public import ArithmeticTriangles.Geometry

/-!
# Elementary bounds used in the classification

This file formalizes the real upper bound in PDF (2.5) and the denominator
bounds in (2.9). The latter are conditional on `StructuralInequality`.
`Structural.lean` now derives this hypothesis from arithmetic hyperbolicity
when e>2, and supplies corresponding arithmetic corollaries.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The algebraic estimate in (2.5), before substituting cosine generators.
Subtracting `D` from `(a+2)²` gives `(4-b²)+(4-c²)+a(4-bc)`. -/
theorem discriminant_lt_square_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : b < 2) (hc : 0 ≤ c) (hc' : c < 2) :
    discriminant a b c < (a + 2) ^ 2 := by
  have hb2 : b ^ 2 < 4 := by nlinarith
  have hc2 : c ^ 2 < 4 := by nlinarith
  have hbc : b * c < 4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - b) hc]
  have hprod : 0 ≤ a * (4 - b * c) := mul_nonneg ha (by linarith)
  unfold discriminant
  nlinarith

namespace Triangle

/-- The first strict upper bound for the distinguished value, PDF (2.5).
No assertion about the field trace is made here. -/
theorem discriminant_lt_generator_bound (triangle : Triangle) (hadm : triangle.Admissible) :
    triangle.discriminant < (cosineGenerator triangle.e + 2) ^ 2 := by
  obtain ⟨he, hef, hfg⟩ := hadm
  exact discriminant_lt_square_bound (cosineGenerator_nonneg he)
    (cosineGenerator_nonneg (le_trans he hef))
    (cosineGenerator_lt_two (le_trans he hef))
    (cosineGenerator_nonneg (le_trans (le_trans he hef) hfg))
    (cosineGenerator_lt_two (le_trans (le_trans he hef) hfg))

/-- Every admissible triangle has distinguished discriminant strictly below 16. -/
theorem discriminant_lt_sixteen (triangle : Triangle) (hadm : triangle.Admissible) :
    triangle.discriminant < 16 := by
  have h := triangle.discriminant_lt_generator_bound hadm
  have hlow := cosineGenerator_nonneg hadm.1
  have hupp := cosineGenerator_lt_two hadm.1
  nlinarith

/-- Clear positive denominators in (2.8), obtaining an exact natural-number
inequality. This bridge lets later finite arguments avoid real division. -/
theorem structural_iff_product_lt (triangle : Triangle) (hadm : triangle.Admissible) :
    triangle.StructuralInequality ↔
      triangle.f * triangle.g < triangle.e * (triangle.f + triangle.g) := by
  obtain ⟨he, hef, hfg⟩ := hadm
  have he' : (0 : ℝ) < triangle.e := by exact_mod_cast (show 0 < triangle.e by omega)
  have hf' : (0 : ℝ) < triangle.f := by exact_mod_cast (show 0 < triangle.f by omega)
  have hg' : (0 : ℝ) < triangle.g := by exact_mod_cast (show 0 < triangle.g by omega)
  have hsum : 1 / (triangle.f : ℝ) + 1 / (triangle.g : ℝ) =
      ((triangle.f : ℝ) + triangle.g) / ((triangle.f : ℝ) * triangle.g) := by
    field_simp
    ring
  unfold StructuralInequality
  rw [hsum, div_lt_div_iff₀ he' (mul_pos hf' hg')]
  norm_num only [one_mul]
  constructor <;> intro h
  · exact_mod_cast (show (triangle.f : ℝ) * triangle.g <
      (triangle.e : ℝ) * (triangle.f + triangle.g) by nlinarith [h])
  · have h' : (triangle.f : ℝ) * triangle.g <
        (triangle.e : ℝ) * (triangle.f + triangle.g) := by exact_mod_cast h
    nlinarith

/-- First denominator bound in (2.9). In fact scaleneness is not needed. -/
theorem middle_lt_twice_first (triangle : Triangle) (hadm : triangle.Admissible)
    (hstruct : triangle.StructuralInequality) : triangle.f < 2 * triangle.e := by
  have hprod := (triangle.structural_iff_product_lt hadm).mp hstruct
  obtain ⟨he, hef, hfg⟩ := hadm
  by_contra h
  have hfe : 2 * triangle.e ≤ triangle.f := by omega
  have h₁ := Nat.mul_le_mul_right triangle.g hfe
  have h₂ := Nat.mul_le_mul_left triangle.e hfg
  nlinarith

/-- The integral bound `g < e(e+1)` in (2.9).

If `f ≥ e+1`, then `(e+1)g ≤ fg < e(f+g)` gives `g < ef`.
To get the bound independent of `f`, combine the original inequality with
`(f-e-1)(g-e) ≥ 0`, expressed below without truncated subtraction. -/
theorem last_lt_first_mul_succ (triangle : Triangle) (hadm : triangle.Admissible)
    (hscalene : triangle.Scalene) (hstruct : triangle.StructuralInequality) :
    triangle.g < triangle.e * (triangle.e + 1) := by
  have hprod := (triangle.structural_iff_product_lt hadm).mp hstruct
  have hstrict := (triangle.strictly_ordered_iff_scalene hadm).mpr hscalene
  obtain ⟨he, hef, hfg⟩ := hadm
  have he1f : triangle.e + 1 ≤ triangle.f := by omega
  have heg : triangle.e ≤ triangle.g := by omega
  -- Work over the integers so subtraction behaves as in the paper.
  have hfe : (0 : ℤ) ≤ (triangle.f : ℤ) - triangle.e - 1 := by omega
  have hge : (0 : ℤ) ≤ (triangle.g : ℤ) - triangle.e := by omega
  have hnonneg := mul_nonneg hfe hge
  have hp : (triangle.f : ℤ) * triangle.g <
      (triangle.e : ℤ) * (triangle.f + triangle.g) := by exact_mod_cast hprod
  have hbound : (triangle.g : ℤ) < (triangle.e : ℤ) * (triangle.e + 1) := by
    nlinarith
  exact_mod_cast hbound

/-- The more precise real bound `g < ef/(f-e)` from (2.9). -/
theorem last_lt_quotient (triangle : Triangle) (hadm : triangle.Admissible)
    (hscalene : triangle.Scalene) (hstruct : triangle.StructuralInequality) :
    (triangle.g : ℝ) < (triangle.e : ℝ) * triangle.f / (triangle.f - triangle.e) := by
  have hstrict := (triangle.strictly_ordered_iff_scalene hadm).mpr hscalene
  have hfe : (triangle.e : ℝ) < triangle.f := by exact_mod_cast hstrict.1
  rw [lt_div_iff₀ (sub_pos.mpr hfe)]
  have hp : (triangle.f : ℝ) * triangle.g <
      (triangle.e : ℝ) * (triangle.f + triangle.g) := by
    exact_mod_cast (triangle.structural_iff_product_lt hadm).mp hstruct
  nlinarith

/-- Section 5.1: before embedding exclusions, exactly these two ranges remain
when the smallest denominator is three. They contain nine triples in total. -/
theorem scalene_first_three_ranges (triangle : Triangle) (hadm : triangle.Admissible)
    (hscalene : triangle.Scalene) (hstruct : triangle.StructuralInequality)
    (he : triangle.e = 3) :
    (triangle.f = 4 ∧ 5 ≤ triangle.g ∧ triangle.g ≤ 11) ∨
      (triangle.f = 5 ∧ 6 ≤ triangle.g ∧ triangle.g ≤ 7) := by
  have hstrict := (triangle.strictly_ordered_iff_scalene hadm).mpr hscalene
  have hf := triangle.middle_lt_twice_first hadm hstruct
  have hg := triangle.last_lt_first_mul_succ hadm hscalene hstruct
  have hp := (triangle.structural_iff_product_lt hadm).mp hstruct
  rw [he] at hstrict hf hg hp
  have hcases : triangle.f = 4 ∨ triangle.f = 5 := by omega
  rcases hcases with hfour | hfive
  · left
    exact ⟨hfour, by omega, by omega⟩
  · right
    rw [hfive] at hp
    exact ⟨hfive, by omega, by omega⟩

/-- The initial ranges in the middle column of the table in Section 5.2.
The degree restriction in its right column is not yet formalized. -/
theorem scalene_first_four_ranges (triangle : Triangle) (hadm : triangle.Admissible)
    (hscalene : triangle.Scalene) (hstruct : triangle.StructuralInequality)
    (he : triangle.e = 4) :
    (triangle.f = 5 ∧ 6 ≤ triangle.g ∧ triangle.g ≤ 19) ∨
      (triangle.f = 6 ∧ 7 ≤ triangle.g ∧ triangle.g ≤ 11) ∨
      (triangle.f = 7 ∧ 8 ≤ triangle.g ∧ triangle.g ≤ 9) := by
  have hstrict := (triangle.strictly_ordered_iff_scalene hadm).mpr hscalene
  have hf := triangle.middle_lt_twice_first hadm hstruct
  have hp := (triangle.structural_iff_product_lt hadm).mp hstruct
  rw [he] at hstrict hf hp
  have hcases : triangle.f = 5 ∨ triangle.f = 6 ∨ triangle.f = 7 := by omega
  rcases hcases with hfive | hsix | hseven
  · rw [hfive] at hp
    exact Or.inl ⟨hfive, by omega, by omega⟩
  · rw [hsix] at hp
    exact Or.inr (Or.inl ⟨hsix, by omega, by omega⟩)
  · rw [hseven] at hp
    exact Or.inr (Or.inr ⟨hseven, by omega, by omega⟩)

end Triangle
end ArithmeticTriangles
