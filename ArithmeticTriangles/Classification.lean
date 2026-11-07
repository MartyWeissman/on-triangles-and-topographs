module

public import ArithmeticTriangles.CosineField
public import ArithmeticTriangles.VerifiedCandidates
public import ArithmeticTriangles.RepeatedCompleteness
public import ArithmeticTriangles.SmallScalene
public import ArithmeticTriangles.IsoscelesField
public import ArithmeticTriangles.LargeCompleteness
public import ArithmeticTriangles.SmallPairCompleteness
public import ArithmeticTriangles.MiddleScalene

@[expose] public section

namespace ArithmeticTriangles

/-- The classification proposition. Its proof is `classification` below. -/
def ClassificationStatement : Prop :=
  ∀ triangle : Triangle,
    triangle.ArithmeticHyperbolic ↔ triangle ∈ expectedArithmeticTriples

/-- Candidate verification reduces classification to the necessity direction. -/
theorem classificationStatement_iff_completeness :
    ClassificationStatement ↔ ∀ t : Triangle, t.ArithmeticHyperbolic → t ∈ expectedArithmeticTriples := by
  constructor
  · intro h t ht
    exact (h t).mp ht
  · intro h t
    exact ⟨h t, expectedArithmeticTriples_arithmeticHyperbolic t⟩

/-- The reduction used before the final trace argument. All three branches
are now discharged by `classification_complete`; the equivalence is retained
to document how the earlier milestones assemble. -/
theorem classificationStatement_iff_remaining_cases :
    ClassificationStatement ↔
      (∀ t : Triangle, t.ArithmeticHyperbolic → 5 ≤ t.e → t.e ≠ 6 →
        t.e = t.f → t.f < t.g → t ∈ expectedArithmeticTriples) ∧
      (∀ t : Triangle, t.ArithmeticHyperbolic → 16 ≤ t.e → t.e < t.f → t.f = t.g →
        t ∈ expectedArithmeticTriples) ∧
      (∀ t : Triangle, t.ArithmeticHyperbolic → 7 ≤ t.e → t.Scalene →
        t ∈ expectedArithmeticTriples) := by
  rw [classificationStatement_iff_completeness]
  constructor
  · intro h
    exact ⟨fun t ht _ _ _ _ => h t ht, fun t ht _ _ _ => h t ht,
      fun t ht _ _ => h t ht⟩
  · rintro ⟨hfirst, hlast, hscalene⟩ t ht
    rcases t.classification_cases ht.admissible with hr | ⟨he, hcases⟩
    · exact ht.mem_expected_of_right hr
    rcases hcases with hdiag | ⟨hef, hfg⟩ | ⟨hef, hfg⟩ | ⟨hef, hfg⟩
    · exact ht.mem_expected_of_equilateral hdiag
    · by_cases he3 : t.e = 3
      · exact ht.mem_expected_of_initial_three_pair he3 (by omega)
      · have hnot := ht.not_four_or_six_of_isosceles_first hef hfg
        exact hfirst t ht (by omega) hnot.2 hef hfg
    · by_cases he15 : t.e ≤ 15
      · exact ht.mem_expected_of_isosceles_last_small he hef hfg he15
      · exact hlast t ht (by omega) hef hfg
    · have hs := (t.strictly_ordered_iff_scalene ht.admissible).mp ⟨hef, hfg⟩
      exact hscalene t ht (ht.seven_le_first_of_scalene hs he) hs

/-- Completeness: every arithmetic hyperbolic triple is one of the 25 candidates.
The large trace bound handles every e≥11 uniformly. Below eleven, the earlier
family classifications and structural finite checks exhaust all possibilities. -/
theorem classification_complete (t : Triangle) (h : t.ArithmeticHyperbolic) :
    t ∈ expectedArithmeticTriples := by
  by_cases he11 : 11 ≤ t.e
  · exact h.mem_expected_of_first_ge_eleven he11
  rcases t.classification_cases h.admissible with hr | ⟨he, hcases⟩
  · exact h.mem_expected_of_right hr
  rcases hcases with hdiag | ⟨hef, hfg⟩ | ⟨hef, hfg⟩ | ⟨hef, hfg⟩
  · exact h.mem_expected_of_equilateral hdiag
  · by_cases he3 : t.e = 3
    · exact h.mem_expected_of_initial_three_pair he3 (by omega)
    · exact h.mem_expected_of_small_initial_pair (by omega) (by omega) hef
  · exact h.mem_expected_of_isosceles_last_small he hef hfg (by omega)
  · have hs := (t.strictly_ordered_iff_scalene h.admissible).mp ⟨hef, hfg⟩
    have he7 := h.seven_le_first_of_scalene hs he
    exact False.elim (t.not_arithmeticHyperbolic_of_scalene_first_seven_to_ten hs he7 (by omega) h)

/-- The full classification, proved in both directions for arbitrary triples. -/
theorem classification : ClassificationStatement :=
  classificationStatement_iff_completeness.mpr classification_complete

/-- A convenient rewriting form of the classification theorem. -/
theorem arithmeticHyperbolic_iff_mem (t : Triangle) :
    t.ArithmeticHyperbolic ↔ t ∈ expectedArithmeticTriples := classification t

/-- The full initial-pair classification, including the diagonal and the
exceptional (3,3,n) family. There are no denominator bounds in the hypotheses. -/
theorem initial_pair_arithmetic_iff (e g : ℕ) :
    (⟨e,e,g⟩ : Triangle).ArithmeticHyperbolic ↔
      (e = 3 ∧ g ∈ repeatedDenominators) ∨
      (e = g ∧ e ∈ repeatedDenominators) ∨ (e = 5 ∧ (g = 10 ∨ g = 15)) := by
  rw [arithmeticHyperbolic_iff_mem]
  constructor
  · intro hm
    simp only [expectedArithmeticTriples, Finset.mem_insert, Finset.mem_singleton,
      Triangle.mk.injEq] at hm
    repeat' (rcases hm with hm | hm)
    all_goals rename_i hrest
    all_goals rcases hrest with ⟨hfirst, hlast⟩
    all_goals simp_all [repeatedDenominators]
  · rintro (⟨rfl, hg⟩ | ⟨rfl, he⟩ | ⟨rfl, rfl | rfl⟩)
    · unfold repeatedDenominators at hg
      fin_cases hg <;> decide
    · unfold repeatedDenominators at he
      fin_cases he <;> decide
    · decide
    · decide

/-- The full final-pair classification, including right and diagonal triples. -/
theorem final_pair_arithmetic_iff (e f : ℕ) :
    (⟨e,f,f⟩ : Triangle).ArithmeticHyperbolic ↔
      (e = 2 ∧ (f = 5 ∨ f = 7)) ∨ ((e = 3 ∨ e = 4) ∧ f = 5) ∨
      (e = f ∧ e ∈ repeatedDenominators) := by
  rw [arithmeticHyperbolic_iff_mem]
  constructor
  · intro hm
    simp only [expectedArithmeticTriples, Finset.mem_insert, Finset.mem_singleton,
      Triangle.mk.injEq] at hm
    repeat' (rcases hm with hm | hm)
    all_goals rename_i hrest
    all_goals rcases hrest with ⟨hfirst, hlast⟩
    all_goals simp_all [repeatedDenominators]
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl⟩ | ⟨rfl, he⟩)
    all_goals try decide
    unfold repeatedDenominators at he
    fin_cases he <;> decide

namespace Triangle

/-- Every non-right arithmetic hyperbolic triple is isosceles. -/
theorem ArithmeticHyperbolic.isosceles_of_not_right {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) : t.Isosceles := by
  have hc := expectedArithmeticTriples_right_or_isosceles t (classification_complete t h)
  rcases hc with hr | hi
  · unfold Right at hr
    omega
  · exact hi

/-- In particular, all non-right scalene triples are excluded, without any
upper bound or parity restriction on their denominators. -/
theorem not_arithmeticHyperbolic_of_scalene (t : Triangle) (hs : t.Scalene) (he : 2 < t.e) :
    ¬t.ArithmeticHyperbolic := by
  intro h
  have hi := h.isosceles_of_not_right he
  unfold Isosceles at hi
  unfold Scalene at hs
  tauto

end Triangle
end ArithmeticTriangles
