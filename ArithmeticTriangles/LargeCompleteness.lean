module

public import ArithmeticTriangles.LargeTrace
public import ArithmeticTriangles.LargeCertificates
public import ArithmeticTriangles.VerifiedCandidates
public import ArithmeticTriangles.IntegerSigns

@[expose] public section
namespace ArithmeticTriangles

namespace Triangle

/-- All three denominators are bounded, including repeated-entry cases. -/
theorem ArithmeticHyperbolic.denominators_le_231_of_first_ge_eleven {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 11 ≤ t.e) : t.e ≤ 231 ∧ t.f ≤ 231 ∧ t.g ≤ 231 := by
  have hd := h.deg_le_sixty_three_of_first_ge_eleven he
  have ht := t.denominator_totients_le_twice_degree h.admissible
  exact ⟨denominator_le_231_of_totient_le_126 t.e (by omega),
    denominator_le_231_of_totient_le_126 t.f (by omega),
    denominator_le_231_of_totient_le_126 t.g (by omega)⟩

/-- Completeness for all triples with first denominator at least eleven. -/
theorem ArithmeticHyperbolic.mem_expected_of_first_ge_eleven {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 11 ≤ t.e) : t ∈ expectedArithmeticTriples := by
  have hd := h.deg_le_sixty_three_of_first_ge_eleven he
  obtain ⟨heB, hfB, hgB⟩ := h.denominators_le_231_of_first_ge_eleven he
  have heD := t.cosine_degree_dvd t.e h.admissible.1 t.firstGenerator.property
  have hfD := t.cosine_degree_dvd t.f (h.admissible.1.trans h.admissible.2.1) t.secondGenerator.property
  have hgD := t.cosine_degree_dvd t.g (h.admissible.1.trans (h.admissible.2.1.trans h.admissible.2.2)) t.thirdGenerator.property
  rw [← smallCosineDegree_eq t.e (by omega)] at heD
  rw [← smallCosineDegree_eq t.f (by omega)] at hfD
  rw [← smallCosineDegree_eq t.g (by omega)] at hgD
  have hs := (t.structural_iff_product_lt h.admissible).mp (h.structural (by omega))
  have heC : t.e ∈ degreeCandidates t.deg := by
    rw [degreeCandidates_check ⟨t.deg, by omega⟩ t.deg_pos]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, he, heD⟩
  have hfC : t.f ∈ degreeCandidates t.deg := by
    rw [degreeCandidates_check ⟨t.deg, by omega⟩ t.deg_pos]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, by have := h.admissible.2.1; omega, hfD⟩
  have hgC : t.g ∈ degreeCandidates t.deg := by
    rw [degreeCandidates_check ⟨t.deg, by omega⟩ t.deg_pos]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, by have := h.admissible.2.1; have := h.admissible.2.2; omega, hgD⟩
  rcases large_degree_sign_certificates ⟨t.deg, by omega⟩ t.deg_pos
      t.e heC t.f hfC h.admissible.2.1 t.g hgC h.admissible.2.2 hs with hm | ⟨k, hk, hfix, hcert⟩
  · rcases t with ⟨e, f, g⟩
    change e = f ∧ f = g ∧ (e = 12 ∨ e = 15) at hm
    rcases hm with ⟨rfl, rfl, rfl | rfl⟩ <;> decide
  · exact False.elim (t.not_arithmeticHyperbolic_of_integer_sign_certificate h.admissible k hk hfix hcert h)

end Triangle
end ArithmeticTriangles
