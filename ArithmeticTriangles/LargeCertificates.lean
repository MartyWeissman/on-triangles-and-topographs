module

public import ArithmeticTriangles.SmallDegreeTable
public import ArithmeticTriangles.IntegerSigns

/-!
# Checking the large finite box

This module isolates the computational part from the mathematical reduction.
Boolean list loops avoid the cost of reducing nested proof-dependent finite
quantifiers. `large_degree_checks` is checked by the kernel, and
`large_degree_sign_certificates` proves precisely what that Boolean result means.
The short witness list is only a search aid: every returned index is checked.
-/

@[expose] public section
namespace ArithmeticTriangles

/-- A small search list, ordered to try the most frequently useful indices first. -/
def largeWitnessIndices : List ℕ := [5,7,11,3,13,17,23,19,29,37,31,41,59,25,53]

/-- Check all three requirements for a forbidden cyclotomic embedding. -/
def integerWitnessCheck (e f g k : ℕ) : Bool :=
  decide (k.Coprime (2 * (⟨e,f,g⟩ : Triangle).commonDenominator)) &&
    !decide ((⟨e,f,g⟩ : Triangle).FixesCosines k) &&
    decide ((⟨e,f,g⟩ : Triangle).integerDiscriminantSignCertificate k = 1)

/-- The two diagonal survivors or a forbidden embedding, for every eligible
triple at a given degree. Ordering and the structural inequality are retained. -/
def largeDegreeCheck (d : ℕ) : Bool :=
  (degreeCandidates d).all fun e =>
  (degreeCandidates d).all fun f =>
  (degreeCandidates d).all fun g =>
    if e ≤ f ∧ f ≤ g ∧ f*g < e*(f+g) then
      decide (e = f ∧ f = g ∧ (e = 12 ∨ e = 15)) ||
        largeWitnessIndices.any (integerWitnessCheck e f g)
    else true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Exact kernel verification of the entire finite box, including every degree. -/
theorem large_degree_checks : (List.range 64).all largeDegreeCheck = true := by
  decide +kernel

/-- Translate the checked Boolean computation back into mathematical witnesses.
No computational oracle is assumed: the preceding theorem supplies the check. -/
theorem large_degree_sign_certificates :
    ∀ d : Fin 64, 0 < (d : ℕ) →
    ∀ e ∈ degreeCandidates d,
    ∀ f ∈ degreeCandidates d, e ≤ f →
    ∀ g ∈ degreeCandidates d, f ≤ g → f * g < e * (f + g) →
      (e = f ∧ f = g ∧ (e = 12 ∨ e = 15)) ∨
      ∃ k : Fin 60,
        (k : ℕ).Coprime (2 * (⟨e, f, g⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, f, g⟩ : Triangle).FixesCosines k ∧
        (⟨e, f, g⟩ : Triangle).integerDiscriminantSignCertificate k = 1 := by
  intro d _hd e he f hf hef g hg hfg hstruct
  have hd := List.all_eq_true.mp large_degree_checks d (List.mem_range.mpr d.isLt)
  simp only [largeDegreeCheck, List.all_eq_true] at hd
  have ht := hd e he f hf g hg
  rw [ite_eq_left ⟨hef, hfg, hstruct⟩] at ht
  rcases Bool.or_eq_true_iff.mp ht with hdiag | hw
  · exact Or.inl (of_decide_eq_true hdiag)
  · obtain ⟨k, hk, hc⟩ := List.any_eq_true.mp hw
    have hbound : ∀ k ∈ largeWitnessIndices, k < 60 := by decide +kernel
    refine Or.inr ⟨⟨k, hbound k hk⟩, ?_⟩
    simpa only [integerWitnessCheck, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, and_assoc] using hc

end ArithmeticTriangles
