module

public import ArithmeticTriangles.ExactSigns
public import ArithmeticTriangles.Structural

/-!
# Excluding scalene triples with smallest denominator 3, 4, 5, or 6

The structural bounds already proved give f<2e and g<e(e+1). For 3≤e≤6
this is a finite box. At each strictly ordered triple in that box, an index
k<20 is coprime to 2N, fails the identity test, and gives positive D.

Lean checks the witnesses by exact rational sign certificates. Thus these
four smallest-denominator cases are excluded without a full degree formula,
a product-trace formula, or decimal approximations to conjugates.
-/

@[expose] public section

namespace ArithmeticTriangles

set_option maxRecDepth 16384 in
/-- An exhaustive bounded witness check, covering 298 strictly ordered triples.
The implications discard indices outside the structural bounds. The existential
search uses only k<20; every witness is checked for coprimality, nonidentity,
and a positive discriminant certificate in Lean's kernel. -/
theorem small_scalene_sign_certificates :
    ∀ e : Fin 7, 3 ≤ (e : ℕ) →
    ∀ f : Fin 12, (e : ℕ) < f → (f : ℕ) < 2 * e →
    ∀ g : Fin 42, (f : ℕ) < g → (g : ℕ) < e * ((e : ℕ) + 1) →
      ∃ k : Fin 20,
        (k : ℕ).Coprime (2 * (⟨e, f, g⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, f, g⟩ : Triangle).FixesCosines k ∧
        (⟨e, f, g⟩ : Triangle).discriminantSignCertificate k = 1 := by
  decide +kernel

namespace Triangle

/-- The bounded computation proves an unbounded theorem in f and g because
the structural inequality first forces every qualifying triple into the box. -/
theorem not_arithmeticHyperbolic_of_scalene_first_three_to_six (t : Triangle)
    (hs : t.Scalene) (he3 : 3 ≤ t.e) (he6 : t.e ≤ 6) : ¬t.ArithmeticHyperbolic := by
  intro h
  have horder := (t.strictly_ordered_iff_scalene h.admissible).mpr hs
  have hf := h.middle_lt_twice_first (by omega)
  have hg := h.last_lt_first_mul_succ (by omega) hs
  have heBound : t.e < 7 := by omega
  have hfBound : t.f < 12 := by omega
  have hgBound : t.g < 42 := by nlinarith
  obtain ⟨k, hk, hfix, hcert⟩ := small_scalene_sign_certificates
    ⟨t.e, heBound⟩ he3 ⟨t.f, hfBound⟩ horder.1 hf ⟨t.g, hgBound⟩ horder.2 hg
  exact t.not_arithmeticHyperbolic_of_sign_certificate h.admissible k hk hfix hcert h

/-- A non-right scalene arithmetic triple must now start at e≥7.
No conductor-parity hypothesis is required. -/
theorem ArithmeticHyperbolic.seven_le_first_of_scalene {t : Triangle}
    (h : t.ArithmeticHyperbolic) (hs : t.Scalene) (he : 2 < t.e) : 7 ≤ t.e := by
  by_contra hsmall
  exact t.not_arithmeticHyperbolic_of_scalene_first_three_to_six hs (by omega) (by omega) h

/-- Under arithmeticity, every triple with 3≤e≤6 is isosceles. -/
theorem ArithmeticHyperbolic.isosceles_of_first_three_to_six {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he3 : 3 ≤ t.e) (he6 : t.e ≤ 6) : t.Isosceles := by
  by_contra hnot
  have hs : t.Scalene := by
    unfold Isosceles at hnot
    unfold Scalene
    tauto
  exact t.not_arithmeticHyperbolic_of_scalene_first_three_to_six hs he3 he6 h

end Triangle
end ArithmeticTriangles
