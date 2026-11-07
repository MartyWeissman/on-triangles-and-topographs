module

public import ArithmeticTriangles.SmallScalene
public import ArithmeticTriangles.IntegerSigns

/-!
# The remaining small scalene denominators

The general trace argument starts at eleven. Structural bounds make the
four intermediate cases 7≤e≤10 finite, with f<20 and g<110.
-/

@[expose] public section
namespace ArithmeticTriangles

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Exact forbidden embeddings for the four intermediate scalene cases. -/
theorem middle_scalene_sign_certificates :
    ∀ e : Fin 11, 7 ≤ (e : ℕ) →
    ∀ f : Fin 20, (e : ℕ) < f → (f : ℕ) < 2 * e →
    ∀ g : Fin 110, (f : ℕ) < g → (g : ℕ) < e * ((e : ℕ) + 1) →
      ∃ k : Fin 36,
        (k : ℕ).Coprime (2 * (⟨e, f, g⟩ : Triangle).commonDenominator) ∧
        ¬(⟨e, f, g⟩ : Triangle).FixesCosines k ∧
        (⟨e, f, g⟩ : Triangle).integerDiscriminantSignCertificate k = 1 := by
  decide +kernel

namespace Triangle

/-- No scalene arithmetic triple starts at 7,8,9, or 10, regardless of parity. -/
theorem not_arithmeticHyperbolic_of_scalene_first_seven_to_ten (t : Triangle)
    (hs : t.Scalene) (he7 : 7 ≤ t.e) (he10 : t.e ≤ 10) : ¬t.ArithmeticHyperbolic := by
  intro h
  have ho := (t.strictly_ordered_iff_scalene h.admissible).mpr hs
  have hf := h.middle_lt_twice_first (by omega)
  have hg := h.last_lt_first_mul_succ (by omega) hs
  have hfB : t.f < 20 := by omega
  have hgB : t.g < 110 := by nlinarith
  obtain ⟨k, hk, hfix, hcert⟩ := middle_scalene_sign_certificates
    ⟨t.e, by omega⟩ he7 ⟨t.f, hfB⟩ ho.1 hf ⟨t.g, hgB⟩ ho.2 hg
  exact t.not_arithmeticHyperbolic_of_integer_sign_certificate h.admissible k hk hfix hcert h

end Triangle
end ArithmeticTriangles
