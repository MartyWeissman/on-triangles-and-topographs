module

public import ArithmeticTriangles.TotientBounds

@[expose] public section
namespace ArithmeticTriangles

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- A sharpened finite consequence of the quadratic totient bound. -/
theorem small_totient_126_check : ∀ a : Fin 63, ∀ b : Fin 256,
    fastTotient (2 * (256 * (a : ℕ) + b)) ≤ 126 → 256 * (a : ℕ) + b ≤ 231 := by
  decide +kernel

/-- A field degree below 64 bounds each cosine denominator by 231. -/
theorem denominator_le_231_of_totient_le_126 (n : ℕ) (h : (2 * n).totient ≤ 126) : n ≤ 231 := by
  have hn := denominator_le_totient_bound_sq n 126 h
  have hb := small_totient_126_check ⟨n / 256, by omega⟩ ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod, fastTotient_eq] using hb
    (by simpa only [Nat.div_add_mod, fastTotient_eq] using h)

end ArithmeticTriangles
