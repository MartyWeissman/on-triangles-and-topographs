module

public import ArithmeticTriangles.RootTraceBounds
public import ArithmeticTriangles.CosineDegree

/-!
# A uniform degree bound when the smallest denominator is at least eleven

All seven root pairs in the discriminant have angles between 0 and 2π/7.
Their normalized traces are at least −1/4 each, so τ≥1/4. The established
bound Tr(D)<16 then gives [F:ℚ]≤63 and bounds every denominator by 231.
This argument does not distinguish parity or equality of denominators.
-/

@[expose] public section
namespace ArithmeticTriangles

/-- The nth cosine inside the ambient field is the root pair indexed by N/n. -/
theorem cyclotomic_cosine_eq_rootPair (N : ℕ) [NeZero N] (n : ℕ) (hdvd : n ∣ N)
    (x : cosineCyclotomicField N) (hx : (x : ℂ) = (cosineGenerator n : ℂ)) :
    x = rootPair (cyclotomicRoot N) (N / n : ℕ) := by
  obtain ⟨m, rfl⟩ := hdvd
  have hn : n ≠ 0 := by have := NeZero.ne (n * m); aesop
  have hm : m ≠ 0 := by have := NeZero.ne (n * m); aesop
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  apply Subtype.ext
  simp only [rootPair, zpow_natCast, zpow_neg]
  change (x : ℂ) = cosineRoot (n * m) ^ m + (cosineRoot (n * m) ^ m)⁻¹
  rw [cosineRoot_pow_mul n m hn hm, hx, cosineGenerator_eq_root_add_inv]

namespace Triangle

/-- Clear the structural inequality after multiplying by N: the three
positive conductor quotients satisfy u<v+w. -/
theorem ArithmeticHyperbolic.conductor_quotient_triangle {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 2 < t.e) :
    t.commonDenominator / t.e < t.commonDenominator / t.f + t.commonDenominator / t.g := by
  let N := t.commonDenominator
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (t.commonDenominator_ne_zero h.admissible)
  have hq : ∀ n : ℕ, n ∣ N → ((N / n : ℕ) : ℝ) = (N : ℝ) / n := by
    intro n hd
    have hn : n ≠ 0 := by intro hz; subst n; simp at hd; exact (ne_of_gt hN) (by exact_mod_cast hd)
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hn)).mpr
    exact_mod_cast Nat.div_mul_cancel hd
  have hh := mul_lt_mul_of_pos_left (h.structural he) hN
  change (N : ℝ) * (1 / t.e) < (N : ℝ) * (1 / t.f + 1 / t.g) at hh
  simp only [mul_add, mul_one_div] at hh
  rw [← hq t.e (Nat.dvd_lcm_left _ _),
    ← hq t.f ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)),
    ← hq t.g ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))] at hh
  exact_mod_cast hh

/-- All seven root-pair indices lie strictly between 0 and 2N/7. -/
theorem ArithmeticHyperbolic.large_root_indices {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 11 ≤ t.e) :
    let u : ℤ := (t.commonDenominator / t.e : ℕ)
    let v : ℤ := (t.commonDenominator / t.f : ℕ)
    let w : ℤ := (t.commonDenominator / t.g : ℕ)
    ∀ q ∈ ([2*u, 2*v, 2*w, u+v+w, u+v-w, u-v+w, -u+v+w] : List ℤ),
      0 < q ∧ 7 * q < 2 * t.commonDenominator := by
  let N := t.commonDenominator
  have hNz : N ≠ 0 := t.commonDenominator_ne_zero h.admissible
  have heD : t.e ∣ N := Nat.dvd_lcm_left _ _
  have hfD : t.f ∣ N := (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
  have hgD : t.g ∣ N := (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
  have hb : ∀ n : ℕ, 11 ≤ n → n ∣ N → 0 < N / n ∧ 11 * (N / n) ≤ N := by
    intro n hn hd
    have hm := Nat.div_mul_cancel hd
    have hpos : 0 < N / n := by
      apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hNz) hd) (by omega)
    constructor
    · exact hpos
    · nlinarith
  have hau := hb t.e he heD
  have hbv := hb t.f (by have := h.admissible.2.1; omega) hfD
  have hcw := hb t.g (by have := h.admissible.2.1; have := h.admissible.2.2; omega) hgD
  have huv : N / t.f ≤ N / t.e := Nat.div_le_div_left h.admissible.2.1 (by omega)
  have hvw : N / t.g ≤ N / t.f := Nat.div_le_div_left h.admissible.2.2 (by have := h.admissible.2.1; omega)
  have htri := h.conductor_quotient_triangle (by omega)
  dsimp [N] at hau hbv hcw huv hvw
  dsimp
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> omega

/-- A uniform normalized discriminant trace bound for all e≥11. -/
theorem ArithmeticHyperbolic.normalizedTrace_ge_quarter_of_first_ge_eleven {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 11 ≤ t.e) :
    (1 : ℚ) / 4 ≤ t.normalizedDiscriminantTrace := by
  let N := t.commonDenominator
  let : NeZero N := ⟨t.commonDenominator_ne_zero h.admissible⟩
  let K := cosineCyclotomicField N
  let ζ := cyclotomicRoot N
  let φ := t.toCyclotomic h.admissible
  let u : ℤ := (N / t.e : ℕ)
  let v : ℤ := (N / t.f : ℕ)
  let w : ℤ := (N / t.g : ℕ)
  have ha : φ t.firstGenerator = rootPair ζ u :=
    cyclotomic_cosine_eq_rootPair N t.e (Nat.dvd_lcm_left _ _) _ rfl
  have hb : φ t.secondGenerator = rootPair ζ v :=
    cyclotomic_cosine_eq_rootPair N t.f
      ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hc : φ t.thirdGenerator = rootPair ζ w :=
    cyclotomic_cosine_eq_rootPair N t.g
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)) _ rfl
  have hζ := cyclotomicRoot_primitive N
  have hz : ζ ≠ 0 := hζ.ne_zero (by have := NeZero.pos N; omega)
  have hD : φ t.fieldDiscriminant =
      2 + rootPair ζ (2*u) + rootPair ζ (2*v) + rootPair ζ (2*w) +
        rootPair ζ (u+v+w) + rootPair ζ (u+v-w) + rootPair ζ (u-v+w) + rootPair ζ (-u+v+w) := by
    have hm : φ t.fieldDiscriminant = ArithmeticTriangles.discriminant (φ t.firstGenerator)
        (φ t.secondGenerator) (φ t.thirdGenerator) := by
      simp [fieldDiscriminant, ArithmeticTriangles.discriminant, map_ofNat]
    rw [hm, ha, hb, hc, discriminant_rootPairs ζ hz]
  have hbound : ∀ q ∈ ([2*u, 2*v, 2*w, u+v+w, u+v-w, u-v+w, -u+v+w] : List ℤ),
      -(1 : ℚ) / 4 ≤ Algebra.normalizedTrace ℚ K (rootPair ζ q) := by
    intro q hq
    have hi := h.large_root_indices he q hq
    apply normalizedTrace_rootPair_ge_neg_quarter (2*N) (by have := NeZero.pos N; omega) ζ hζ q hi.1
    exact_mod_cast hi.2
  have htwo : Algebra.normalizedTrace ℚ K (2 : K) = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ K (2 : ℚ)
  have heq : t.normalizedDiscriminantTrace = Algebra.normalizedTrace ℚ K (φ t.fieldDiscriminant) := by
    rw [Algebra.normalizedTrace_map, Algebra.normalizedTrace_eq_of_finiteDimensional_apply]
    simp [normalizedDiscriminantTrace, discriminantTrace, fieldTrace, deg, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, hD]
  simp only [map_add, htwo]
  have h1 := hbound (2*u) (by simp)
  have h2 := hbound (2*v) (by simp)
  have h3 := hbound (2*w) (by simp)
  have h4 := hbound (u+v+w) (by simp)
  have h5 := hbound (u+v-w) (by simp)
  have h6 := hbound (u-v+w) (by simp)
  have h7 := hbound (-u+v+w) (by simp)
  linarith

/-- The positive trace lower bound forces the full degree below 64. -/
theorem ArithmeticHyperbolic.deg_le_sixty_three_of_first_ge_eleven {t : Triangle}
    (h : t.ArithmeticHyperbolic) (he : 11 ≤ t.e) : t.deg ≤ 63 := by
  have hl := h.normalizedTrace_ge_quarter_of_first_ge_eleven he
  have hd : (0 : ℚ) < t.deg := by exact_mod_cast t.deg_pos
  rw [normalizedDiscriminantTrace, le_div_iff₀ hd] at hl
  have ht : t.discriminantTrace < 16 := by exact_mod_cast h.trace_lt_sixteen
  have : (t.deg : ℚ) < 64 := by linarith
  have : t.deg < 64 := by exact_mod_cast this
  omega

end Triangle
end ArithmeticTriangles
