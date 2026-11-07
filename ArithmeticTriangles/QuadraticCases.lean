module

public import ArithmeticTriangles.Embeddings
public import ArithmeticTriangles.ArithmeticConsequences
public import ArithmeticTriangles.Identities

/-!
# First fully verified arithmetic candidates

For `n = 4, 6`, the cosine generator is respectively `√2, √3`. Every
embedding preserves its square, so it sends the generator to itself or its
negative. Extensionality rules out the positive choice for a nonidentity
embedding. The factorizations from the earlier session then prove `D < 0`.

This verifies both the geometric and arithmetic conditions for four of the
25 candidates: `(3,3,4)`, `(3,3,6)`, `(4,4,4)`, `(6,6,6)`.
These are sufficiency results from PDF §§4.1–4.2, not completeness results.
We do not assume that arbitrary choices of conjugate values give embeddings.
-/

@[expose] public section

namespace ArithmeticTriangles

@[simp] theorem cosineGenerator_three : cosineGenerator 3 = 1 := by
  norm_num [cosineGenerator, Real.cos_pi_div_three]

theorem cosineGenerator_four : cosineGenerator 4 = Real.sqrt 2 := by
  norm_num [cosineGenerator, Real.cos_pi_div_four]
  ring

theorem cosineGenerator_six : cosineGenerator 6 = Real.sqrt 3 := by
  norm_num [cosineGenerator, Real.cos_pi_div_six]
  ring

theorem cosineGenerator_four_sq : cosineGenerator 4 ^ 2 = (2 : ℝ) := by
  rw [cosineGenerator_four, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem cosineGenerator_six_sq : cosineGenerator 6 ^ 2 = (3 : ℝ) := by
  rw [cosineGenerator_six, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- A reusable verification principle for equilateral triples whose
generator has an integer square. Geometry and the square relation are
explicit hypotheses; no list of embeddings is assumed. -/
theorem equilateral_arithmetic_of_square (n k : ℕ)
    (hadm : (⟨n, n, n⟩ : Triangle).Admissible)
    (hhyper : (⟨n, n, n⟩ : Triangle).Hyperbolic)
    (hsquare : cosineGenerator n ^ 2 = (k : ℝ)) :
    (⟨n, n, n⟩ : Triangle).ArithmeticHyperbolic := by
  let triangle : Triangle := ⟨n, n, n⟩
  refine ⟨hadm, hhyper, ?_⟩
  intro σ hne
  have hchoices := triangle.embedding_eq_or_eq_neg_of_square σ triangle.thirdGenerator k hsquare
  rcases hchoices with hfix | hneg
  · -- Fixing this generator fixes all three, hence the entire field.
    exfalso
    apply hne
    exact triangle.embedding_ext σ triangle.cosineField.val hfix hfix hfix
  · -- At the remaining conjugate, D=(-u-1)(2-u)² is strictly negative.
    change discriminant (σ triangle.thirdGenerator) (σ triangle.thirdGenerator)
      (σ triangle.thirdGenerator) < 0
    rw [discriminant_equilateral, hneg]
    have hlow := cosineGenerator_nonneg hadm.1
    have hupp := cosineGenerator_lt_two hadm.1
    change (-cosineGenerator n - 1) * (-cosineGenerator n + 2) ^ 2 < 0
    exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos (by linarith))

/-- The same argument for the initial pair `(3,3)`. Here `a=b=1` and
`D=(c+2)(c-1)`, so the negative conjugate gives `(2-u)(-u-1)<0`. -/
theorem initial_three_pair_arithmetic_of_square (n k : ℕ)
    (hadm : (⟨3, 3, n⟩ : Triangle).Admissible)
    (hhyper : (⟨3, 3, n⟩ : Triangle).Hyperbolic)
    (hsquare : cosineGenerator n ^ 2 = (k : ℝ)) :
    (⟨3, 3, n⟩ : Triangle).ArithmeticHyperbolic := by
  let triangle : Triangle := ⟨3, 3, n⟩
  have ha : triangle.firstGenerator = 1 := by
    apply triangle.cosineField.val.injective
    exact cosineGenerator_three
  have hb : triangle.secondGenerator = 1 := by
    apply triangle.cosineField.val.injective
    exact cosineGenerator_three
  refine ⟨hadm, hhyper, ?_⟩
  intro σ hne
  have hchoices := triangle.embedding_eq_or_eq_neg_of_square σ triangle.thirdGenerator k hsquare
  rcases hchoices with hfix | hneg
  · exfalso
    apply hne
    apply triangle.embedding_ext σ triangle.cosineField.val
    · simp [ha]
    · simp [hb]
    · exact hfix
  · change discriminant (σ triangle.firstGenerator) (σ triangle.secondGenerator)
      (σ triangle.thirdGenerator) < 0
    rw [ha, hb, map_one, discriminant_two_unit_generators, hneg]
    have hn : 2 ≤ n := by have := hadm.2.2; change 3 ≤ n at this; omega
    have hlow := cosineGenerator_nonneg hn
    have hupp := cosineGenerator_lt_two hn
    change (-cosineGenerator n + 2) * (-cosineGenerator n - 1) < 0
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- Full arithmetic verification of the PDF candidate `(3,3,4)`. -/
theorem arithmeticHyperbolic_three_three_four :
    (⟨3, 3, 4⟩ : Triangle).ArithmeticHyperbolic :=
  initial_three_pair_arithmetic_of_square 4 2
    (by norm_num [Triangle.Admissible]) (by norm_num [Triangle.Hyperbolic])
    cosineGenerator_four_sq

/-- Full arithmetic verification of the PDF candidate `(3,3,6)`. -/
theorem arithmeticHyperbolic_three_three_six :
    (⟨3, 3, 6⟩ : Triangle).ArithmeticHyperbolic :=
  initial_three_pair_arithmetic_of_square 6 3
    (by norm_num [Triangle.Admissible]) (by norm_num [Triangle.Hyperbolic])
    cosineGenerator_six_sq

/-- Full arithmetic verification of the PDF candidate `(4,4,4)`. -/
theorem arithmeticHyperbolic_four_four_four :
    (⟨4, 4, 4⟩ : Triangle).ArithmeticHyperbolic :=
  equilateral_arithmetic_of_square 4 2
    (by norm_num [Triangle.Admissible]) (by norm_num [Triangle.Hyperbolic])
    cosineGenerator_four_sq

/-- Full arithmetic verification of the PDF candidate `(6,6,6)`. -/
theorem arithmeticHyperbolic_six_six_six :
    (⟨6, 6, 6⟩ : Triangle).ArithmeticHyperbolic :=
  equilateral_arithmetic_of_square 6 3
    (by norm_num [Triangle.Admissible]) (by norm_num [Triangle.Hyperbolic])
    cosineGenerator_six_sq

end ArithmeticTriangles
