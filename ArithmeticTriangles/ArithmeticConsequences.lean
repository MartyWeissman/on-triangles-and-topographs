module

public import ArithmeticTriangles.Bounds
public import ArithmeticTriangles.CosineField

/-!
# Immediate consequences of arithmetic hyperbolicity

The geometric sign theorem is now connected to the existing field-theoretic
definition. In particular, a nonidentity embedding fixing `D` is forbidden,
even if it acts nontrivially on other field elements. This is the obstruction
used repeatedly in PDF §§2.4 and 3.1.

The real trace bound is proved in `RealTrace.lean`; the special embeddings
and structural inequality of Lemma 2.2 are in `Structural.lean`. This file uses only
`ArithmeticHyperbolic` and the geometric theorems already proved.
-/

@[expose] public section

namespace ArithmeticTriangles.Triangle

/-- An arithmetic hyperbolic triple has positive distinguished discriminant. -/
theorem ArithmeticHyperbolic.discriminant_pos {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) : 0 < triangle.discriminant :=
  (triangle.discriminant_pos_iff_hyperbolic h.admissible).mpr h.hyperbolic

/-- The distinguished value lies in `(0,16)`. The corresponding trace bound is in `RealTrace.lean`. -/
theorem ArithmeticHyperbolic.discriminant_mem_Ioo {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) : triangle.discriminant ∈ Set.Ioo 0 16 :=
  ⟨h.discriminant_pos, triangle.discriminant_lt_sixteen h.admissible⟩

/-- Under admissibility, the definition can equivalently be stated using
positive distinguished `D` and negative `D` at every other embedding. -/
theorem arithmeticHyperbolic_iff_discriminant_signs (triangle : Triangle)
    (hadm : triangle.Admissible) :
    triangle.ArithmeticHyperbolic ↔
      0 < triangle.discriminant ∧
        ∀ embedding : triangle.cosineField →ₐ[ℚ] ℝ,
          embedding ≠ triangle.cosineField.val → triangle.discriminantAt embedding < 0 := by
  constructor
  · intro h
    exact ⟨h.discriminant_pos, h.2.2⟩
  · intro h
    exact ⟨hadm, (triangle.discriminant_pos_iff_hyperbolic hadm).mp h.1, h.2⟩

/-- A single nonnegative value at a nonidentity embedding rules out arithmeticity.
This formulation includes zero, which is also forbidden by the strict sign rule. -/
theorem not_arithmeticHyperbolic_of_nonnegative_embedding (triangle : Triangle)
    (embedding : triangle.cosineField →ₐ[ℚ] ℝ)
    (hne : embedding ≠ triangle.cosineField.val)
    (hnonneg : 0 ≤ triangle.discriminantAt embedding) :
    ¬ triangle.ArithmeticHyperbolic := by
  intro h
  exact (not_lt_of_ge hnonneg) (h.2.2 embedding hne)

/-- In a qualifying triple, an embedding with nonnegative `D` must be the
distinguished inclusion. This is often how the paper identifies an embedding. -/
theorem ArithmeticHyperbolic.embedding_eq_inclusion_of_nonneg {triangle : Triangle}
    (h : triangle.ArithmeticHyperbolic) (embedding : triangle.cosineField →ₐ[ℚ] ℝ)
    (hnonneg : 0 ≤ triangle.discriminantAt embedding) :
    embedding = triangle.cosineField.val := by
  by_contra hne
  exact triangle.not_arithmeticHyperbolic_of_nonnegative_embedding embedding hne hnonneg h

/-- In particular, fixing the distinguished value of `D` forces identity on
the whole cosine field. We do not identify embeddings merely by distinct
values of `D`: the conclusion is proved from the arithmetic sign condition. -/
theorem ArithmeticHyperbolic.embedding_eq_inclusion_of_fixes_discriminant
    {triangle : Triangle} (h : triangle.ArithmeticHyperbolic)
    (embedding : triangle.cosineField →ₐ[ℚ] ℝ)
    (hfix : embedding triangle.fieldDiscriminant = triangle.discriminant) :
    embedding = triangle.cosineField.val := by
  apply h.embedding_eq_inclusion_of_nonneg embedding
  rw [discriminantAt_eq_embedding, hfix]
  exact h.discriminant_pos.le

end ArithmeticTriangles.Triangle
