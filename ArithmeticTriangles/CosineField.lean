module

public import ArithmeticTriangles.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

namespace ArithmeticTriangles
namespace Triangle

/-- The full cosine field `ℚ(2 cos(π/e), 2 cos(π/f), 2 cos(π/g))`,
viewed inside `ℝ` with its distinguished inclusion. -/
noncomputable def cosineField (triangle : Triangle) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ
    ({cosineGenerator triangle.e, cosineGenerator triangle.f,
      cosineGenerator triangle.g} : Set ℝ)

noncomputable def firstGenerator (triangle : Triangle) : triangle.cosineField :=
  ⟨cosineGenerator triangle.e, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

noncomputable def secondGenerator (triangle : Triangle) : triangle.cosineField :=
  ⟨cosineGenerator triangle.f, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

noncomputable def thirdGenerator (triangle : Triangle) : triangle.cosineField :=
  ⟨cosineGenerator triangle.g, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

/-- Field degree. Finiteness is proved separately in `Algebraic.lean`, keeping
the basic definitions independent of that proof. -/
noncomputable def deg (triangle : Triangle) : ℕ :=
  Module.finrank ℚ triangle.cosineField

/-- `D`, as an element of the full cosine field. -/
noncomputable def fieldDiscriminant (triangle : Triangle) : triangle.cosineField :=
  ArithmeticTriangles.discriminant triangle.firstGenerator
    triangle.secondGenerator triangle.thirdGenerator

/-- `E`, as an element of the full cosine field. -/
noncomputable def fieldCompanionDiscriminant (triangle : Triangle) : triangle.cosineField :=
  ArithmeticTriangles.companionDiscriminant triangle.firstGenerator
    triangle.secondGenerator triangle.thirdGenerator

/-- The trace from the full cosine field to `ℚ`. Its expression as a sum over
complex embeddings is proved in `TraceEmbeddings.lean` using finite dimensionality. -/
noncomputable def fieldTrace (triangle : Triangle) (value : triangle.cosineField) : ℚ :=
  Algebra.trace ℚ triangle.cosineField value

noncomputable def discriminantTrace (triangle : Triangle) : ℚ :=
  triangle.fieldTrace triangle.fieldDiscriminant

noncomputable def discriminantAt (triangle : Triangle)
    (embedding : triangle.cosineField →ₐ[ℚ] ℝ) : ℝ :=
  ArithmeticTriangles.discriminant (embedding triangle.firstGenerator)
    (embedding triangle.secondGenerator) (embedding triangle.thirdGenerator)

theorem discriminantAt_eq_embedding (triangle : Triangle)
    (embedding : triangle.cosineField →ₐ[ℚ] ℝ) :
    triangle.discriminantAt embedding = embedding triangle.fieldDiscriminant := by
  simp [discriminantAt, fieldDiscriminant, ArithmeticTriangles.discriminant, map_ofNat]

@[simp] theorem discriminantAt_inclusion (triangle : Triangle) :
    triangle.discriminantAt triangle.cosineField.val = triangle.discriminant := rfl

/-- Arithmetic hyperbolicity is defined using embeddings of the *full* cosine
field. Nonidentity means distinct from its distinguished inclusion into `ℝ`;
it does not mean merely that the value of the discriminant changes. -/
def ArithmeticHyperbolic (triangle : Triangle) : Prop :=
  triangle.Admissible ∧ triangle.Hyperbolic ∧
    ∀ embedding : triangle.cosineField →ₐ[ℚ] ℝ,
      embedding ≠ triangle.cosineField.val → triangle.discriminantAt embedding < 0

theorem ArithmeticHyperbolic.admissible {triangle : Triangle}
    (arithmetic : triangle.ArithmeticHyperbolic) : triangle.Admissible := arithmetic.1

theorem ArithmeticHyperbolic.hyperbolic {triangle : Triangle}
    (arithmetic : triangle.ArithmeticHyperbolic) : triangle.Hyperbolic := arithmetic.2.1

end Triangle
end ArithmeticTriangles
