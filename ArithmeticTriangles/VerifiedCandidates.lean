module

public import ArithmeticTriangles.ExactSigns
public import ArithmeticTriangles.CandidateList

/-!
# Every listed candidate is arithmetic

For each of the 25 triples, check every index k modulo 2N. Coprime indices
failing the identity test have discriminant sign certificate −1. The exact
sign theorem and exhaustive embedding criterion turn these finite rational
calculations into proofs of full arithmetic hyperbolicity.

This proves the sufficiency direction of the classification. It does not
assert that every arithmetic triple lies in the list.
-/

@[expose] public section

namespace ArithmeticTriangles

set_option maxRecDepth 8192 in
/-- Every nonidentity cyclotomic embedding of every listed candidate has
negative discriminant. The computation is reduction in Lean's kernel. -/
theorem expectedArithmeticTriples_sign_certificates (t : Triangle)
    (ht : t ∈ expectedArithmeticTriples) :
    ∀ k : Fin (2 * t.commonDenominator),
      (k : ℕ).Coprime (2 * t.commonDenominator) → ¬t.FixesCosines k →
      t.discriminantSignCertificate k = -1 := by
  unfold expectedArithmeticTriples at ht
  fin_cases ht <;> decide +kernel

/-- All 25 proposed triples satisfy the full arithmetic condition, including
the strict sign requirement at every nonidentity real embedding. -/
theorem expectedArithmeticTriples_arithmeticHyperbolic (t : Triangle)
    (ht : t ∈ expectedArithmeticTriples) : t.ArithmeticHyperbolic :=
  t.arithmeticHyperbolic_of_sign_certificates
    (expectedArithmeticTriples_admissible t ht)
    (expectedArithmeticTriples_hyperbolic t ht)
    (expectedArithmeticTriples_sign_certificates t ht)

end ArithmeticTriangles
