# Mathematical statement and formal representation

The project classifies ordered integer triples using embeddings of the full
cosine field. The exact definitions below are the specification checked by Lean.
The project title is broader than the current formalized scope: topographs are
not yet part of the library.

## Objects and definitions

A `Triangle` is a structure with three natural numbers `e`, `f`, and `g`.
`Triangle.Admissible` means \(2\le e\le f\le g\). Natural numbers are
sufficient for the intended integer statement because admissibility imposes
a positive lower bound. Arbitrary structures need not be admissible.

For an admissible triple set
\(a=2\cos(\pi/e)\), \(b=2\cos(\pi/f)\), and \(c=2\cos(\pi/g)\).
The library constructs the subfield \(F=\mathbb Q(a,b,c)\subset\mathbb R\)
as an intermediate field. It defines the element
\(D=a^2+b^2+c^2+abc-4\in F\) and its images under rational-algebra embeddings.
The distinguished embedding is the inclusion of this subfield into the reals.

The predicate `ArithmeticHyperbolic` asserts admissibility,
\(1/e+1/f+1/g<1\), and strict negativity of \(\sigma(D)\) for every
embedding other than that inclusion. The library proves that hyperbolicity
is equivalent to positivity of \(D\) at the inclusion, under admissibility.

| Mathematical item | Formal location |
|---|---|
| Triples, ordering, hyperbolicity, discriminant | [Basic.lean](../ArithmeticTriangles/Basic.lean) |
| Full cosine field and arithmetic predicate | [CosineField.lean](../ArithmeticTriangles/CosineField.lean) |
| Hyperbolicity and the sign of D | [Geometry.lean](../ArithmeticTriangles/Geometry.lean) |
| Explicit set of 25 triples | [CandidateList.lean](../ArithmeticTriangles/CandidateList.lean) |
| Verification of the listed triples | [VerifiedCandidates.lean](../ArithmeticTriangles/VerifiedCandidates.lean) |
| Necessity and equivalence | [Classification.lean](../ArithmeticTriangles/Classification.lean) |

## What is classified

The complete list is displayed in the [README](../README.md). In Lean,
`expectedArithmeticTriples_card` proves its cardinality is 25,
`expectedArithmeticTriples_arithmeticHyperbolic` proves sufficiency, and
`classification_complete` proves necessity. The theorem
`arithmeticHyperbolic_iff_mem` combines the two directions.

The words “arithmetic hyperbolic” refer to this project's predicate. In
particular, the embedding condition is on the full field \(F\), not a
replacement by \(\mathbb Q(D)\) or an invariant trace field. Distinct
embeddings can have the same image of \(D\); they are still distinct
embeddings for purposes of this definition. The resulting list is a subset of
Takeuchi’s Theorem 3; see [References](References.md). This literature comparison
is documented here, not formalized as a theorem about triangle groups in Lean.

## Outline of the proof

1. Trigonometric product identities give exact sign criteria and structural
   inequalities. Cyclotomic automorphisms produce the relevant real embeddings.
2. Small-unit arguments classify the right and diagonal families and constrain
   the isosceles and scalene branches. Each listed candidate is verified.
3. For first denominator at least 11, a seven-term root-pair expansion gives a
   normalized discriminant trace at least 1/4. The sign condition gives total
   trace less than 16, so the full cosine-field degree is at most 63.
4. Each individual cosine degree divides this degree. Totient estimates and a
   proved finite table bound each denominator by 231. Exact, kernel-checked
   certificates exclude all survivors except the diagonal triples at 12 and 15.
5. A related trace bound handles the remaining small initial pairs. Earlier
   structural restrictions bound the remaining scalene cases. These branches
   exhaust all ordered triples.

The [proof guide](ProofGuide.md) supplies details, including why the finite
checks are proofs of unbounded classification after the mathematical bounds
are established. The [module guide](Modules.md) maps the supporting results.

This is an alternative formal proof of the classification in the supplied
working manuscript. It does not formalize every intermediate assertion of
that manuscript. It does not establish priority, novelty, or the correctness
of any broader interpretation not expressed in the Lean definitions.
