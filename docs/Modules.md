# Module guide

Paths in this table are relative to `ArithmeticTriangles/`. Start with
[the statement](../ArithmeticTriangles/Classification.lean), then follow the
[mathematical overview](Mathematics.md) and [completeness proof](ProofGuide.md).


| File | Contents |
|---|---|
| [Basic.lean](../ArithmeticTriangles/Basic.lean) | Definitions; exhaustion by the geometric cases; equivalence of strict ordering and scaleneness for admissible triples |
| [Identities.lean](../ArithmeticTriangles/Identities.lean) | Six polynomial identities, including the right, isosceles, and equilateral factorizations and the `D E` identity |
| [Trigonometry.lean](../ArithmeticTriangles/Trigonometry.lean) | Both product identities for arbitrary real angles; angle-level sign criteria |
| [Geometry.lean](../ArithmeticTriangles/Geometry.lean) | Angle and generator bounds; `D > 0 ↔ Hyperbolic`; `E < 0 ↔ StructuralInequality` for admissible triples |
| [Bounds.lean](../ArithmeticTriangles/Bounds.lean) | `D < (a+2)² < 16` (as an upper bound for D); conditional bounds on `f,g` and the initial small-denominator ranges |
| [CosineField.lean](../ArithmeticTriangles/CosineField.lean) | Field, generators, degree, trace, and arithmetic definitions; compatibility of the discriminant with embeddings and the inclusion |
| [Algebraic.lean](../ArithmeticTriangles/Algebraic.lean) | Integral cosine generators; finite-dimensional cosine field; positive degree; integer discriminant trace |
| [Embeddings.lean](../ArithmeticTriangles/Embeddings.lean) | Embeddings are determined by their values on the three generators and preserve polynomial equations |
| [TraceEmbeddings.lean](../ArithmeticTriangles/TraceEmbeddings.lean) | The degree counts complex embeddings; the field trace is the sum over them |
| [Cyclotomic.lean](../ArithmeticTriangles/Cyclotomic.lean) | Explicit roots of unity; ambient cyclotomic degree and Galois group; containment of the cosine field |
| [CyclotomicAction.lean](../ArithmeticTriangles/CyclotomicAction.lean) | Coprime power automorphisms; real embeddings and their explicit action on cosine generators |
| [CyclotomicEmbeddings.lean](../ArithmeticTriangles/CyclotomicEmbeddings.lean) | Exhaustiveness of cyclotomic embeddings; identity criterion; finite sign equivalence for arithmeticity |
| [CosineDegree.lean](../ArithmeticTriangles/CosineDegree.lean) | Individual degree φ(2n)/2; divisibility into the full degree; denominator totient bounds |
| [CyclotomicTrace.lean](../ArithmeticTriangles/CyclotomicTrace.lean) | Primitive-root and square-trace evaluations; normalized trace compatibility; even-N trace formula |
| [TraceBounds.lean](../ArithmeticTriangles/TraceBounds.lean) | Möbius-ratio estimates; normalized trace lower bounds and degree consequences |
| [Structural.lean](../ArithmeticTriangles/Structural.lean) | Structural inequality; arithmetic denominator bounds and the e=3,4 scalene ranges |
| [EvenSymmetry.lean](../ArithmeticTriangles/EvenSymmetry.lean) | Even-N automorphism; degree parity; `Tr(abc)=0`; square-trace decomposition; conditional degree bounds |
| [EvenParity.lean](../ArithmeticTriangles/EvenParity.lean) | An odd number of denominator positions have maximal 2-adic valuation |
| [TotalReality.lean](../ArithmeticTriangles/TotalReality.lean) | Chebyshev equations prove total reality; standard number-field instances; real/complex embedding equivalence |
| [RealTrace.lean](../ArithmeticTriangles/RealTrace.lean) | Trace as a real sum; `Tr(D) ≤ D < 16`; strictness for degree > 1; integer bound ≤ 15; sharper `e=4` bound |
| [ArithmeticConsequences.lean](../ArithmeticTriangles/ArithmeticConsequences.lean) | Sign-based reformulation of arithmeticity; a nonidentity embedding fixing `D` is impossible for a qualifying triple |
| [QuadraticCases.lean](../ArithmeticTriangles/QuadraticCases.lean) | Full arithmetic verification of `(3,3,4)`, `(3,3,6)`, `(4,4,4)`, and `(6,6,6)` |
| [CandidateList.lean](../ArithmeticTriangles/CandidateList.lean) | The explicit 25-element list and elementary properties; full arithmeticity is proved in VerifiedCandidates |
| [ExactSigns.lean](../ArithmeticTriangles/ExactSigns.lean) | Sound rational certificates for cosine and discriminant signs; finite verification and single-witness exclusion principles |
| [VerifiedCandidates.lean](../ArithmeticTriangles/VerifiedCandidates.lean) | Full arithmeticity of all 25 listed candidates via exact sign checks |
| [SmallScalene.lean](../ArithmeticTriangles/SmallScalene.lean) | Positive-conjugate witnesses for 298 bounded triples; exclusion of all scalene arithmetic triples with 3≤e≤6 |
| [SmallUnits.lean](../ArithmeticTriangles/SmallUnits.lean) | Unbounded construction of small units; the eight repeated-family denominators |
| [RepeatedCompleteness.lean](../ArithmeticTriangles/RepeatedCompleteness.lean) | Complete classifications of `(n,n,n)` and `(3,3,n)` for all n; membership corollaries |
| [RightCompleteness.lean](../ArithmeticTriangles/RightCompleteness.lean) | Complete classification of right triangles |
| [SmallestConjugate.lean](../ArithmeticTriangles/SmallestConjugate.lean) | Uniform lower bound on squared cosine conjugates |
| [IsoscelesCompleteness.lean](../ArithmeticTriangles/IsoscelesCompleteness.lean) | Rational-square initial pairs and bounded final-pair completeness |
| [IsoscelesField.lean](../ArithmeticTriangles/IsoscelesField.lean) | Isosceles field equality, parity, and embedding constraints |
| [TotientBounds.lean](../ArithmeticTriangles/TotientBounds.lean), [FiniteTotients.lean](../ArithmeticTriangles/FiniteTotients.lean) | Elementary totient estimate and checked denominator bounds |
| [RootTraceBounds.lean](../ArithmeticTriangles/RootTraceBounds.lean), [LargeTrace.lean](../ArithmeticTriangles/LargeTrace.lean) | Seven root-pair expansion and uniform τ≥1/4 for e≥11 |
| [SmallDegreeTable.lean](../ArithmeticTriangles/SmallDegreeTable.lean) | Kernel-checked degree data used to speed up finite searches |
| [IntegerSigns.lean](../ArithmeticTriangles/IntegerSigns.lean) | Integer cosine-sign certificates, with a proof of soundness |
| [LargeCertificates.lean](../ArithmeticTriangles/LargeCertificates.lean) | Exact Boolean check of all degree-compatible triples and proof of its meaning |
| [LargeCompleteness.lean](../ArithmeticTriangles/LargeCompleteness.lean) | Completeness for every triple with e≥11 |
| [SmallPairTrace.lean](../ArithmeticTriangles/SmallPairTrace.lean), [SmallPairCompleteness.lean](../ArithmeticTriangles/SmallPairCompleteness.lean) | Trace reduction and completeness for initial pairs 4≤e≤10 |
| [MiddleScalene.lean](../ArithmeticTriangles/MiddleScalene.lean) | Exclusion of scalene triples with 7≤e≤10 |
| [Classification.lean](../ArithmeticTriangles/Classification.lean) | Full 25-triple classification, both unrestricted isosceles families, and non-right scalene exclusion |

The finite checks use exact proof-producing arithmetic, without floating-point
approximations or `native_decide`.

`ClassificationStatement` defines the proposition; the theorem `classification`
now proves it. `arithmeticHyperbolic_iff_mem` is the convenient rewriting form.

