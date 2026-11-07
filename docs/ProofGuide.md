# Completeness proof guide

The classification is now a theorem, in both directions, for arbitrary triples:

```lean
theorem arithmeticHyperbolic_iff_mem (t : Triangle) :
  t.ArithmeticHyperbolic ↔ t ∈ expectedArithmeticTriples
```

The theorem is in [Classification.lean](../ArithmeticTriangles/Classification.lean).
There are no denominator bounds or unproved completeness assumptions in its
statement. Admissibility, hyperbolicity, and the condition on every nonidentity
embedding of the **full cosine field** are all part of `ArithmeticHyperbolic`.

Let S={4,5,6,7,8,9,12,15}. The 25 triples are:

| Family | Survivors |
|---|---|
| Right | (2,3,7), (2,3,9), (2,3,11), (2,5,5), (2,7,7) |
| Initial pair 3 | (3,3,n) for n∈S |
| Diagonal | (n,n,n) for n∈S |
| Other isosceles | (3,5,5), (4,5,5), (5,5,10), (5,5,15) |

In particular, every **non-right** arithmetic hyperbolic triple is isosceles.
The qualification is essential: the first three right triples are scalene.

## A uniform trace argument

Three infinite branches require completeness arguments: general initial pairs,
large final pairs, and scalene triples starting at 7. A uniform lower bound on
the normalized discriminant trace handles **all e≥11**.
It covers repeated denominators, distinct denominators, and both parities
of the common denominator.

The bound is deliberately weak. It leaves a larger finite check, but the
mathematical proof is short and uses trace machinery already established.

Write N=lcm(e,f,g), ζ=exp(πi/N), and

\[
u=N/e,\qquad v=N/f,\qquad w=N/g,\qquad R(q)=\zeta^q+\zeta^{-q}.
\]

Then a=R(u), b=R(v), c=R(w). Multiplication of root pairs gives
R(i)R(j)=R(i+j)+R(i−j), so the discriminant expands as

\[
D=2+R(2u)+R(2v)+R(2w)
 +R(u+v+w)+R(u+v-w)+R(u-v+w)+R(-u+v+w).
\]

This identity is `discriminant_rootPairs` in
[RootTraceBounds.lean](../ArithmeticTriangles/RootTraceBounds.lean).

Ordering gives u≥v≥w>0. The already proved structural inequality gives
u<v+w. Thus all seven indices q are positive. If e≥11, then u,v,w≤N/11,
so q≤3N/11<2N/7. Consequently the order

\[
m=\frac{2N}{\gcd(2N,q)}
\]

of ζ^q is at least 8. Indeed, gcd(2N,q)≤q, so 2N>7q forces m>7.

The normalized trace of R(q) is 2μ(m)/φ(m). Our earlier Möbius estimate
μ(m)/φ(m)≥−1/8 applies to every m≥8. Each of the seven terms therefore
contributes at least −1/4, giving

\[
\tau=\frac{\operatorname{Tr}(D)}d\ge2-7\cdot\frac14=\frac14.
\]

Normalized traces agree when passing to the ambient cyclotomic field; that
compatibility is why we can compute with ζ even when the full cosine field
is smaller. No formula for its exact degree is needed.

Since Tr(D)<16, we obtain d<64, hence **d≤63**. These steps are in
[LargeTrace.lean](../ArithmeticTriangles/LargeTrace.lean).

## From degree to a finite box

For each denominator n=e,f,g, the degree φ(2n)/2 of its individual cosine
field divides d. In particular φ(2n)≤126.

[TotientBounds.lean](../ArithmeticTriangles/TotientBounds.lean) proves the
elementary estimate n≤2φ(n)². For odd n the factor 2 is unnecessary: prove
the estimate for prime powers, then multiply over coprime factors. The
prime 2 accounts for the sole extra factor. Applied to 2n, the estimate gives
n≤φ(2n)²≤126²=15876.

[FiniteTotients.lean](../ArithmeticTriangles/FiniteTotients.lean) checks this
finite interval using Euler's product formula and sharpens the bound to
**n≤231**. The product implementation `fastTotient` is proved equal to
mathlib's totient, so this is a theorem about the original function.

The final search uses more than the numerical box: it retains ordering,
the structural inequality fg<e(f+g), and divisibility φ(2n)/2∣d for a common
d with 1≤d≤63. [LargeCertificates.lean](../ArithmeticTriangles/LargeCertificates.lean)
checks that every surviving triple is one of the two diagonal exceptions or has
a forbidden embedding with index k<60.
[LargeCompleteness.lean](../ArithmeticTriangles/LargeCompleteness.lean) applies
this finite theorem to the arbitrary triple with which we started. The only listed triples in this range are (12,12,12) and
(15,15,15).

## The remaining small initial pairs

For 4≤e=f≤10, the structural inequality alone does not bound g. Suppose
g>210. In the root-pair expansion, the constant and repeated-a terms give

\[
2+4\frac{\mu(e)}{\varphi(e)}\ge1.
\]

This is a check of just seven values of e. The five remaining terms are
R(2w), R(2u+w), R(2u−w), and two copies of R(w).

The first and last terms have orders g and 2g. For either cross term
q=2u±w, gcd(2N,q) divides ew. Using eu=N=gw gives

\[
2g\le e\frac{2N}{\gcd(2N,q)}.
\]

Because g>210 and e≤10, all these orders exceed 42. For every m>42,
μ(m)/φ(m)≥−1/20. To prove this unbounded statement, only the case μ(m)=−1
needs work: if φ(m)<20, the elementary totient estimate bounds m<768,
and an exact check rules out m>42 with both properties.

Each of the five variable terms therefore contributes at least −1/10.
Thus τ≥1−5/10=1/2 and d≤31. Now φ(2g)≤62, and another finite totient check
gives g≤105, contradicting g>210. We have proved **g≤210**, starting with
no upper bound at all. The bounded sign check then finishes the family.

See [SmallPairTrace.lean](../ArithmeticTriangles/SmallPairTrace.lean) and
[SmallPairCompleteness.lean](../ArithmeticTriangles/SmallPairCompleteness.lean).

For scalene triples with 7≤e≤10, the existing structural bounds give
f<2e<21 and g<e(e+1)≤110. The exact check in
[MiddleScalene.lean](../ArithmeticTriangles/MiddleScalene.lean) excludes them.
Together with the family classifications described in the module guide, these
arguments exhaust every case.

## Why the finite checks are proofs

Each exclusion provides an integer k satisfying three conditions:

1. k is coprime to 2N, so it defines a cyclotomic embedding.
2. The embedding does not fix all three cosine generators.
3. Its discriminant is positive, contradicting the arithmetic sign condition.

For efficiency, [IntegerSigns.lean](../ArithmeticTriangles/IntegerSigns.lean)
uses a shared denominator 2P, where P=efg. The four cosine arguments have
integer numerators k(fg+eg+ef), k(fg+eg−ef), k(fg−eg+ef), and
k(−fg+eg+ef). Reducing each numerator modulo 4P gives its cosine sign by
integer comparisons. Periodicity and monotonicity of cosine prove this
procedure sound; the four-factor identity transfers the signs to D.
A zero or otherwise inconclusive sign is never accepted as a strict sign.

[SmallDegreeTable.lean](../ArithmeticTriangles/SmallDegreeTable.lean) packs
232 small degree values into a natural number, with seven bits per entry.
The candidate lists for each degree are cached too and checked against their
defining conditions. The large literal is merely data: Lean checks **every entry** against
φ(2n)/2. Later proofs use that checked equality. External exploration may
suggest bounds, witnesses, or data, but it supplies no trusted mathematical
premises.

The large check uses Boolean `List.all` and `List.any` loops. A separate
proof translates their result into the required universally quantified
statement and explicit witnesses. This avoids the evaluation cost of nested
proof-dependent finite quantifiers. The search tries a short list of indices;
it need not contain every possible index, because a single checked forbidden
embedding suffices for each excluded triple.

All finite checks use `decide +kernel`: evaluation takes place in Lean's
kernel. There is no floating-point evaluation, `native_decide`, extra
mathematical axiom, or proof placeholder.

## How to read and use the final proof

Start at `classification_complete` in Classification.lean. Its case split
is now short:

- e≥11: apply the uniform completeness theorem.
- Right or diagonal: apply the complete family theorem.
- e=f<g below eleven: use the (3,3,g) theorem or the small-pair theorem.
- e<f=g below eleven: use the bounded final-pair theorem.
- Scalene below eleven: previous results force e≥7, and the intermediate
  check gives a contradiction.

This is a good example of proof organization: the final argument names the
mathematical steps, while each step has its own independently checked proof.

`classification_complete` proves necessity. The earlier theorem
`expectedArithmeticTriples_arithmeticHyperbolic` proves sufficiency.
`classification` combines them into a proof of `ClassificationStatement`.
That name was previously only a definition of the desired proposition; it
now has an actual proof.

The unbounded family corollaries `initial_pair_arithmetic_iff` and
`final_pair_arithmetic_iff` follow by simplifying list membership. They
include diagonal cases, and the latter includes right isosceles cases.
Lessons 32–36 in [Learning.lean](../Learning.lean) show how `rw`, `.mp`, and
`exact` let a short new proof reuse the complete argument.

## Scope relative to the PDF

The classification itself is complete. This is an alternative proof of its
remaining branches, not a claim that every intermediate lemma of the PDF
has been formalized in the paper's order. In particular, the general
three-generator degree formula, the general product-trace formula, and the
paper's relative-degree/conductor arguments are not required by the completed
proof. They remain possible future projects in algebraic number theory.

The development milestones and working manuscripts are retained in the private
development archive; this release presents the completed proof. See
[provenance and AI assistance](Provenance.md) for the scope of the archive.

## Verification and line counts

The full library builds successfully, all lessons compile, and the expanded
axiom audit checks **238 declarations**, including the final classification.
Only Lean's standard foundations `propext`, `Classical.choice`, and `Quot.sound`
occur. The finite Boolean theorem `large_degree_checks` itself depends only
on `propext`. The saved report is [axiom report](../verification/axioms.txt).

There are **5,525 library lines** and **6,345 selected Lean lines total**.
Counts include comments and blank lines and exclude mathlib, generated output,
and scratch experiments. See [source statistics](SourceStatistics.md) for the
per-file breakdown and [the verification record](../verification/README.md)
for the environment and scope of the recorded run.
