# Provenance, contributions, and AI assistance

## Author and scope

The author named for this project is **Martin H. Weissman**, University of
California, Santa Cruz, [ORCID 0000-0003-2078-1185](https://orcid.org/0000-0003-2078-1185).
These details were supplied by the author. The title is *On Triangles and
Topographs*. This release contains the cosine-triple classification and
teaching material; its title does not imply that topographs have been formalized.

## Mathematical starting material

The development began from a privately supplied 13-page working manuscript
entitled *Hyperbolic cosine triples with a single hyperbolic embedding*, together
with Lean work from an earlier AI-assisted session. The supplied PDF has SHA-256:

```
7c8ddaf7349173d74c34d9dfe85859623e140928a4c672f4fc58646b8ca99aca
```

As confirmed by Martin H. Weissman, the PDF manuscript was itself developed
with extensive use of **OpenAI Codex (GPT-6 Astra)** under his direction. The
PDF has no byline or date; this development attribution comes from his account.
It is identified here as a working development source rather than a published
reference. The manuscript and exploratory files are retained
in the private development archive and are not distributed in this package.
The formal statement, proofs, and mathematical reading guides are included,
so the PDF is not needed to build or inspect the result.

The final completeness proof uses uniform trace bounds and exact finite
certificates. It does not follow every argument of the working manuscript;
in particular, a general three-generator degree formula and its relative-degree
and conductor arguments are not claimed as formalized here.

The historical classification of arithmetic triangle groups is due to Takeuchi
(1977); the present list is a subset. See [References](References.md).

## AI assistance and human involvement

OpenAI Codex was used extensively, under Martin H. Weissman's direction, to
port and write Lean code, search the installed mathlib source, develop proof
strategies, debug proofs, run checks, and draft documentation and lessons.
The author supplied the problem and starting materials, directed the scope,
and discussed the mathematics and formalization interactively. This account
does not assert that every generated line has received independent human review.

GPT-6 Astra is specifically identified above for development of the starting
PDF. The complete earlier conversation history and model identifiers for every
stage of the later formalization are not available in this publication package.
No complete prompt log or exhaustive model-by-model attribution is claimed. AI systems are disclosed as tools, not
listed as human authors. The documentation, including this statement, was
prepared with AI assistance and remains subject to author review.

## Proof checking and its limits

Lean checks proof terms against the formal definitions. The selected audit
includes the final classification and its transitive dependencies and reports
only `propext`, `Classical.choice`, and `Quot.sound`. Exact finite certificates
are evaluated in the kernel using `decide +kernel`; their validity does not
rely on an external numerical search being trustworthy.

These checks do not establish that the definitions capture every intended
informal interpretation, that the result is new, that the prose contains no
errors, or that the software and hardware are infallible. No independent
mathematical review, external peer review, or separately implemented proof
checker is claimed. The [verification record](../verification/README.md)
describes what was actually run.

## Dependency credit and release history

This work relies on [Lean](https://github.com/leanprover/lean4) and
[mathlib](https://github.com/leanprover-community/mathlib4), including their
algebra, number theory, real analysis, and tactic infrastructure. The dependency
lock identifies the exact versions; dependencies retain their own licenses
and authorship and are not bundled into the source release.

The initial public package is a curated snapshot, not the complete development
history. Its Lean source and dependency configuration are copied unchanged
from private development commit `9a05fd6b5872d9865e38a9c94bb305e24c3453e6`.
That identifier records provenance; it is not a promised publicly accessible
commit. The earlier repository remains preserved separately. The public
package excludes the private manuscripts, local paths, exploratory scripts,
session notes, downloaded toolchains, dependencies, and generated build files.
