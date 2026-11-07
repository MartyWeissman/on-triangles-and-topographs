# Verification record

Recorded locally on **2026-11-07** for the initial publication candidate.

| Check | Result |
|---|---|
| First-party Lean library | Full rebuild passed; Lake reported 3,415 completed build jobs including dependencies |
| Teaching examples | All 36 lessons in `Learning.lean` compiled |
| Dependency revisions | All nine Git checkouts matched the manifest; no tracked dependency changes |
| Named-declaration audit | All 238 requests returned; only `propext`, `Classical.choice`, and `Quot.sound` occurred |
| Audit-tool regression tests | Seven tests passed, including rejection of truncated reports, extra axioms, placeholders, and omitted required theorems |
| Publication source comparison | All 47 Lean files and the four build/toolchain files match the completed private development snapshot byte for byte |

The environment was macOS on Apple silicon. Lean identified itself as 4.35.0,
`arm64-apple-darwin24.6.0`, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Mathlib was fixed at `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The curated directory began without first-party compiled modules. It reused
existing third-party dependency checkouts and their compiled caches through
a local `.lake/packages` link. Thus this was a fresh build of the project's
Lean source, **not** a fresh internet installation or a rebuild of all mathlib.
The local link, dependencies, build products, and transient logs are excluded
from the source archive.

[axioms.txt](axioms.txt) is the output of `Check.lean` from the curated copy.
The final theorem is included. The audit reports transitive foundational
dependencies of named declarations; these findings are not an external review
of the mathematical specification or a claim that every declaration in mathlib
was individually audited.

The GitHub workflow is configured but has not yet run on GitHub. No independent
peer review or second proof-checker run is claimed. Reproduce the local checks
using [these instructions](../docs/Reproducibility.md).

`SHA256SUMS` at the repository root lists every distributed file except itself.
From the root, `shasum -a 256 -c SHA256SUMS` (macOS) or
`sha256sum -c SHA256SUMS` (Linux) checks the snapshot's file integrity. If you
edit files, the old checksums no longer describe the edited version; regenerate
them for the next reviewed release. Checksums provide integrity information,
not proof correctness or author authentication.
