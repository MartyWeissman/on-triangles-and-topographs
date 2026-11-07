# Reproducing and inspecting the checks

## Environment

The release selects Lean 4.35.0 in `lean-toolchain`. `lake-manifest.json` locks
all nine Git dependencies, including mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
Keep both files unchanged when reproducing this version.

Install Git, Python 3, and [elan](https://github.com/leanprover/elan). The shell
scripts require Bash; on Windows use an appropriate Bash environment such as
WSL. VS Code is optional. Initial dependency downloads require internet access.
Dependency and compiled-cache storage can occupy several GB; the distributed
first-party source is much smaller.

From the repository root:

```sh
./lakew exe cache get
./scripts/verify.sh
```

`lakew` uses an optional project-local `.tools/lean/bin/lake`, then elan when
available, otherwise `lake` on the path. It stores mathlib download caches under
`.tools/`. These local directories are excluded from publication.
Do not run `lake update` to reproduce the release: that command can update
the manifest. A dependency upgrade is a separate change requiring new checks.

## What verification runs

The verification script stops on any failed command and performs:

1. `./lakew build` — compile the first-party library.
2. `python3 scripts/check_dependencies.py` — require each dependency checkout's
   Git revision to match the manifest and its tracked files to be unmodified.
3. `./lakew env lean Learning.lean` — compile all 36 lessons.
4. `./lakew env lean Check.lean` — print foundational dependencies of the
   declarations explicitly listed in that file.
5. `python3 scripts/audit_axioms.py work/axioms-current.txt` — require a complete
   report matching the requested declarations, including the final theorem,
   and reject axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
6. Run the verification-tool regression tests.

Transient logs go in ignored `work/`. The saved [axiom report](../verification/axioms.txt)
is evidence of a recorded run, not a substitute for running the checks yourself.
The audit covers the named declarations and their transitive dependencies;
it is not a claim to enumerate every declaration in mathlib.

The finite certificates use kernel evaluation, with no floating-point sign
oracle or `native_decide`. Downloaded mathlib build caches are standard compiled
dependencies; this workflow does not claim to recompile all of mathlib from
source or independently recheck every cached dependency object.

To force this project's Lean modules to rebuild while retaining dependency
caches, run `./lakew clean` before `./scripts/verify.sh`. The larger certificate
modules can take minutes; subsequent unchanged builds are much faster.

## Automated checks and source inspection

[The GitHub workflow](../.github/workflows/lean.yml) is configured to build and
run verification on pushes and pull requests. Its actual status must be checked
on GitHub after publication; configuring a workflow is not evidence that a
hosted run has succeeded.

[Check.lean](../Check.lean) lists the audited declarations. Read the definitions
in [CosineField.lean](../ArithmeticTriangles/CosineField.lean) and the final
[Classification.lean](../ArithmeticTriangles/Classification.lean) when checking
that the specification matches the intended mathematics. See
[provenance](Provenance.md) for the limits of automated assurance.

Regenerate the source-size table using:

```sh
python3 scripts/source_stats.py > docs/SourceStatistics.md
```

Counts include comments and blank lines. They measure source size rather than
novelty, difficulty, or independent human contribution.
