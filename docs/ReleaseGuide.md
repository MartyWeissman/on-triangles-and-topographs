# Publication checklist: GitHub and Zenodo

The source repository is
[MartyWeissman/on-triangles-and-topographs](https://github.com/MartyWeissman/on-triangles-and-topographs).
[Version `v0.1.0`](https://github.com/MartyWeissman/on-triangles-and-topographs/releases/tag/v0.1.0)
was released on 2026-11-07 and archived as [DOI 10.5281/zenodo.24043993](https://doi.org/10.5281/zenodo.24043993).
Zenodo integration was enabled before publication. The DOI was added to
repository metadata afterward; this did not change the archived release.
The steps below describe the publication workflow for subsequent releases.

## Before uploading

- Review the mathematical statement, documentation, AI-assistance disclosure,
  author metadata, published references, and the account of the working
  manuscript’s development.
- Confirm the licensing scope in [LICENSES.md](../LICENSES.md): Apache 2.0
  for software and CC BY 4.0 for standalone documentation. Both full license
  texts are included; `CITATION.cff` records the software license. Preserve
  the documentation-license distinction in the Zenodo record description.
- Run `./scripts/verify.sh`; review the result rather than relying only on the
  saved report. Inspect the source archive and its checksum.
- The repository is `MartyWeissman/on-triangles-and-topographs`.
  The existing Lean package and namespace remain `ArithmeticTriangles` for
  source compatibility.

Use this curated directory to begin a new repository history. Do not publish
the private development repository's history: its earlier commits contain
research material and local-path records excluded from this release.
The `.gitignore` excludes dependency caches and build products, but always
inspect the actual staged file list before uploading.

## GitHub

Upload the reviewed source and wait for its Lean workflow to pass. The
repository URL is recorded in `CITATION.cff`. GitHub recognizes a root `CITATION.cff` and presents citation
information: [GitHub citation-file documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files).

Keep `lake-manifest.json` and `lean-toolchain` under version control. Do not
upload `.lake/`, `.tools/`, `work/`, private research material, or the old `.git/`
directory. A small source archive can still require substantial downloaded
storage when someone builds it.

## Zenodo

1. Sign into your own Zenodo account and connect the intended GitHub account.
2. Enable archiving for this repository **before** creating the first GitHub
   release. See [enable a repository](https://help.zenodo.org/docs/github/enable-repository/).
3. Confirm citation metadata, license, version, and release notes. Create the
   reviewed version tag and GitHub release (the initial proposed version is
   `v0.1.0`, matching the package version).
4. Check Zenodo's import status and inspect the resulting deposit, file list,
   author details, license, version, and assigned DOI. See
   [archive a GitHub release](https://help.zenodo.org/docs/github/archive-software/github-upload/).
5. Add the actual DOI and publication date to subsequent citation metadata and
   repository documentation, and update Zenodo's metadata as needed. Do not
   invent a DOI, predate publication, or imply that a later metadata commit was
   included in an earlier archived source snapshot. Cite the particular archived
   version when reproducibility requires that version.

This package uses `CITATION.cff` as its single citation-metadata source. Zenodo
supports a subset of CFF; if a `.zenodo.json` is also present, it takes precedence.
Avoid maintaining two conflicting metadata files. See
[Zenodo's CFF guidance](https://help.zenodo.org/docs/github/describe-software/citation-file/).

## Later versions

Document mathematical changes separately from editorial changes in the
changelog. Re-run verification after source or dependency changes. Keep a
stable version tag for each archived release and record its checks. A DOI
makes an artifact citable; it does not itself constitute peer review of the
mathematics or formal specification.
