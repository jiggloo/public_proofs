# Completeness of the coordinate zeros of tree-level pion amplitudes (Theorem Π)

- [`paper/pion_completeness-draft.pdf`](paper/pion_completeness-draft.pdf): the paper, a draft. Its title page says
  *Draft, not a release*.
- [`lean/`](lean/): the Lean 4 / Mathlib project that proves the paper's main theorem, Theorem 3.1. Its
  [`README.md`](lean/README.md) says what the compared theorems state and how to build and check them.

**Status: a draft, not a release, and not peer reviewed.** These files are made public before the paper's first
release, which includes the submission of the Lean code to Palomar. The release process has not been run on them: no
version number, no tag, no release checks and no submission yet. Where the paper and the Lean documentation speak of "this release", they mean
the first release, which these files precede. The first version of this proof, with an AI-written draft note that the
paper supersedes, is in
[`jiggloo/public_proofs`](https://github.com/jiggloo/public_proofs/tree/3c27d89b1cc873b5c2625a9dbbb45e8055f3e48b/pion_completeness)
at commit `3c27d89b1cc873b5c2625a9dbbb45e8055f3e48b`.

## AI use

The paper's section *Tool and computational resource disclosure* (Section 10 of the PDF) says how the paper and its
Lean code were made and what checked them. This section states only the AI use in preparing these files for
submission, which the paper does not cover.

- **Tools.** Claude Code, with the model Claude Opus 5.5 (`claude-opus-5-5`) of Anthropic.
- **Purpose.** To prepare these files for submission to Palomar: check which files could be made public, with the
  private source's leak check for private paths and internal references; build the PDF from the paper's source; copy the files here; write this
  README and the changes to the repository's `README.md` and `.gitignore`.
- **Parts affected.** This README and the repository's `README.md` and `.gitignore`. The PDF was built, unchanged,
  from the paper's source. The files of `lean/`, `docs/`, `LICENSES/`, `NOTICE` and `REUSE.toml` were copied
  unchanged from the private source.

## License

The paper is licensed under the Creative Commons Attribution 4.0 International License (CC BY 4.0), the Lean code under
the Apache License, Version 2.0. See the repository's [`NOTICE`](../NOTICE) and [`REUSE.toml`](../REUSE.toml).
