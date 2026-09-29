# Theorem Π (pion completeness) — Lean 4 formalisation

A self-contained Lean 4 / Mathlib project that machine-checks **Theorem Π** of the accompanying note
(`../pion-completeness-A.html`, supplement `../pion-completeness-A-supp.html`): for every even `N ≥ 6`,

* **clause 1 (completeness)** — every non-degenerate coordinate zero of the pion amplitude `𝒜_N` contains a member of the family `𝒢_N`
  (`PiZ.pi_clause1`);
* **clause 2 (minimality)** — every member of `𝒢_N` is a non-degenerate zero and is minimal (`PiZ.pi_clause2`);
* **hence** — the minimal non-degenerate zeros are exactly `𝒢_N` (`PiZ.pi_minimal_iff`).

Status: **draft, not yet peer-reviewed.** Licence: to be decided by the authors.

## Reproduce the check

Requirements: [elan](https://github.com/leanprover/elan) (installs the pinned toolchain `leanprover/lean4:v4.34.0-rc2` automatically),
git, ~8 GB free RAM per Lean process, ~6 GB disk for Mathlib's build cache.

```sh
cd lean
lake exe cache get        # download Mathlib's compiled files for the pinned commit (85e3a25e…, tag v4.34.0-rc2)
lake build                # compiles the four library files and the chain PionCompleteness.C0 … C10 (≈ 25–45 min on a laptop)
lake env lean Verify.lean # prints the three statements and their axioms
```

Expected: every `#print axioms` line in `Verify.lean`'s output is

```
'PiZ.pi_clause1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(likewise for `pi_clause2`, `pi_minimal_iff`, `germ_input`, `resChild_input`, `stZero_input`), i.e. Lean's three standard axioms and
**no `sorryAx`**. Optional independent kernel re-check of every compiled module: `lake env leanchecker PionCompleteness.C0` (and so on
through `C10`). File integrity: `shasum -a 256 -c SHA256SUMS`.

Memory: the proof is split into a **linear chain of modules** (`PionCompleteness/C0.lean` … `C10.lean`, each importing the previous one,
and the import-only wrapper `PionCompleteness.lean`), so modules compile one after another with peak ≈ 8 GB each. A single-file version
of the same text needs more than 26 GB. The chain is a pure re-packaging: removing the generated `import` / `namespace PiZ` / `open …` /
`end PiZ` lines at the module boundaries gives back the accepted merged text byte for byte (md5 `fd58cb085e3938f6ba99af51be0e9293`).

## What to read to trust the result

A machine check proves exactly the statements written in Lean, so the part to review is the **statements and definitions**, not the proofs:

* the definitions (`calA` ≈ l.73, `NonDegPt`, `AmpZeroOn`, `IsNDZero`, `IsMinimalZero` ≈ l.100–115, `sepPairs` ≈ l.365, `gFamily` ≈ l.389, …)
  are in `PionCompleteness/C0.lean` (namespace `PiZ`; its module docstring explains the conventions: legs `1..N`, chords as sorted pairs,
  the amplitude as the δ-shift coefficient of the Tr φ³ triangulation sum); the three theorem statements are near the end of
  `PionCompleteness/C10.lean` (`pi_clause1` ≈ l.1138, `pi_clause2`, `pi_minimal_iff`), and `Verify.lean` prints them with `#check`;
* the imported library files `TreeRectangleZero.lean` (amplitude, mesh, triangulations), `ChainSlice.lean`, `PionZeros.lean`,
  `PionNLSM.lean` (the NLSM numerator `NP` and its residue / zero theorems). They contain a few unrelated statements that are still open
  (`sorry`); none of them is in the dependency closure of Theorem Π, which `#print axioms` confirms.

**Comments in the `.lean` files are historical.** Docstrings carry status markers from the development (for example `` `sorry` (pkgST,
M3; …) `` on `stZero_input` in `C10.lean`, or the list of "3c-b targets" in `C0.lean`'s header), internal project codes (`R12-P7b0`,
`PREFORM-Germ`, `pkgGerm`, …) and references to files that are not in this directory. Many of those markers are superseded: the
statements they call `sorry` were proved later. The files are kept byte for byte as accepted (see `SHA256SUMS` and the md5 above), so the
comments were not edited. The authority on what is proved is `#print axioms`, not the comments.

## Files

| file | role |
|---|---|
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | pinned toolchain, Mathlib commit, all transitive dependency revisions |
| `TreeRectangleZero.lean`, `ChainSlice.lean`, `PionZeros.lean`, `PionNLSM.lean` | imported library (earlier project phases) |
| `PionCompleteness/C0.lean` … `C10.lean`, `PionCompleteness.lean` | Theorem Π: frozen definitions and statements, all proofs, controls and an axiom report |
| `Verify.lean` | the check to run |
| `SHA256SUMS` | integrity of every file above |

## Provenance

The proofs were produced by AI prover agents and accepted by the project's hardened acceptance checker (frozen statements compared
expression-by-expression against a reviewed base; a code-execution filter; kernel replay of every declaration; `leanchecker`; guard
theorems; a dependency-closure check). Final verdict `ACCEPT-RESULT: PI-M3 CLOSED` on 2026-09-28 (8 567 declarations, 12 modules).
The checker, its reviews and the full development history live in the authors' research repository.
