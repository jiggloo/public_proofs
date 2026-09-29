# Pion completeness (Theorem Π) — initial public draft

* `pion-completeness-A.html` — the note: the minimal non-degenerate coordinate zeros of the pion (NLSM) amplitude at every even
  multiplicity `N ≥ 6` are exactly the family `𝒢_N` (Theorem Π), with proofs.
* `pion-completeness-A-supp.html` — supplement (long proofs, tables, provenance). The two files link to each other.
* `pion-zero-examples.html` — "Pion zeros, one case at a time": a picture guide to Definition 2.7, Theorem 2.9 and Theorem 3.1 of
  the note, drawing each kind of zero in `𝒢_N` once in the kinematic-mesh style. A teaching companion, not part of the paper.
* `lean/` — a self-contained Lean 4 / Mathlib project that machine-checks Theorem Π; see `lean/README.md` to reproduce the check.

Status: **draft, not yet peer-reviewed.** Theorem Π is fully machine-checked (all three clauses, no `sorry`, only Lean's standard
axioms; `lean/`); no person has yet checked that the Lean definitions match the note's. Licence: Apache 2.0 (see [`LICENSE`](../LICENSE) and [`NOTICE`](../NOTICE)).
