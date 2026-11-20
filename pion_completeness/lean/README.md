# Completeness of the coordinate zeros of tree-level pion amplitudes: the Lean proof

This Lean 4 / Mathlib project proves the main theorem of the companion paper, *Completeness of the coordinate zeros of
tree-level pion amplitudes* (Henru Wang; its Theorem 3.1, called Theorem Π in the Lean code). The theorem holds for
every even number `N ≥ 6` of pions, for the tree-level, flavor-ordered, massless amplitude of the non-linear sigma
model (NLSM). It classifies the minimal sets (by inclusion) of pairs of legs whose mesh variables, set to zero, make
the amplitude vanish identically. Such a set must leave every planar variable, the denominator of a propagator, not
identically zero.

Comparator (`leanprover/comparator`, shipped with Lean as `lake comparator`) is the checker that the Palomar registry
of formal proofs uses. It checks that a project proves the statements of a separate file, the Challenge, with the same
definitions and only the permitted axioms. The Lean code states the main theorem as the three theorems that comparator
checks here.

This README is for a reader who wants to check the Lean code. It says what the three theorems state, what they leave
out, how to build and check them, and how the code was made. The paper's Appendix A, "The formalization", says how
the paper's statements match the Lean code. [`formalization.yaml`](formalization.yaml) holds these facts in structured
form. Its `alignment` gives the Lean names of each statement of the paper that has a Lean counterpart, and names the
one lemma that has none.

## The three compared theorems

Comparator, run on [`comparator.json`](comparator.json), checks three theorems of the module `PionCompleteness.Paper`
against the statements of the Challenge, [`PionCompletenessChallenge.lean`](PionCompletenessChallenge.lean). The
Challenge restates them with every definition they use, and imports only Mathlib. All three theorems live in the
namespace `PionCompleteness.Paper.NLSM.Zeros` and assume `6 ≤ N` and `Even N`.

**The objects**, as the Challenge defines them. Each definition is copied character for character from this project's
library, the modules under `PionCompleteness/`.

- **Legs and pairs.** The `N` legs are the numbers `1, …, N` in cyclic order. A pair `{a, b}` of two legs that are not
  adjacent is written `(a, b)` with `a < b`. The pairs are exactly the diagonals of the `N`-gon, `diagonals N`.
- **Planar variables and mesh variables.** The kinematic space has one coordinate `X_ab`, a planar variable, for each
  diagonal. The mesh variable of a pair is the linear form `c_ab = X_ab + X_{a+1,b+1} − X_{a,b+1} − X_{a+1,b}`
  (`mesh`), with `X` read as `0` on the edges of the polygon. The docstrings call a pair's mesh variable a *tile*.
  For massless momenta, `c_ab = −2 p_a·p_b`, so setting `c_ab = 0` sets the Mandelstam invariant `s_ab` of the two
  legs to zero. This reading is the literature's; the Lean code has no momenta.
- **The amplitude** `NLSM N` (written `A_N^NLSM` in the docstrings). Take the tree amplitude of the `Tr(φ³)` theory:
  the sum, over the triangulations of the `N`-gon, of the product of `1/X` over the diagonals of the triangulation
  (`amp`). Shift every planar variable whose two ends are even by `+δ`, and every one whose two ends are odd by `−δ`.
  Expand the shifted amplitude in powers of `1/δ`. The NLSM amplitude is its coefficient of `δ^(−(N−2))`, a rational
  function of the planar variables.
- **Coordinate loci and zeros.** For a set `S` of pairs, the locus `L_S` is where every mesh variable of `S` vanishes
  (`OnLocus`). `S` is **regular** when no planar variable vanishes identically on `L_S` (`IsRegularSet`). `S` is a
  **zero** when the amplitude restricts to the zero rational function on `L_S` (`IsCoordinateZero`, through
  `RatZeroOn`). A **regular coordinate zero** is a set of pairs that is both (`IsRegularCoordinateZero`).
- **Minimal.** A regular coordinate zero `Z` is minimal when, for each pair `t` in `Z`, the set `Z` without `t` is
  no longer a zero (`IsMinimalCoordinateZero`).
- **The list `𝒢_N`** (`IsListMember`; the theorems' names call it a *family*). Its members are of two kinds:
  - the **causal diamonds**: for two legs `a < b` with a leg strictly between them and a leg outside them, the pairs
    with one leg strictly between `a` and `b` and the other outside them (`sepPairs N {a, b}`, in
    `IsCausalDiamond`);
  - the **`T`-separated sets** `S_T`: for a set `T` of at least three legs, all of one parity, the pairs of legs
    outside `T` that lie in different arcs of the circle cut at the legs of `T` (`sepPairs N T`).

**The theorems.**

1. **Completeness**, `every_coordinate_zero_contains_a_family_member`: every regular coordinate zero `S` contains a
   member of the list.
2. **Minimality**, `family_members_are_minimal_zeros`: every member of the list is a minimal regular coordinate zero.
   Each member is a regular set, and the amplitude vanishes identically on its locus. When any one of its mesh
   variables is left free, the amplitude no longer vanishes identically.
3. **The classification**, `minimal_coordinate_zeros_are_the_list`: a set of pairs is a minimal regular coordinate
   zero exactly when it is a member of the list.

The zeros on the causal diamonds are the hidden zeros of arXiv:2312.16282. For `|T| = 3`, the `T`-separated sets are
the split kinematics of arXiv:2112.14191. [What was known](#what-was-known-and-what-the-search-did-not-find) lists the
other known cases and what the literature search did not find.

## What a reader checks

Lean's kernel checks the proofs. A reader checks that the statements, and the definitions they use, say what the paper
says:

- [`PionCompletenessChallenge.lean`](PionCompletenessChallenge.lean): the three statements and every definition they
  use. Its three proofs are `sorry` on purpose: comparator takes the proofs from `PionCompleteness.Paper`.
- [`Statements.lean`](Statements.lean) prints, and pins, the statements of the module `Paper`, the tests of
  `PaperTests`, the outside anchors of `Conventions` and the library definitions that match the paper's. A pin fails
  the build when the printed text changes. The outside anchors check the amplitude against the closed formulas of an
  independent paper, arXiv:1304.3048. A reader can read the pinned statements side by side with the paper.
- [`REVIEW-CHECKS.md`](REVIEW-CHECKS.md) lists the tests in the library's modules, by the statement of the paper each
  tests. A test here states what a definition gives on one example.

`Statements.lean` does not print some of the definitions that the three compared theorems use. Read them in their
modules, or in the Challenge, which copies them:

- the amplitude's sum: `TreeRectangleZero.amp`, `triangulations`, `IsTriangulation`
  (`PionCompleteness/Base/TreeRectangleZero.lean`);
- the shift: `PionNLSM.shiftSign`, `delta`, `shifted`, `shiftCoeff` (`PionCompleteness/Base/PionNLSM.lean`);
- the field of rational functions `PionNLSM.RF` and its generic point `gen`, at which a zero is read (the same file).

The other pinned statements also use library definitions that `Statements.lean` does not print, for
example the library's other forms of the causal diamonds and loci (`TreeRectangleZero.OnRect`, `PionZeros.OnZT`; see
*Two forms of the definitions* below), `PionZeros.quadrangulations`, `PionNLSM.zeroAt` and the proof's own
definitions in `C0`–`C10`.

## Assumptions and limitations

- **Hypotheses.** Each compared theorem assumes `N` even and `N ≥ 6`. They say nothing about odd `N` or `N = 4`. The
  definitions of a regular set and a zero do not assume `N` even; the theorems do.
- **Axioms.** The proofs depend on at most Lean's three standard axioms, `propext`, `Classical.choice` and
  `Quot.sound`. These are the axioms `comparator.json` permits.
- **The amplitude is defined, not derived from a Lagrangian.** `NLSM` is the coefficient of the shifted `Tr(φ³)`
  amplitude above (arXiv:2312.16282 eq. (7.15), arXiv:2401.05483 eq. (2)). The Lean code has no Lagrangian.
  - For every even `N ≥ 4` and every non-zero constant `F`, it proves that this amplitude is `−(2F²)^((N−2)/2)` times
    the sum over the Feynman diagrams of the Cayley parametrization of arXiv:1304.3048 §4.2 (`Pi.nlsm_knt_cayley`,
    module `Conventions`). `F` is the constant of that paper's formulas.
  - At `N = 4, 6, 8` it proves that the amplitude is the same factor times the closed formulas of arXiv:1304.3048
    (`Pi.nlsm_four_knt`, `Pi.nlsm_six_knt`, `Pi.nlsm_eight_knt`). At `N = 8` this holds off the poles: where no
    planar variable of an odd diagonal vanishes.
  - That this is the amplitude of the NLSM Lagrangian is cited, not formalized. It rests on arXiv:1304.3048 and on
    the reading `s_{i,j} = X_{i,j+1}` of arXiv:2403.04826 (the paper's Remark 2.7). There `s_{i,j}` is the invariant
    of the consecutive legs `i, …, j`, not the two-leg `s_ab` above.
- **The sign.** The normalization is `NLSM_4 = −(X₁₃ + X₂₄)` (`NLSM_four`), the sign of arXiv:2610.01775 and
  arXiv:2401.05483. At `N = 4`, arXiv:2312.16282 writes the opposite sign (eqs. (4.4), (7.17)), while its six-point
  amplitude (4.3) has this one. Both of its amplitudes match `(−1)^(N/2−1)` times `NLSM_N`, the normalization in which
  the quartic Feynman rules of arXiv:2607.27345 give the amplitude. No zero depends on the overall sign.
- **General spacetime dimension.** The planar variables are independent coordinates. In four dimensions they satisfy
  Gram-determinant relations; the theorems say nothing about that case.
- **Coordinate loci only.** The theorems classify zeros on loci cut out by setting mesh variables to zero. Zeros on
  other linear loci (arXiv:2610.01775 §6.2) are outside them.
- **How a zero is read.** `RatZeroOn` writes the amplitude as `P/Q`. It asks that `P` vanish at every rational point
  of the locus, and that `Q` not vanish at at least one of them. Over the rationals this is the same as vanishing
  identically on the locus. Neither that equivalence nor the independence of the choice of `P` and `Q` is a Lean
  statement. A point is a function on all pairs of natural numbers, not only on the diagonals. The planar variables
  and the amplitude read only the diagonals, so the other coordinates are free and change nothing.
- **Minimal, pair by pair.** The definition removes one pair at a time. For even `N ≥ 4`, a regular set of pairs that
  contains a zero is itself a zero (`isCoordinateZero_of_subset`). So no proper subset of a minimal zero is a zero
  either (the paper's Remark 2.16).
- **What is formalized.** Besides the main theorem, every definition, fact, lemma, proposition, theorem and corollary
  of the paper has a Lean counterpart, except Lemma F.8. Seven remarks and three examples also have Lean
  counterparts; no other remark or example is formalized. `formalization.yaml`'s `alignment` lists each.
- **Not formalized.** Lemma F.8 of the paper (a locus is generic) is proved only in the paper, and the compared
  theorems do not depend on it. `polygon_numerators_vanish_on_ear_locus` takes the lemma's conclusion as a
  hypothesis. The Lean proofs that use it prove that hypothesis for each diagonal they need, at a point they
  construct (`Pi.pkR_b_wit4`). For the sign in the paper's Remark F.17, the Lean code proves only that it is not
  zero, not its value.
- **Two forms of the definitions.** The library's proofs use their own forms of the definitions, for example
  `Pi.IsNDZero` for a regular coordinate zero and `Pi.gFamily` for the list. The module `Paper` proves the two forms
  of each definition equivalent under the theorems' hypotheses, except for the causal diamonds, which the theorems use
  only through the list. It derives the compared theorems from the library's `Pi.pi_clause1`, `Pi.pi_clause2` and
  `Pi.pi_minimal_iff` (module `C10`).
- **How the forms differ.** For each statement of the paper whose Lean form differs or is missing,
  `formalization.yaml`'s `alignment` has a note: how the forms differ, and how they agree.
- **Docstrings.** The Challenge's docstrings cite library results that it does not copy, such as `NLSM_four`. Find
  them in the library's modules.

## Files

| File | Holds |
|---|---|
| `PionCompleteness.lean` | the library's root: imports every module, so `lake build` builds them all |
| `PionCompleteness/Base/` | the amplitude, the mesh and the loci: `TreeRectangleZero`, `ChainSlice`, `PionZeros`, `PionNLSM` |
| `PionCompleteness/C0.lean` … `C10.lean` | the proof of Theorem Π in the library's terms, each module importing the previous one; the statements are in `C10` |
| `PionCompleteness/Paper.lean` | the paper's definitions and statements, and their proofs from the library's |
| `PionCompleteness/PaperTests.lean` | every test of `Paper`: non-vacuity, definitions on given objects, examples |
| `PionCompleteness/Conventions.lean` | the outside anchors: arXiv:1304.3048's closed formulas and Feynman rules |
| `PionCompletenessChallenge.lean`, `comparator.json` | the Challenge and comparator's configuration |
| `Verify.lean`, `Statements.lean` | the axioms check and the pinned statements (targets, not built by default) |
| `formalization.yaml` | the structured metadata, in version v0.4 of the mathlib initiative's `formalization.yaml` standard; generated, not edited by hand |
| `PROVENANCE.md`, `RENAME_MAP.tsv` | how this project relates to the first version of this proof ([below](#earlier-formalizations)), and the reviewed renames |
| `REVIEW-CHECKS.md` | the tests outside `PaperTests`, by the statement of the paper they test |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | the Lake package and its pins |

## Build and check

You need [elan](https://github.com/leanprover/elan), which installs the pinned toolchain `leanprover/lean4:v4.35.0`
from [`lean-toolchain`](lean-toolchain), and git. Mathlib is pinned to its tag `v4.35.0` in
[`lakefile.toml`](lakefile.toml), and every dependency's revision is in [`lake-manifest.json`](lake-manifest.json).
Plan for about 9 GiB of disk: Mathlib's checkout and build cache take about 7.3 GiB, the other dependencies and this
project's build the rest. Plan for at least 8 GiB of free memory: single modules have peaked at 4–7 GiB.

**Building runs code from the project and its dependencies with your permissions.** Every command below except
comparator does: Lean runs the project's code while it elaborates, Lake evaluates the dependencies' lakefiles, and
`lake exe cache get` runs Mathlib's cache program and downloads compiled files. The output of `lake build Verify` and
`lake build Statements` can be trusted only if no code tampered with the build. For a copy you do not trust:

1. Check that `lean-toolchain` reads `leanprover/lean4:v4.35.0`, and that `lake-manifest.json` names the official
   repositories at the revisions listed. elan installs whatever toolchain `lean-toolchain` names, and comparator
   itself comes with that toolchain.
2. Run comparator first, or run every command in a container or a virtual machine. A build run on your machine before
   comparator can change what later commands, comparator included, report.

In this folder:

```sh
lake exe cache get                     # Mathlib's compiled files for the pinned commit
lake build                             # every module of the library
lake build Verify                      # the axioms of every listed result, the three compared theorems among them
lake build Statements                  # the pinned statements and definitions
lake build PionCompletenessChallenge   # the Challenge: warns "declaration uses `sorry`" 3 times, by design
```

- `lake build` builds the library and fails if any proof fails. On a 5-CPU CI runner, the module times of a cold
  build, with Mathlib from its cache, summed to about 37 minutes. No wall time of a cold build alone was measured.
- `lake build Verify` runs `#print axioms` on each listed result inside `#guard_msgs`. The build fails unless each
  result depends on at most `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`, and no axiom declared in
  this project.
- `lake build Statements` prints each pinned statement (`#check`) and definition (`#print`). It fails if one differs
  from the text written above it.

Optionally, `leanchecker` checks the compiled modules' declarations in Lean's kernel again. Each replay task uses
about 2–2.5 GiB, and `LEAN_NUM_THREADS` caps how many run at once:

```sh
LEAN_NUM_THREADS=2 lake env leanchecker PionCompleteness.Paper    # or any module; list them all to replay all
```

**Comparator** checks that `PionCompleteness.Paper` proves the Challenge's three statements with the same
definitions, in Lean's kernel, using no axiom outside the three in `comparator.json`. It builds and exports both
modules inside a bubblewrap (`bwrap`) sandbox. So it needs Linux with bubblewrap installed, and bubblewrap needs
either unprivileged user namespaces or a setuid-root install:

```sh
lake comparator                        # reads comparator.json; exit 0: accepted
lake comparator --paranoid             # also the other kernels bundled with Lean (lean4lean, nanoda, …)
```

Comparator compares definitions by their exact form. It rejects a Challenge definition changed to an equivalent one.
This keeps the Challenge tied to the library's definitions.

## What was known, and what the search did not find

The AI agents that made this code, described [below](#how-it-was-made), also searched the literature for earlier
statements of the results.

- **Not found in earlier work by that search:** completeness, and the zeros on the `T`-separated sets with
  `4 ≤ |T| ≤ N/2 − 1`. Whether they are new is unknown: a search that did not find a result does not show that it is
  new.
- **Proved here, not searched for:** the minimality of every member of the list. Whether it is new is unknown.
- **Known before, proved again here:** the zeros on the causal diamonds (arXiv:2312.16282 §4), on the `T`-separated
  sets with `|T| = 3` (arXiv:2112.14191 §4), and with `T` a whole parity class (arXiv:2607.27345 §IV.1).
- **The setup** comes from these sources:
  - arXiv:2312.16282 and arXiv:2401.05483: the amplitude's definition, the mesh, the causal diamonds, and the
    analytic facts about the amplitude that the proof uses (its order in `δ`, factorization, symmetry), which the
    Lean code proves;
  - arXiv:1711.09102 and arXiv:1912.12948: the planar and mesh variables;
  - arXiv:2610.01775: the notion of a regular linear zero, restricted here to coordinate loci, and the sign;
  - arXiv:2607.27345: the normalization, through its quartic Feynman rules.

  `formalization.yaml`'s `sources` lists each source, with its relationship and a note.

## Earlier formalizations

- **The first version of this proof**, released on 2026-09-29 in
  [`jiggloo/public_proofs`](https://github.com/jiggloo/public_proofs/tree/3c27d89b1cc873b5c2625a9dbbb45e8055f3e48b/pion_completeness/lean)
  at commit `3c27d89b1cc873b5c2625a9dbbb45e8055f3e48b` (toolchain `v4.34.0-rc2`). It was the first presentation of
  the result, released together with an AI-written draft note that the companion paper supersedes. This project is a
  port of it to a stable toolchain, with the paper's statements and the Challenge added.
  [`PROVENANCE.md`](PROVENANCE.md) records what the port changed and how that was checked.
- **Independent work:**
  - `GoldenPhysicsProject/GPPVerify` formalizes the hidden zeros of the `Tr(φ³)` amplitude at `N = 4, 5, 6`, with no
    NLSM and no classification.
  - `andrey-kokoev/marici` writes the `Tr(φ³)` amplitude as a sum over the triangulations of a polygon, as this
    project does, with no zeros.

  `formalization.yaml`'s `related_formalizations` gives the files and commits.
- **The search.** On 2026-10-30, the same AI agents searched Palomar's registry, GitHub's repository and code search,
  and the Lean Zulip by web search. They found no other formalization of the NLSM's coordinate zeros or of this
  classification. They did not search the Isabelle AFP or the Rocq package index directly.

## How it was made

The paper's section "Tool and computational resource disclosure" is the full account. The paragraphs below on the
author's role, on what a person had checked and on responsibility quote it word for word, with its references to the
paper's own parts written out. The others condense it.

AI agents produced the research behind the paper, the text of the paper with its proofs, this Lean code and the
computer checks: Claude Code, with the model Claude Opus 5.5 (`claude-opus-5-5`) of Anthropic, from September to
October 2026. Some agents of the research were asked to run Claude Fable 5.1 (`claude-fable-5-1`); their records show
that almost all of their requests were served by Claude Opus 5.5.

**The author's role.** The agents made most of the choices of the research. They proposed the routes to the proof,
and they chose each lemma, each computation and each line of the Lean code and of the paper's text. The author made
the main decisions at the level of the project: its aims and scope, the standards it follows, and the methods by which
its results were produced and checked. These methods include the formalization in Lean, automated checks run on every
change, tests of the Lean statements and definitions, reviews by AI agents and a record of the research. The author
chose these methods and set their requirements. The agents built the tools for these methods, ran them and chose their
details. In the research itself, the author also chose among options the agents proposed, such as which routes to the
proof to try. The author approved each change to the paper and to the Lean code after its automated checks had passed
and AI agents had reviewed it; in the research, from which the first version of the Lean code came, the author
approved the work the same way. Approval was a decision to accept a change, not a reading of it.

**Review and checks.** AI agents of the same model reviewed the research, each change to the Lean code and each change
to the paper. All of these reviewers were Anthropic's Claude models; none was a model of another developer, and none
was a person. AI agents of the same model also compared the paper's statements and definitions with their Lean
counterparts.

- **A literal reading.** For the combinatorics of the paper's Section 7.2 and Appendix H, a computer check compared
  the Lean code with a literal reading of the text. Claude Opus 5.5 wrote that reading as a program, in separate
  sessions that had not seen the Lean code. Sessions that had seen it set the interfaces: the names of the functions,
  and how each statement is split into hypotheses. The check ran on finite instances with `N ≤ 16`.
- **Planted mistakes.** In October 2026, on an earlier version of the Lean code, AI agents planted mistakes on
  purpose, seven plantings in all. No check noticed two of the seven. These two led to new checks, which caught both
  when they were planted again.
- **Comparator's controls.** Comparator accepted the Lean code against the Challenge, and rejected two versions of
  the Challenge changed on purpose: one with a definition of the list changed to an equivalent form, and one with
  completeness lacking the hypothesis that `N` is even.
- **Bounded checks.** Programs written by the same agents evaluated many of the paper's statements, and the main steps
  of their proofs, on every instance up to a bound. The research also checked the value of the sign in Remark F.17
  numerically up to `N = 14`. The computer checks are evidence, not proof.

**What a person had checked at this release.** The author read and understood the statement of the main theorem,
Theorem 3.1, and the definitions it uses. The author read, followed and understood the idea of its proof in Section 1
and the map of the proof in Section 4.1. At this release, no person had read the Lean code, checked the proofs of the
paper, compared its statements with the Lean code, or checked the choices the literal reading made where the text can
be read in more than one way. In place of a person's comparison, AI agents compared the paper's statements with the
Lean code, and the literal-reading check, comparator and the tests of the Lean statements and definitions checked
parts of that comparison.

**What was not published.** The record of the research, the prompts given to the agents and summaries of their
reasoning, the planted mistakes, and the programs of the computer checks were not published with this release. The
author intends to publish the record of the research later.

**Responsibility.** The author takes full responsibility for the content of the paper and of the accompanying Lean
code, including the parts produced by AI agents. For the parts no person had checked, the author bases that
responsibility on the methods the author chose, described in the paper's disclosure section and in its Appendix A.
As, at this release, no person had understood every proof in full, the paper is released as an initial release of
results that no person had verified, so that others can check, use and correct them.

## License

Everything in this folder, the code and its documentation, is released under the Apache License, Version 2.0. Its
text is the `LICENSE` file at the root of this repository; the `LICENSES/` folder there holds the licenses of the
repository's other parts. Each Lean file's copyright header names that license.
