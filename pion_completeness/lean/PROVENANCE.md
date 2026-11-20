# Provenance of the Lean proof of Theorem Π

This project is a tidy port of the Lean proof of Theorem Π first released in
[`jiggloo/public_proofs`](https://github.com/jiggloo/public_proofs), directory `pion_completeness/lean/`, at commit
`3c27d89b1cc873b5c2625a9dbbb45e8055f3e48b` (toolchain `v4.34.0-rc2`; accepted on 2026-09-28, by the author's
record). We call that release *the accepted text*. The port moves the proof module by module, bottom up along the import
graph, to the stable toolchain `v4.34.1` (since bumped to `v4.35.0`, [below](#toolchain)), with copyright headers,
precise imports, descriptive namespaces and docstrings that describe the statements. This file records how the released
files relate to the accepted text, what the port changed, and how that was checked.

Theorem Π is `pi_minimal_iff` with its two clauses `pi_clause1` (completeness) and `pi_clause2` (minimality), and `cl2a`
(the members of the family are non-degenerate zeros), all in `PionCompleteness.Pi` (module `C10`). To check this release
against the accepted text without the private tools: compare the hashes [below](#the-accepted-files) with
`public_proofs` at the commit above, then run `lake build` (every module) and `lake build Verify` (the axioms).

**How it was made.** The port was made from 2026-10-06 to 2026-10-12 with Claude Code (model `claude-opus-5-5`). Each
module was reviewed by four AI review agents (code quality, completeness, documentation, safety; same model), and the
author, Henru Wang, merged each port. The docstrings of `C1`–`C10` were first drafted by further agents of the same
model, each checked by a script to have changed comments only.

## The rule and the check

The rule and the check below held for the port and until the bump to `v4.35.0`; both were dropped with that
bump ([Toolchain](#toolchain)).

**The rule.** The port may change proofs, imports, comments, docstrings and names (through the reviewed rename map,
[`RENAME_MAP.tsv`](RENAME_MAP.tsv)). It does not change definitions or statements, with two kinds of listed exception:

- a declaration may be removed, if it was unproved (`sorry`) and outside the closure of Theorem Π (the declarations
  its statements and proofs depend on); the map lists it with `-` (three declarations, [below](#removed-declarations));
- a theorem may drop arguments that the rest of its statement does not use outside proofs (instance arguments
  `[DecidablePred A]`, …, or an unused hypothesis); the map lists it with `~` (eleven theorems,
  [below](#statement-changes)). The new statement implies the accepted one (apply it and ignore the dropped
  arguments). Until 2026-10-12 only helper theorems (ones the paper does not cite) and only instance arguments were
  allowed; the rule was widened after the port, so that statements can match the paper exactly (see
  [`Paper`](#new-module-paper)).

**The check.** A Lean command (the *statement check*) loads a verbatim copy of the accepted module and the ported module
into one environment and compares, for every declaration, the kind, the universe parameters, the type, the instance and
reducibility status and (for definitions) the body, after applying the rename map, up to binder names and with universe
levels in normal form (`max (u+1) 1` is `u+1`), and with every proof inside a statement or a definition erased first
(two proofs of the same proposition are interchangeable for Lean's kernel, so only what they prove counts). Lean's
generated declarations that a compared type or body uses (the matcher holding a definition's `match` patterns, for
example) are compared too. A binder name is not part of a statement, so an unused hypothesis `hn` may become `_hn`;
binder kinds (explicit, implicit, instance) must match. The rename map renames only declarations of the verbatim copies,
never a library constant, and every entry must be used. Declarations added by the port, declarations the map lists as
removed (by exact name; one the port still has is an error) and the theorems the map lists as changed (the checker
accepts only dropped arguments the rest of the statement does not use outside proofs, and a listed theorem
whose statement did not change is an error) are reported. Each module's summary is pinned in the source repository's
tests, so any change to it is reviewed.

The checker has its own negative controls: changes to a definition body, a hypothesis, an argument's kind, a dropped
declaration, a theorem turned into a definition, `match` patterns, a theorem named like an equation lemma, a `private`
theorem, an instance turned into a definition and an added constructor are all reported, as are unused and colliding
map entries, a namespace-wide removal, a universe level one higher and a changed value next to a proof, also when the
ported module hides its definition bodies (Lean's module system). For `~` entries, an unlisted drop, a listed theorem
left unchanged, a used instance or argument replaced or dropped, a drop together with another change, swapped
arguments, an added instance and an added hypothesis are all reported. Faithful ports, including ones whose universe
levels differ only in form, pass.

The checker is a tool of this release's source repository and is not released with it yet; this file states its
results. What a reader can check without it: the hashes below, `lake build` (every module), `lake build Verify`
(the axioms) and `lake build Statements` (the statement pins, below).

**Axioms.** `Verify.lean` asserts, for each of the 556 results listed there (2026-10-26), the axioms it depends on, each
`#print axioms` wrapped in `#guard_msgs`, so a different answer fails the build. Every listed result depends on exactly
`[propext, Classical.choice, Quot.sound]`, except `legZ_labZ` and `legZ_rotLeg` (`C0`) and `shiftSign_of_parity_ne` and
`rotInv_rotInv` (`Paper`), which need only `[propext, Quot.sound]`, and `shiftSign_values` (`PaperTests`), which depends
on none. The list contains every result the accepted text printed the axioms of (its final "Axiom report", 57 `#print
axioms` lines), and more.

**Statements.** `Statements.lean` pins, under `#guard_msgs`, the four statements of Theorem Π (`C10`) and every
declaration of `Paper`, `PaperTests` and `Conventions`: each theorem as `#check` prints it, each definition as `#print`
prints it, so `lake build Statements` fails on any change to them; it also pins, with `#print`, the library definitions
that a definition of the paper is matched by (listed in the file's docstring), and, since the bump to `v4.35.0`, ten
more library definitions and nine library theorems the paper cites ([Toolchain](#toolchain)). That every declaration of
these three modules has a pin there is checked by a tool of the source repository (a metaprogram, so not part of this
release).

## Names, modules and registry keys

**Names.** The accepted text used internal project codes as namespaces (`R12P1`, `R12P3`, `R12P3C`, `R12P4A`, `PiZ`).
Each library module now has the namespace `PionCompleteness.<Module>`, and the chain `C0`–`C10`, which continues one
text, has `PionCompleteness.Pi`, as does the new module `Conventions` (and `NonVacuity` had); the new module
`PaperTests` has `PionCompleteness.PaperTests`. Declaration names are unchanged,
except that the 206 helper definitions whose names contained `_` are now in lowerCamelCase, Mathlib's convention for
definitions (`_` marks theorems): each `_` is dropped and the letter after it capitalized (`pkD_x` → `pkDX`,
`p3b_IsChild` → `p3bIsChild`); where two names would coincide, the letter that was lower case stays lower case
(`pkD_Y` → `pkDY`, `pkD_y` → `pkDy`; `pkR_ch_E` → `pkRChE`, `pkR_ch_e` → `pkRChe`). `RENAME_MAP.tsv` lists each of
them, and the one definition renamed since for the paper's word: `IsMinimalChord` → `IsInnermostChord`, with its
generated `Decidable` instance (2026-10-19; "minimal" is the paper's word for minimality over sets, and the chord is the
innermost chord). Theorem names are unchanged, so some still spell a definition the old way (`pkG_V_eq_faceVertex` is
about `pkGV`). Helper prefixes such as `pkG`, `pkR`, `pkCh` label the parts the accepted text was assembled from; they
carry no mathematical meaning and are kept.
The new module `Paper` has the namespace `PionCompleteness.Paper`. A declaration that a claim of the paper names (it
carries the claim's registry key, below: a theorem stating the claim, or a definition the claim introduces) is named
`PionCompleteness.Paper.<subject path>.<name>`, where the subject path is the claim's subject in the owner's registry,
in UpperCamelCase with acronyms kept whole (`nlsm.zeros` → `NLSM.Zeros`); a theorem stating the claim is usually named
after the last part of the claim's descriptive name (`nlsm.zeros.minimal-coordinate-zeros-are-the-list` →
`PionCompleteness.Paper.NLSM.Zeros.minimal_coordinate_zeros_are_the_list`). Lemmas in the namespace of such a definition
move with it, so that dot notation finds them (`PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.add`). The other
declarations of `Paper` (companion forms such as `t_separated_zero_pointwise`, helper lemmas and definitions) keep `PionCompleteness.Paper.<name>`. Since 2026-10-26 every test of `Paper` (its examples and
non-vacuity facts among them, seven of which carry a claim's key) is in `PaperTests`, named
`PionCompleteness.PaperTests.<name>`.

**Module system.** Since 2026-10-08 every file is a Lean *module* (first command `module`): imports are `public import`
(`Verify.lean` imports the library privately; it declares nothing), and each library file puts its declarations in
`@[expose] public section`, so every declaration is public and every definition's body stays visible to importing
files, as in the accepted text. `#print axioms`, the per-declaration axioms check and kernel replay (`leanchecker`)
still see the proofs. The statement check found 0 differences for every module after the change.

**Exposure narrowed, then restored.** From 2026-11-17 to 2026-11-20 the library hid most definitions' bodies from
importing files: each library file opened a plain `public section`, and 253 of the library's 443 definitions had
their bodies exposed, each where a build of the library needed it. Comparator, the check Palomar runs (see *New file:
`PionCompletenessChallenge`*), then rejected the Challenge in the author's own run, before any release. The Challenge
exposes every body. Each copied definition matched the library's text apart from `@[expose]`, but exposure changes
the compiled constants. An exposed definition that uses hidden ones (`IsRegularCoordinateZero` uses `IsRegularSet` and
`IsCoordinateZero`) gets a lower definitional height (the reducibility hint Lean stores with it). A hidden body's
auxiliary proofs get private names. The author
judged choosing which bodies to expose not worth the effort, so every body is exposed again, as before. The narrowed
state was never released.

**Registry keys.** Since 2026-10-12, key declarations carry a comment `-- registry: C-…` (a claim) or `T-…` (a term)
before their docstring. The key is a stable identifier of the claim or term in the owner's registry; quote it to ask
the author for the history behind it (drafts, reviews, experiments). The docstrings describe the statements only: the
accepted text's citations of drafts, reviews and experiments are not in the released files, and the accepted text
itself, at the commit above, keeps them verbatim. Since 2026-10-21 the declarations of `Conventions` that the registry
names carry keys too.

## The accepted files

The accepted text has four library files and one Theorem Π source of 27,005 lines (sha256
`baedaecdc8df6adb159f8e1f2a958b41b3b8f9c74800f44541faf1cdb8195820`), which was not published as one file: the
accepted release cut it into the linear chain `C0` → … → `C10`, so that each module compiles in about 8 GB (a
single-file build needed more than 26 GB).
The cut is by line count: `C0` is lines 1–2506, a blank line and `end PiZ`; module `Ck` (`k ≥ 1`) is the line
`import PionCompleteness.C(k−1)`, a blank line, `namespace PiZ`, a blank line, the text's own `open` line (line 56), a
blank line, then lines `a`–`b` of the text; every module but `C10` ends with a blank line and `end PiZ` (`C10` runs to
the end of the text). Removing the added lines and joining the modules gives back the text with the sha256 above.

All files are at `public_proofs` commit `3c27d89` (the chain is unchanged since commit `0df22d2`), under
`pion_completeness/lean/` (the library files at its top level, the chain in `PionCompleteness/`). The port of
each is the module of the same name here (library files in `PionCompleteness/Base/`).

| module | lines of the source | sha256 of the accepted file | compared: statements, definitions | listed changes | results in `Verify.lean` |
|---|---|---|---|---|---|
| `TreeRectangleZero` | — | `8ab005daa440cba972c7fc2ef41cc8ae528f890efeb4c6ab1c7a7a2ad86a6514` | 62, 29 | — | 19 |
| `ChainSlice` | — | `bbece3266702ff96e6c4b4d0ab4a38f3521754593203bbc2bec47b25eabd979e` | 84, 38 | 2 removed | 18 |
| `PionZeros` | — | `1aff45600a1c95520e9f8ce7a06011876fc2a6f83a44bb4fc19e73a5b16b27c3` | 144, 59 | — | 31 |
| `PionNLSM` | — | `eae212b870c0058f3af074f3496bede78bddd9eb55f956235470015f40f9d812` | 292, 46 | 1 removed, 1 `~` | 27 |
| `C0` | 1–2506 | `cf7a999105b9eed37835236c3a23291e4496659e8fa10c077a527b09da08dd93` | 124, 89 | 1 `~` | 21 |
| `C1` | 2507–5064 | `b7497b1098eb0aa40d44050284840e45b04dc0e1b0200539718bba59e49d4bc3` | 132, 6 | — | 4 |
| `C2` | 5065–7638 | `ffda275b171ce7720f00662177ab25da69388ce36f69725bccec8c7d31984b96` | 84, 2 | 1 `~`, 22 added | 2 |
| `C3` | 7639–10145 | `2c14fab62cdc3617c4da4d238d49010844b82d0183e65658f05032918d41f872` | 37, 1 | 1 `~`, 6 added | 7 |
| `C4` | 10146–12647 | `6930a93f72e3b7d09d8fd38256e36aadf9465a2f86d14ef4b08763153116c299` | 165, 37 | 2 `~` | 6 |
| `C5` | 12648–15150 | `c7154ca57cdc6562184a7c71ac359d7adeef28d3c40f11dbd232b98ef7bb83b9` | 109, 21 | 5 `~` | 1 |
| `C6` | 15151–17661 | `0387ff41bc7a3ed27c0ac9f6037e2bcdc08d4d48db6c8bfc62ca36385bf1821d` | 122, 27 | — | — |
| `C7` | 17662–20163 | `df4836d0bdec4a078e0bcc8ab9871dc8663be3a4e16dcccca3c3748b1f0a5321` | 131, 12 | — | — |
| `C8` | 20164–22670 | `b9521586e22eca3848e61d107abfd085e26107ba140a4fcbb42a0b2631966577` | 100, 8 | — | — |
| `C9` | 22671–25202 | `e478e4bf5beed17d539cf4726e373390f9dbd022387a3a6fc02314b1846748ec` | 86, 19 | — | — |
| `C10` | 25203–27005 | `58c2f7f2fbe3bc26b5c4681f063723227b2e59b5c93d695f364e1d0ad9cb2629` | 134, 27 | 1 `~`, 3 added | 44 |

For every module the statement check reported **0 differences** (at every run, the last on `v4.34.1`) and no declaration
added, removed or changed other than those listed. `C6`–`C9` hold helpers of the residue input, whose result
`resChild_input` (`C10`) is in `Verify.lean`. `C10` adds one control (2026-10-13): `control_ndZero_not_minimal` proves
that `S_{1,3,5} ∪ {(1,4)}` at `N = 6` is a non-degenerate zero that is not minimal, which the accepted docstring of
`control_not_minimal` stated but its statement did not. It comes with the witness `notMinWitness` and the lemma
`nd_notMin`. `C2` and `C3` add general forms of five of their lemmas (2026-10-13), which the old lemmas hid and the
paper states: `pkCh_lift_explicit` names the separator that `pkCh_lift` only asserts to exist; `pkCh_sideR` and
`pkCh_sideL` are the side lemma for any chord of `𝒮_B` (with `pkCh_sideLeg`), of which `pkCh_oddBelowR` and
`pkCh_oddBelowL` are the innermost case; `pkCh_tailAsc` and `pkCh_tailSep` give the separator of `pkCh_tailLin`
explicitly, and `pkCh_thinLinRuns` adds to `pkCh_thinLin` the oddness of the separator, its extreme legs and the
single-even-leg runs. Each old lemma is now proved from the new one; its statement is unchanged. `NonVacuity` (merged
into `PaperTests` since), `Paper` and `PaperTests` are new ([below](#new-module-nonvacuity), [and](#new-module-paper),
[and](#new-module-papertests)).

## Removed declarations

Three statements with a `sorry` proof, outside the closure of Theorem Π (no other declaration used them; the axioms in
`Verify.lean` show that no result depends on `sorryAx`), are deleted rather than proved or kept with a `sorry` (owner
decision, 2026-10-06):

- `ChainSlice.eq_coordPt_of_onE`: every point of the locus `L_E` is the point `coordPt` of its own coordinates (the
  "interval formula"); the definitions `sInt` and `coordPt` stay, proved lemmas use them;
- `ChainSlice.minimal_zero_iff`: among the sets of tiles `E ⊆ S` (`ChainSlice`'s term), the minimal zero sets are
  exactly the `E ∪ D(a,b)` (marked optional, off the main theorem's closure, in the accepted text);
- `PionNLSM.NLSM_ne_zero`: `NLSM_N` is not identically zero for every even `N ≥ 4` (marked optional). The witnesses
  `NLSM_ne_zero_small` (`N = 4, 6`) and `theoremB_hyp_inhabited` stay, and `exists_NLSM_ne_zero` (`NonVacuity`) proves
  the statement for even `N ≥ 6`.

## Statement changes

Ten helper theorems, none cited by the paper, drop instance arguments that their statements do not use; Mathlib's
linters (`unusedDecidableInType`, `unusedArguments`) report such arguments. The proofs start with `classical` where they
need decidability; no caller passed the dropped instances explicitly, so no caller changed. Two theorems the paper
cites drop a hypothesis their proofs never used, `S ∈ F^π`: `can_exists` (2026-10-12), so that it holds for every set
`S` of pairs with `𝒫₁ ≠ ∅`, as the paper states, and `int_of_bot` (2026-10-13), part of the paper's Proposition 7.5
("No hypothesis on `S`"); the one caller of each (`C3`; `chain_interval` for `int_of_bot`) changed accordingly. The
statement check reported each drop by argument position, pinned with the module's summary.

| theorem | module | dropped |
|---|---|---|
| `pkRw_decomp` | `PionNLSM` | `[DecidablePred A]`, `[DecidablePred B]` |
| `labZ_legZ` | `C0` | `[NeZero N]` (also unused by its proof) |
| `pkG_avoid`, `pkG_avoid_locus` | `C4` | `[DecidableEq ι]` |
| `pkG_Xpow_dvd` | `C5` | `[DecidableEq α]` |
| `pkR_prodDiv_aux`, `pkR_prodDiv`, `pkR_avoid_aux`, `pkR_avoid` | `C5` | `[DecidableEq ι]` |
| `pkR_d2_primeFin` | `C10` | `[DecidableEq ι]` |
| `can_exists` | `C2` | `(hF : InFpi N S)` |
| `int_of_bot` | `C3` | `(_hF : InFpi N S)` |

## Transformations

The same steps were applied to every module.

1. *Module, namespace, imports.* Copyright header and `module` added; namespaces renamed (above). `import Mathlib` and
   the accepted text's imports of whole earlier files were replaced by the Mathlib modules each file needs (for the
   library files, `#min_imports` and leave-one-out builds). `C0` also imports `Mathlib.Algebra.Field.ZMod`: without it,
   the statement of `labZ_parity` elaborated `Ring (ZMod 2)` through `ZMod.commRing 2` instead of the accepted text's
   field instance; the two are equal by definition, but the statement check compares terms exactly, and with the import
   the port elaborates the accepted term.
2. *Warnings* fixed; `lake build --wfail` is clean with the project's linter options: deprecated names (`if_pos` →
   `ite_eq_left`, `if_neg` → `ite_eq_right`, `push_neg` → `push Not`, …), `show` that changes the goal → `change`,
   unused `simp` arguments, tactics that never ran, `<;>` where `;` suffices, and lines over 100 characters wrapped (by
   a script checked to change whitespace only, then by hand). Unused hypotheses of statements are renamed `h` → `_h`,
   never removed, so the statements are unchanged.
3. *Heartbeats.* Each `set_option maxHeartbeats` was measured with `#count_heartbeats in` and set to Mathlib's
   suggestion with the reason and the count in a comment, or removed when the proof needs no raise; two keep a slightly
   higher value for headroom (`pkL_noSign_core` in `C0`, `pkR_d2_OT` in `C10`).
4. *`#print axioms`* lines moved from the ends of the modules (and the accepted text's final axiom report) to
   `Verify.lean`.
5. *Docstrings and section headings* rewritten to describe the file as it is; each module has a new module
   docstring, and definitions without a docstring got one (Mathlib's `docBlame` linter). Status markers that are no
   longer true ("PROVED", "ASSEMBLED", "`sorry`", "target", "frozen", TODOs) are dropped: every declaration is proved.
   Terms follow `C0`: "mixed chord" or "odd diagonal" became "odd chord", "tile" became "pair" or "mesh variable".
   Research labels used as titles were replaced by descriptions. The declaration names `lemma65`, `lemma14_6` and
   `prop14_7` carry the numbering of earlier drafts and are kept. Changed on 2026-10-19: in `C0`–`C5`, `C8`, `C10`,
   `ChainSlice` and `PionNLSM`, the labels the docstrings define (`Sep_all`, `runcut`, traces, (Even-top′), (b0),
   `F^π`, the germ input, the M2 and M3 forms, Theorem I, the row locus, …) are glossed with the paper's words where
   they are defined; "canonical chord" became "innermost chord"; citations of an earlier draft's supplement were
   removed from `C1` and `C3`, and "massless" from `C8`.
6. *Docstrings corrected.* A docstring that said more than, or other than, its statement was corrected to say what the
   statement proves; hypotheses that docstrings left out were added. The statements were not changed. The corrections
   that change what a reader would take the result to say:
   - `C3`: `int_of_bot`, `chain_interval` (the class lies between the heads of `b` and `t`, containment, not equality
     with an interval); `int_of_bot`, like `can_exists` (`C2`), did not use its hypothesis `S ∈ F^π` (`InFpi`, `C0`),
     since dropped from both ([Statement changes](#statement-changes));
   - `C4`: `pkG_gen_A4`, `pkG_gen_A5`, `pkG_G4`, `pkG_G4_e`, `pkG_V_base`, `pkG_V_leaf`, `pkG_G3_clean`, `pkG_E_zero`,
     `pkG_gov_map`, `pkG_See_F`, `pkG_mesh_sh`, `pkM_base4`, `pkM_c1_ind`, `pi_clause1_M2`, `cl2a_M2`, `prop14_7`,
     `minimal_iff_of`, `pi_minimal_iff_M2`, `ResChildInput` (now spelled out in full);
   - `C5`: `pkG_sh_ne_ct`, `pkGNum`, `pkGRowZ`, `pkG_rowZ_of`, `pkG_zres`, `pkG_dvd3`, `pkG_num_res`, `pkR_div`,
     `pkR_STnum`, `pkR_resNum`, `pkR_prodDiv`;
   - `C6`: `pkR_collapse`, `pkR_planar_gram`, `pkR_fh_planar`, `pkR_fh_mesh`, `pkR_fh_sp`, `pkR_ZT_evens`,
     `pkR_rk_lam`, `pkR_rk_W`, `pkR_rk_ne`, `pkR_rk_mz`, `pkR_rk_mnz`, `pkR_rg_mr`, `pkR_rg_sp`, `pkR_rg_x`,
     `pkR_rg_xp`, `pkR_rg_vanM`, `pkR_rg_term`, `pkRRG`, `pkRBCross`, `pkR_XQ_pt`, `pkR_XQ`, `pkR_Wind1`,
     `pkR_Wind2`, `pkR_GW_star`, `pkR_GW_starp`, `pkR_Gq`, `pkR_GW_Q`, `pkR_single`;
   - `C7`: `pkR_b_F_erase` (the direction was reversed), `pkR_b_F_glue`, `pkR_b_cross_not_sub`, `pkR_b_chain`,
     `pkR_b_R17`, `pkR_b_blk_pos`, `pkR_b_om_blk`, `pkRBOmI`;
   - `C8`: `pkR_lam_ofC`, `pkR_rotG_NP`, `pkR_childA`, `pkR_childB`, `pkR_b_R5c2`, `pkR_b_R2top`, `pkR_b_R2bot`,
     `pkR_wxA`, `pkR_wxB`, `pkR_wxC`, `pkR_b_primeProd`;
   - `C9`: `pkR_b_R2A`, `pkR_d2_cross_nsub`, `pkR_d_Havoid`, `pkR_ch_W`, `pkR_om_count`, `pkR_d2_part`, `pkR_ch_row`,
     `pkR_omega_ind`, `pkR_d2_countH1`;
   - `C10`: `pi_clause1`, `pi_clause2`, `pi_minimal_iff` and `cl2a` (now with "for even `N ≥ 6`" and the predicates
     they prove), `control_empty`, `control_not_minimal`, `ctl8_neg`, `S8B` (maximality is not checked in Lean),
     `S8N`, `pkR_d2_W_self`, the controls `min_*`, `notZero_*`, `nd_*`, `zero_*`, and the shared docstrings of
     `rev_card6`, `rev_head`, `rev_tri12`, `ctl8_route`, now split, one per theorem.

   Corrected after the port (2026-10-13): `C1`'s `pkTRemT`, `pkTRemS` and `pkTZoneSet` were described as the reach
   sets `Z_X`, `Z_Y` and the reach witness `(τ ∖ Z_X) ∪ (σ ∖ Z_Y)` of the walk-based proof of the three-separator
   lemma. No relation with those walk-defined sets is stated or proved, and outside the zone case they can differ; the
   docstrings now say that these are the removal rules and the zone set `G′` of the walk-free proof (Supplement S6).
7. *Toolchain.* `v4.34.0-rc2` → `v4.34.1` (Lean and Mathlib tags). The bump changed no proof; its deprecation warnings
   are fixed under item 2. Later bumps: [Toolchain](#toolchain).

Build of the port, per module of the chain (laptop, the project's options; the method varies by module): 32–252 s
and 1.9–7.1 GiB maximum resident memory, against 58–281 s and 6.3–8.3 GiB for the accepted copies on the same
toolchain.

## Toolchain

The project follows the stable releases of Lean, with the matching Mathlib tag. Bumps after the port:

**`v4.34.1` → `v4.35.0`** (2026-10-26). No statement or definition changed (the diff edits proofs only); each of the 544
pins `Statements.lean` had before the bump printed the same text on both toolchains, and `Verify.lean` finds no axiom
beyond Lean's standard three, as before. Proofs changed where the new toolchain rejected them:

- `PionZeros`: the 14 `decide` proofs `quads_8_0` … `quads_8_11`, `card_quads_small` and `alternating_eight` exceed
  Lean's default recursion depth (512); each now runs with `set_option maxRecDepth 1024 in`.
- `ChainSlice`: in `pkE_tele`, two `try omega` after `simp` no longer do anything (the `simp` closes the goal) and are
  removed.
- `C0`, `C1`, `C4`: six steps that restated a goal as the body of a definition (`change`) ran out of heartbeats while
  checking that the two forms agree; they now unfold the definition instead (`unfold sepPairs` twice in `C0` and once
  in `C1`, `unfold sepIn`, `unfold innerEE`, `dsimp only [pkGSplit]`).
- `C9`: `pkR_d2_omegaQ` needs 641,724 heartbeats (359,986 before); its budget is 800,000 (was 400,000), set as in
  item 3 of [Transformations](#transformations).

**What this bump dropped.** The statement check (above) no longer runs: the verbatim accepted copies do not compile on
`v4.35.0` (in `C0`, two `show` steps run out of heartbeats, also with 1,600,000 heartbeats and with either of Lean's
`backward.isDefEq.*` compatibility options), and editing them would break their hashes ([The accepted
files](#the-accepted-files)). Its last run, on `v4.34.1`, found every module equal to the accepted text as described
above; that was the Lean of this project just before the bump. With the check, the rule it enforced is dropped too: from
this bump on, the base modules and `C0`–`C10` may change statements and definitions in place, like any library code. The
rename map's `-` and `~` lists, [Removed declarations](#removed-declarations) and [Statement
changes](#statement-changes) record the port up to this bump. What is still checked mechanically: `Statements.lean` pins
the statements of Theorem Π; every declaration of `Paper`, `PaperTests` and `Conventions`; the library definitions that
`Paper`'s definitions are matched by, and the ten that only its helper statements read; and nine library theorems the
paper cites (the last two groups added at this bump). A pin fixes the printed text of a statement or of a definition's
body, not the definitions that text names unless they are pinned themselves: the definitions those use (among them the
amplitude's, in the base modules) and 38 library declarations the paper cites (some of them among those definitions) are
not pinned. `Verify.lean` checks the axioms. No check compares the other declarations of the library (most of the 2,227
the statement check compared) with the accepted text any more; a change to them is seen only in review.

## New module: `NonVacuity`

`PionCompleteness/NonVacuity.lean` was **not part of the accepted text**. It was added by the port (2026-10-10) so that
the release shows that Theorem Π is not vacuous for every even `N ≥ 6` (the controls of `C10` check this at `N = 6, 8,
10, 12` only). Its statements come from an AI statement audit of the accepted text (model `claude-opus-5-5`; the audit
itself was not reviewed by a person), where two of them took clause 1 or `cl2a` as a hypothesis; here they use the
proved theorems (`pi_clause1`, `cl2a`), so they hold outright. `exists_NLSM_ne_zero` is new: `NLSM_N ≠ 0` at a rational
point where no odd chord vanishes, for even `N ≥ 6`. There is no accepted module to compare with; the module was
reviewed like the others (four review agents, then merged by the author), and its 6 results are in `Verify.lean`.
Added 2026-10-13: `empty_mem_gFamily_of_odd` (`∅ ∈ 𝒢_N` for every odd `N ≥ 3`) and `containsGMember_of_odd` (so for odd
`N` every `S` contains a member of `𝒢_N`), which show why clause 1 needs `Even N`: without it, the statement would hold
at odd `N` for this reason alone. With them, 8 results are in `Verify.lean`; every declaration is pinned in
`Statements.lean`. Made with Claude Code (model `claude-opus-5-5`).
Added 2026-10-19, with Theorem 3.1 in the paper's terms (module `Paper`, below): the same facts for it, through the
equalities proved there (`not_isListMember_empty`, `not_isCoordinateZero_empty`, `isListMember_sepPairs_one_three`,
`isRegularCoordinateZero_sepPairs_one_three`; the odd-`N` facts have no counterpart, as the statements assume even
`N`); the module now imports `Paper`, so it builds after it. With them, 12 results are in `Verify.lean`. Made with
Claude Code (model `claude-opus-5-5`).
Merged into `PaperTests` on 2026-10-26, its declarations renamed (below).

## New module: `Paper`

`PionCompleteness/Paper.lean` is **not part of the accepted text**. It was added on 2026-10-12 so that each claim of the
paper has a Lean declaration that states it exactly: the same hypotheses and the same conclusion, in the paper's form,
so that a reader can compare the two side by side without an argued step between them. Its statements were found by
comparing each claim of the paper with the Lean statements and the definitions they use (AI side-by-side reads, model
`claude-opus-5-5`, checked by the author's AI session, same model); most are short consequences of the general results
of `C0`–`C10` and the library files, which stay general (one of them, `can_exists`, lost an unused hypothesis, above;
so did `int_of_bot`, which `Paper` does not use).
Where the general result and the paper differed, either a statement was added here or the paper's wording changed (where
the Lean form was the one reviewed in the research, or the clearer one). The statements therefore follow the paper of
record, which differs from earlier versions of the paper, in its lemmas and theorems, in eleven places: the order count
counts the faces with at most one chord side outside `𝒫₀`; the face identity has that hypothesis and states its display
with `U_f` and its complement (the sink and source values move into the proof of the sink and source walk); the
first-order term's expansion `G_S` is a remark, not part of the theorem, and not formalized; the sink and source walk
says `V_h ≡ 0` on `L_S` (equivalently, `V_h` in the span of the missing mesh variables); the non-vanishing of `NLSM_N`
when `𝒫₁ = ∅` is stated for `S ∈ F_N`; the linked member of the innermost class drops the redundant hypothesis `𝒫₁ ≠ ∅`;
the symmetry of `NLSM_N` among the analytic facts is stated for the rotations of the legs (invariance under a reflection
and under `v₀ ↦ −v₀` is a remark of the paper, not formalized); the momentum reading of the parity form, `E = −(Σ_even
p)² = −(Σ_odd p)²`, is a remark after the lemma on momentum conservation, not formalized (there are no momenta in the
Lean; its content in mesh language is the block-sum identity `E = −Q_evens = −Q_odds`); the three-separator lemma states
the single-family form of the walk-free proof (Supplement S6), which is the proof of record, with (Tri) as its corollary
(the walk-based lemmas of the earlier proof are not part of the record); the lemmas of the zone case of S6 assume "`τ`,
`σ` odd and not (EP)" (earlier: "not (EP)", under which the gap lemma is false for an even singleton); the coarse
translation lemma "(Tri) ⇒ (Bot)" is flattened: (Bot) is stated directly, its proof using the three-separator lemma. Its
definitions also change: in the definition of dissections, `Σ_f(|f| − 2) = N − 2` becomes a remark and the orientation
of the chords (in- and out-chords, sinks, sources) moves into the proof of the sink and source walk; `ε_N :=
(−1)^{(N−2)/2}` is defined directly and `∏_f sgn_f = ε_N` is a remark; the "equivalently" in the definition of `𝒢_N` is
a remark. The paper's "`S` is a zero" (an identity of rational functions) is `RatZeroOn`; the library's pointwise form
is equivalent for non-degenerate `S` (`ampZeroOn_iff_ratZero`). Definitions state notions of the paper that the library
had only in another form: the faces of a dissection (`IsFace`, `faces`: the maximal sets of vertices no two of which a
chord of the dissection separates; the library indexes faces by a root side, and `isFace_iff` and `faces_eq_image` prove
that the two agree, one face per root side), the legs of the sides of a face that start at an odd vertex (`sideStart`,
`oddStartLegs`) and its chord sides (`chordSides`), the paper's vertex of a face (`faceVertex`; the library's `pkGV`
uses the face's own class, equal by `pkG_V_eq_faceVertex`), `cayleySum` (the Cayley sum, over any field, a sum over
faces) and `meshMap` (the map `X ↦ (c_t(X))_t` as a linear map, for the rank in the lemma on momentum conservation).
There is no accepted module to compare with; every result is in `Verify.lean`, and the module was reviewed by AI review
agents (two rounds, four agents in the first), then merged by the author. It covers part of the paper so far; the other
claims follow.

Extended on 2026-10-13 with the analytic facts, the transversal form of candidate sets, the block sums, the parity
form, the top and bottom of a flank class, the single-leg zeros and Supplement S2's lemmas; and, the same day, with
the linear algebra of the mesh (the kernel, relations, rank and image of the mesh map; coordinates on a locus), the
flank sets, the odd planar variables on the base locus, and the members of `𝒢_N` (non-degenerate, zeros, linearly
closed). A residue of the paper, `Res_{X_C=0} F := (X_C F)|_{X_C=0}`, is stated as
`RatZeroOn {x | x C = 0} (X_C · F − G)` for `Res_C F = G`; the lemma `ratZeroOn_hyperplane_iff_zeroAt` proves the step
from the library's numerator form (`zeroAt`) to this rational form, which the research text had argued in words.

Extended again on 2026-10-13 with the readable faces of a dissection above and the claims inside the definitions of an
odd chord's sides (two arcs of odd size at least three; a chord is determined by its odd-ended side) and of dissections
(face count `|D| + 1`, at least four and an even number of vertices, alternating parities), the face identity, and the
identities of the forms of Supplement S1.1 (with the linear independence of mesh variables omitting a same-parity pair,
from the relations of the mesh map); the order count and the sink and source walk are now stated with these faces. The
library definitions behind the paper's coordinate loci and zeros, `S_G`, `𝒢_N`, dissections and admissible separators,
minimal zeros and the forms `Q_U`, `E`, `Σ^{ee}`, `Σ^{oo}` are pinned in `Statements.lean`.

Extended once more on 2026-10-13 with the three-separator lemma in its single-family form and (Tri), the lemmas of its
walk-free proof (Supplement S6: the block lemma, the gap lemma, the convexity and size of the zone set `G′`, the zone
lemma) and the absorption lemma. Supplement S6's case (EP) and zone set `G′` are definitions here (`CaseEP`,
`HasWideGap`, `zoneSet` with its removal rules `RemovedTau`, `RemovedSigma` and the conditions `PX`, `PY`), equal to the
library's inline form by `zoneSet_eq_pkT_zoneSet` (for legs `≥ 1`, as in the setting). The configuration of the paper's
Figure 9 shows that the hypotheses of the zone case can hold together (`figure_nine_configuration`). The library
definitions of the setting (`ThreeSepSetting` and its parts, `runSepA`, `threeSepCut`, `ConsecWit`) and the flank class
`hitClass` are pinned in `Statements.lean`.

Extended a fourth time on 2026-10-13 with the class residue in the paper's language of rational functions
(§7.3–§7.4), which the library states for numerators, pointwise. "The restriction of `f` to `L_S` is regular at generic
points of `H = L_S ∩ {x = 0}`" is `RegularAlong` (on `L_S`, `f = P / D` with `D` not identically zero on `H`) and
"`f|_H = 0`" is `RestrictsToZeroAlong` (the value does not depend on the representation on
`L_S`, `restrictsToZeroAlong_numerator`); `regularAlong_can_fail` shows that `1 / x` is not regular there, so the first is a
condition. The amplitude avoiding a set of chords, `N^{¬K}`, is defined as the paper defines it (`nlsmAvoiding`) and
related to the library's numerator by `nlsmAvoiding_numerator_hom`. Definition 7.8's hypotheses are a structure
(`FlankClassPoleHypotheses`, with `residueHyperplane`, `stripHalfLength`, `childAmpB`, `childAmpA` for `H`, `d`, `a_t`,
`b_b`), with the lemma that they make `K` the flank class of its top, the two remarks after the definition as lemmas,
and the paper's Example 4.6(b) as an instance with a class of two members (`example_four_six_residue_regime`). Lemma
7.15 (`only_extreme_term_survives`) follows, and in Example 4.6(b) the cases it excludes do fail: the extreme terms do
not restrict to zero on `H` (`example_four_six_extreme_terms_nonvanishing`); its third part uses a new lemma (`region_diag_not_member`: no odd
diagonal of the region `Ω(Q, Q′)` other than the members strictly between `Q′` and `Q` is in `K`, which the library had
only for the region between the top and the bottom). The library definitions these definitions are read through or
assume (`relab`, `npair`, `pkRBPull`, `pkRSubX`, `pkRBOmL`, `pkRBOlo`, `pkRBOmM`, `InFpi`, `ContainsGMember`)
are pinned in `Statements.lean`.

Extended a fifth time on 2026-10-13 with the rest of §7 and of Supplement S1.2, in the same language: the descent and
containment lemmas of §7.1 (`descent_to_smaller_side`, `odd_side_nesting` and its mirror); the grouping lemma as a
one-chord recursion of rational functions (`grouping_identity`, `nlsmAvoiding_step`), from the library's numerator
recursion and a split of the product of the odd chords at the chord; the chains of a class
(`flank_class_members_form_chains`); the collapse identity (`collapse_identity`), by iterating that recursion top-down
over the class and bottom-up inside the A-side polygon of each member; the class residue and the value of the strip
factor (`simple_pole_along_flank_class`, `strip_factor_value`); the strip regions in mesh language (`strip_regions`);
the corner identity for a polygon with side values (`planarWithSides`, `meshWithSides`, `corner_identity`); the ear
lemma on a readable locus (`earLocus`, equal to the library's by `earLocus_iff`;
`polygon_numerators_vanish_on_ear_locus`); the children of an odd chord (`children_of_odd_chord_locus` and its
companions; the restriction to a child maps the locus with `X_P = 0` into the child's locus, `child_onLocus`, which the
library had only for the other inclusion); and, on the universal polygon of the supplement, the Gram model, the
genericity clauses and the value on the universal locus (`gram_model`, `genericity` and its companions,
`polygon_numerator_value`, with an instance where `I` is not empty, `universal_locus_nonvacuous`). The paper of record
changes with them. The descent lemma concludes `|B_Q| < |B_P|`, and its mirror is a remark. The grouping lemma is the
one-chord recursion, and the general sums over non-crossing sets leave the paper. The collapse identity assumes
(H1)–(H4). The strip regions, corners and ear lemma are in mesh language (no momenta). For the 4-gon, where one mesh
variable straddles two sides, the corner identity adds both side values. The ear lemma's `N^{¬K}(𝖯_Q) ≡ 0` is a step of
its proof; the Lean statement does not assume that the set of chords contains the one cutting off `R`. The class
residue, the value of the strip factor and the value on the universal locus are stated with a non-zero constant, and
`(−1)^d` is a remark, not formalized. The parts of the supplement's Gram model and genericity lemmas that serve only its
own proof of the value on the universal locus are not formalized; the library proves that theorem another way. The
library definitions of the universal polygon these statements read (`pkRLam`, `pkRMinrect`, `pkRHead`, `pkRIsMem`,
`pkRClosed`, `pkRMchord`, `pkRW`, `pkRCstp`, `pkRTau`, `pkRGramPt`, `pkRArcX`), of the children (`ChildPairIn`,
`childSetA`, `childSetB`, `NonzeroOn`, `pkRBChildB'`), the members below a member that the collapse identity reads
(`pkRD2Below`) and the rotation `rot` are pinned in `Statements.lean`.

Extended a sixth time on 2026-10-13 with §8.3, the translation to combinatorics. The runs of Definition 8.0 are
definitions here (`IsRunOf`, for any arc, `IsOccupiedRun`, `IsSpread`, and the piece `R_τ` as `reachPiece`), with the
fact the definition states (each pair of `o_in(P′)` lies in one run, `inner_oo_pair_in_one_run`) and their relation to
the library's `Spread` for a set of legs (`isSpread_iff_spread`; for an arbitrary set it fails, since a number that is
not a leg can share a leg's position); the paper's Example 8.C is an instance (`example_eight_c_spread`), and the
hypotheses of the shortening hold together (`example_shortening_nonvacuous`). The run chords (`occupied_run_chords`),
the sub-arc lemma (`separated_pairs_of_sub_arc`), the shortening (`shortening_spread_separator` and its mirror, proved
along the paper's steps (1)–(3), step (4) by another argument), (NoSpread) (`innermost_chord_has_no_spread_separator`),
the side lemma (`unlinked_side_has_smaller_linked_chord` and its mirror), the corollary on odd singletons
(`no_odd_singleton_separator`), the thin runs (`thin_runs`) and the lift (`spread_separator_passes_to_innermost_chord`)
follow: the side lemma, the thin runs and the lift from the general forms added to `C2` and `C3` (above), the corollary
from the side lemma. The paper of record changes with them: the runs are defined for any odd chord; the sub-arc lemma
assumes `L ⊊ C_N` (it is false for `L = C_N`); (NoSpread) drops the redundant `𝒫₁ ≠ ∅`; and the fine translation lemma
is part of the proof of (NoSpread), not a numbered statement. Since 2026-10-29 the lift is stated in the paper's
general form (an on-shell chord inside any odd chord, spread as `IsSpread`), proved from `pkCh_lift_explicit`; its name,
kept for the registry key, is that of the special case it stated before. The Lean proves (NoSpread) through the library's linear
encoding, not through the statements of the run chords and the shortening above. Statements whose library form already
matched are restated here too, so that each claim has a pinned declaration in this module: the two parts of Theorem 3.1
(`every_coordinate_zero_contains_a_family_member`, `minimal_coordinate_zeros_are_the_list`; since 2026-10-19 in the
paper's terms, below), the chord formula (`chord_formula`, with the parity form `E` where the library has the sum over
the missing even pairs, equal on the locus), proportionality (`proportional_odd_chords_share_missing_flank_set`), the
antichain (`separated_pair_family_is_antichain`) and the quartic rules (`quartic_rules_give_nlsm`, `Q^π_N = 𝒜_N`, where
the library states `σ_N · NLSM_N` with the same sign). `NLSM` is pinned in `Statements.lean`.

Extended on 2026-10-19 with the gap lemma's parts (b)–(d) as statements of their own, each in the setting and the zone
case: the removal rules in the form "a leg of `τ` (of `σ`) is removed if and only if `X` (`Y`) is exposed and …"
(`removed_leg_of_tau_iff`, `removed_leg_of_sigma_iff`; the first holds for any number `t`, not only legs of `τ`), the
four side gaps (`side_gap_gamma_sigma`, `side_gap_gamma_tau`, `side_gap_left_sigma`, `side_gap_right_tau`) and the
legs that are always kept (`zoneSet_keeps_middle_legs`, `zoneSet_keeps_common_legs`). They restate library lemmas of
`C1` (`pkT_remT_PX`, `pkT_remS_PY` and the converses `pkT_remT_of_A`, `pkT_remT_of_B`, `pkT_remS_of_A`,
`pkT_remS_of_B`; `pkT_WgY`, `pkT_WgX`, `pkT_WlY`, `pkT_WrX`; `pkT_mid_G`, `pkT_notBoth`), which the paper cited
before, so that each claim of the paper has a pinned declaration in this module.

Changed on 2026-10-19: **Theorem 3.1 in the paper's terms.** The three statements of Theorem 3.1
(`every_coordinate_zero_contains_a_family_member`, `family_members_are_minimal_zeros`,
`minimal_coordinate_zeros_are_the_list`) were restated with definitions shaped like the paper's: `IsRegularSet` ("no
planar variable vanishes identically on `L_S`"), `IsCoordinateZero` (`NLSM_N` restricts to the zero rational function on
`L_S`, `RatZeroOn`, where the statements had the pointwise `AmpZeroOn` of `𝒜_N = (−1)^{N/2−1} NLSM_N`),
`IsRegularCoordinateZero`, `IsMinimalCoordinateZero`, `IsCausalDiamond` and `IsListMember` (the list as the paper
defines it: the causal diamonds and the `S_T` for at least three legs of one parity, where the statements had `gFamily`,
the `S_T` for at least two legs and the causal diamonds `S_{a,b}` with `a`, `b` of opposite parity). Each definition but
`IsCausalDiamond` (covered through the list's equality) is proved equal to the library's, under the statements'
hypotheses (no hypothesis for regularity; even `N ≥ 4` for zeros and minimal zeros, and a regular set of pairs for a
zero; even `N` for the list) (`isRegularSet_iff_nondeg`, `isCoordinateZero_iff_ampZeroOn`,
`isRegularCoordinateZero_iff_isNDZero`, `isMinimalCoordinateZero_iff_isMinimalZero`, `isListMember_iff_mem_gFamily`),
and the three statements are proved from `pi_clause1`, `pi_clause2` and `pi_minimal_iff`, which do not change. Clause 2,
as before, does not state that each member has a point of its locus with every planar variable non-zero (`NonDegPt`):
the paper does not state it, and `pi_clause2` does. Added with them: the paper's lemma that a zero can be read pointwise
(`isCoordinateZero_iff_pointwise`) and the size of the list at eight legs, 30 (`list_eight_card`, computed). The
definitions in the statements of Theorem 3.1 (their closure up to Lean and Mathlib) went from 37 definitions, 105 lines,
to 28 definitions (and one proof Lean generates), 92 lines. Made with Claude Code (model `claude-opus-5-5`).

Changed on 2026-10-19: **the other statements in the paper's terms.** A definition of candidate sets as the paper
defines them was added, `IsCandidateSet` (a regular set of pairs containing no member of the list), proved equal to the
library's `InFpi` for even `N` (`isCandidateSet_iff_inFpi`). Every statement of this module that named `InFpi`,
`gFamily`, `IsNDZero`, `IsMinimalZero` or `Nondeg` was restated with the paper's definitions, among them the hypotheses
of the residue theorem (`FlankClassPoleHypotheses`, whose field `candidate` is now `IsCandidateSet`); only the
equalities between the two forms still name the library's. The quartic rules and the lemma on the NLSM side state `Q^π_N
= (−1)^{N/2−1} NLSM_N` and `NLSM_N` where they had `𝒜_N = (−1)^{N/2−1} NLSM_N`. The sizes of the children of an odd
chord and the children's candidate sets are stated for every odd chord (the paper states them for a residue chord; the
proofs use only that the chord is odd). The lemma that only the extreme term survives states the paper's two claims; the
third part it also stated, that every strip factor has no pole along `H`, is the lemma `stripFactor_hasNoPoleAlong`.
Renamed, for the paper's words: `RegularAlong` → `HasNoPoleAlong` ("has no pole along `H`"; "regular" is the paper's
word for sets of pairs), with `RegularAlong.add` → `HasNoPoleAlong.add`, `RegularAlong.mul` → `HasNoPoleAlong.mul`,
`regularAlong_can_fail` → `hasNoPoleAlong_can_fail`, `not_regularAlong_inv` → `not_hasNoPoleAlong_inv`,
`regularAlong_of_eq` → `hasNoPoleAlong_of_eq`, `regularAlong_const` → `hasNoPoleAlong_const`, `stripFactor_regularAlong`
→ `stripFactor_hasNoPoleAlong`, `RestrictsToZeroAlong.regularAlong` → `RestrictsToZeroAlong.hasNoPoleAlong`;
`universal_locus_nonvacuous` → `marked_locus_nonvacuous` and `universalLocus_mono` → `markedLocus_mono` (the paper's
marked locus); `o_clean_pole_chord_joins_innermost_flank_class` → `residue_chord_joins_innermost_flank_class`;
`odd_chord_vanishing_on_base_locus` → `odd_chord_vanishing_on_same_parity_sublocus`;
`base_dissection_has_vanishing_face` → `on_shell_dissection_has_vanishing_face`; `leading_term_at_base_point` →
`nonvanishing_without_residue_chords`; `flank_sets_and_evens_by_odds_block` → `flank_sets_of_odd_chord`;
`chord_families_on_base_locus_clean_iff` → `on_shell_iff_flank_sets_share_no_missing_pair`;
`gFamily_two_same_parity_pairs_outside` → `list_member_two_same_parity_pairs_outside`. The docstrings of this module no
longer cite the numbers of an earlier draft of the paper; the library's own labels are glossed with the paper's words
where they are defined (`C0`). Made with Claude Code (model `claude-opus-5-5`). Added 2026-10-22: the members of a
child's list inside the child set, for any set of pairs and any odd chord. Without the new leg, a set `T` of child legs
is a leg set of the child's list iff its legs in the `N`-gon are one of the `N`-gon's, and the child set contains `S_T`
iff `S` contains their separated pairs (`child_zeros_away_from_new_leg`); with it, the legs in the `N`-gon of the rest
of `T` are an admissible separator, and the child set contains `S_T` iff that separator is free, so a side is linked iff
the child set contains no such `S_T` (`child_zeros_at_new_leg`). Two consequences: an unlinked side's child set contains
a member of the child's list, and for `m ≥ 6` `NLSM_m` vanishes at every point of its locus at which no odd planar
variable vanishes (`unlinked_side_child_vanishes`); a residue chord with both sides linked is alone in its flank class,
and an innermost chord has a linked odd-ended side iff its class has one member
(`both_sides_linked_alone_in_flank_class`). An example at `N = 8`, checked by `decide`, has two residue chords, neither
with both sides linked (`example_no_residue_chord_with_both_sides_linked`). Their general forms for one side are new in
`C2` (`pkCh_child_zero_nohat`, `pkCh_child_zero_hat` and the lemmas before them), and `pkCh_child_nf`, `pkCh_tr_hat`,
`pkCh_tr_nohat` are now proved from them, statements unchanged; `pkCh_tr_mixed` and `pkCh_tr_in` are kept, no longer
used. 5 results in `Verify.lean`. Made with Claude Code (model `claude-opus-5-5`).
Added 2026-10-23: the image of the cut at an odd chord, for any set of pairs, any odd chord and either side `D`. The cut
equation is the child's momentum conservation read in the parent's mesh variables (`cut_relation`); the cut image lies
in the child's coordinate locus and is all of it when `D` has an absorber (a missing same-parity pair with both legs
outside `D`, or an end leg of `D` and a leg outside, or two missing pairs of one leg of `D` that is not an end leg with
legs outside `D` of opposite parity) or no missing pair is of one parity (`cut_image_onto`); otherwise, when `X_P` does
not vanish identically on `L_S`, it is the hyperplane of that locus on which the form with the weights `cutWeight`
vanishes (`cut_image_hyperplane`); for an odd chord, every pair of `e_in(P)` is an absorber of `A_P` and every pair of
`o_in(P)` one of `B_P` (`cut_absorber_of_inner_pair`), so both sides of a residue chord have one
(`cut_absorber_of_residue_chord`). An example at `N = 8`, checked by `decide` and the hyperplane statement, has an
on-shell chord whose even-ended side has no absorber although its child set is a candidate set
(`example_cut_image_hyperplane`, with `example_cut_image_hyperplane_candidates`). The proofs number the legs from the
side's first leg and use the kernel and the image of the mesh map (`momentum_conservation_relation`, `mesh_kernel`); no
earlier declaration changes. 46 results in `Verify.lean`. Made with Claude Code (model `claude-opus-5-5`).
Added 2026-10-23: short arguments of the paper's remarks on its definitions and main theorem. A regular set of pairs
containing a zero is a zero, every regular coordinate zero contains a minimal one, so a regular set is a zero exactly
when it contains a minimal zero (`isCoordinateZero_of_subset`, `exists_minimal_coordinate_zero_subset`,
`isCoordinateZero_iff_contains_minimal`). With `nextCut N G g`, the leg of `G` after `g` cyclically (numbered past `N`
where the gap wraps around): a set of legs has one parity iff the gap after each of its legs holds an odd number of
legs (`one_parity_iff_gaps_odd`); two legs of opposite parity have even gaps and a causal diamond with odd corners
(`opposite_parity_gaps_even`); a causal diamond `S_{a,b}` inside `S_G` forces `G ⊆ {a, b}`, so `S_T` with `|T| ≥ 3`
contains no causal diamond (`subset_pair_of_causal_diamond_subset`, `no_causal_diamond_in_separated_pairs`); `S_G` is
the union, over two legs `g < h` of `G`, of the tiles of (gap after `g`) × (gap after `h`), each block a range of tiles
of the form of `ChainSlice.diamond`, and for two legs it is that diamond (`separated_pairs_eq_blocks`,
`separated_pairs_block_tile`, `separated_pairs_of_two_legs_eq_diamond`). An example at `N = 6` is a candidate set
with no residue chord on whose locus `NLSM_6` equals the parity form at every point off the poles
(`example_pole_free_locus_six`) and as rational functions (`example_pole_free_locus_six_rational`). For a member of
the list, the parity form vanishes identically on its locus exactly when it is one of the two whole-parity members,
the sets of all ee pairs and of all oo pairs (`parity_form_vanishes_on_member_iff`, `whole_parity_members`), and for
any set of pairs exactly when it contains one of them (`parity_form_vanishes_iff_contains_whole_parity`). No
earlier declaration changes. 19 results in `Verify.lean`. Made with Claude Code
(model `claude-opus-5-5`).

## New module: `Conventions`

`PionCompleteness/Conventions.lean` is **not part of the accepted text**. It was added on 2026-10-12 so that the release
checks the conventions of `𝒜_N` (`calA`: sign, normalization, leg labels) against an outside source. Until then every
check of `calA` compared it with formulas in the same variables, by the same authors, so a slip made the same way in all
of them would pass. The module transcribes the closed forms of K. Kampf, J. Novotný, J. Trnka, arXiv:1304.3048, eqs.
(33), (34) and (200): amplitudes computed from Feynman diagrams of the Lagrangian, in their own variables `s_{i,j}`. It
proves `𝒜_N = (−1)^{N/2}(2F²)^{(N−2)/2}·𝓜_N` at `N = 4, 6, 8` for every `F ≠ 0` (`N = 8` off the poles). An AI numerical
check of the same normalization, with its own Lagrangian evaluator (model `claude-opus-5-5`, confirmed by a second run),
found it up to `N = 10`; it is not part of this release. The sign is fixed relative to KNT's formulas read with `s = X`,
and leg labels up to rotation and reflection (symmetries of the amplitude); the module docstring says how to check the
transcriptions by hand. Made with Claude Code (model `claude-opus-5-5`). There is no accepted module to compare with.
Its 6 results are in `Verify.lean`, and its definitions and statements are pinned in `Statements.lean` (before
2026-10-13 in the statement check, a tool of the source repository). Review: AI review agents (one round so far, three
agents), then the author's merge (pending). Added 2026-10-19: the three controls for `NLSM_N` itself, in the form the
paper states (`NLSM_N = −(2F²)^{(N−2)/2}·𝓜_N`, one sign for every `N`: `nlsm_four_knt`, `nlsm_six_knt`,
`nlsm_eight_knt`), derived from the controls for `𝒜_N`, since Theorem 3.1 in the paper's terms is about `NLSM_N`; 9
results in `Verify.lean`. Review: AI review agents, then the author's merge.
Added 2026-10-20: the relation for every even `N`, through the Cayley form. KNT's Feynman rules in the Cayley
parametrization, written in their variables (`kntV` transcribes their eq. (62); `kntDot`, derived from their eq. (30),
writes `2 p_a·p_b`; `kntSq`, `kntFeynman`, `kntCayleySum`, with their propagator), give `(2F²)^{−(N−2)/2}` times the Cayley sum for every even `N` (`kntCayleySum_eq`, from the face count
`faces_card_sub_two_sum`), so `NLSM_N = −(2F²)^{(N−2)/2}·kntCayleySum_N` (`nlsm_knt_cayley`, through `cayley_form`);
controls against KNT's closed forms at `N = 4, 6, 8` and three negative controls (the vertex constant and sign, the
propagator sign). That these Feynman rules give the amplitude of the Lagrangian is cited, not formalized. 26 results in
`Verify.lean`.
Planted slips (the working copy, restored; nothing committed): the propagator `+1/p²` fails `kntCayleySum_eq` and the
`N = 6` expansion; `2^{n+1}` in `kntV` fails the `N = 4` and `6` controls; dropping `s_{a+1,b−1}` from `kntDot` fails
the `N = 6` control. Made with Claude Code (model `claude-opus-5-5`). Review: AI review agents, then the author's
merge.

**Planted slips** (2026-10-12). Each slip was made in the working copy (not a separate copy of the project: disk
space), the module built, and the file restored; nothing was committed. The exact check computes `𝒜_N` from its
definition (the coefficient of `δ^{−(N−2)}` in the φ³ amplitude at `X + δ v₀`) with exact rational arithmetic at
random points, and compares it with KNT's formulas, independently of the Lean library.

| Slip | Where | Lean | Exact check (N = 4, 6, 8) |
|---|---|---|---|
| M1: `v₀` negated (`−1` on ee, `+1` on oo) | `shiftSign` | `PionNLSM` fails to build (9 errors: its proofs use the sign values) | identity still holds: for even `N` this is no slip (`δ → −δ` scales the `δ^{−(N−2)}` coefficient by `(−1)^{N−2} = 1`) |
| M2: `v₀ = +1` on oo chords too | `shiftSign` | `PionNLSM` fails to build (10 errors) | holds at N = 4; fails at 6, 8 |
| M3: chord index shifted (`d.1 + 1` in `v₀`) | `shiftSign` | `PionNLSM` fails to build (45 errors) | fails at 4, 6, 8 |
| M4: dictionary off by one, `s_{i,j} = X_{i,j}` | `kntS` | all three controls fail | — |
| M5: sign `(−1)^{N/2−1}` | `kntConst` | all three controls fail | — |

A slip in the definition of `NLSM` stops the build in `PionNLSM` (`NLSM_four`, `NLSM_six`, `theoremB` and the lemmas
under them) before the controls are reached. The controls are proved from those lemmas, so they cannot be proved;
that their statements are then false, and not only unproved, is shown by the exact check, outside Lean. M1 shows that
those proofs also fail on a change that leaves the even-`N` amplitude unchanged. M4 and M5 are now checked on every
build, at one rational point, by the negative controls `negctl_knt_dictionary` and `negctl_knt_sign`. Each mutated
build of `PionNLSM` took 80–90 s, with a peak of 4.7 GiB (laptop).

## New module: `PaperTests`

`PionCompleteness/PaperTests.lean` is **not part of the accepted text**. It was added on 2026-10-26 to hold every test
of the module `Paper` in one place for a reviewer, after the `test` statements of the formal-conjectures project ("a
statement that serves as a sanity check (e.g. for a new definition)"): the main theorem's non-vacuity (`NonVacuity`'s 16
theorems, merged here); the definitions on given objects, where they hold and where they fail; the paper's examples that
have a Lean form; and the hypotheses of theorems holding together. It holds 60 theorems:

- 24 new ones, tests of the definitions the main theorem's statement uses that no such statement tested before (regular
  sets, zeros, regular coordinate zeros, minimal ones and causal diamonds, in the paper's terms at `N = 6`, from the
  controls of `C10`; the triangulations, the shift and its sign, of the amplitude's definition), of two definitions that
  had none (the strip region, `regionAmp` and `stripFactor`; the Cayley sum and its vertex, at `N = 4`), and the
  hypotheses of the `T`-separated zeros and of the value on the marked locus. Which definitions and statements needed
  one was measured first, by a tool of the source repository that reads every `\lean` name of the paper and searches
  the Lean for a statement about given objects that tests it or shows its hypotheses holding; the author chose the
  scope (the review results and the theorems; the definitions of the statements a reader checks, and every paper
  definition with no test).
- 16 from `NonVacuity` (the module is gone), and 20 from `Paper`: its examples (`list_eight_card`,
  `figure_nine_configuration`, `example_eight_c_spread`, `example_shortening_nonvacuous`,
  `example_four_six_residue_regime`, `example_no_residue_chord_with_both_sides_linked`,
  `example_four_six_extreme_terms_nonvanishing`, `marked_locus_nonvacuous`, `example_cut_image_hyperplane` with its
  `example_cut_image_hyperplane_candidates`, `example_pole_free_locus_six`, `example_pole_free_locus_six_rational`),
  its non-vacuity checks of definitions (`faces_empty`, `hasNoPoleAlong_can_fail`, `not_hasNoPoleAlong_inv`,
  `not_restrictsToZeroAlong_one`) and the helpers only they use (`ratZeroOn_poly`, `onLocus_line_closed`,
  `restrictsToZeroAlong_numerator`, `residueHyperplane_line_closed`). Statements and proofs are unchanged; each name
  `PionCompleteness.Pi.x`, `PionCompleteness.Paper.x` or `PionCompleteness.Paper.<subject path>.x` became
  `PionCompleteness.PaperTests.x`, with the registry tags of the seven that carry one, and `Paper.lean` is 513 lines
  shorter (9,675).

The library's own controls (in `C0`–`C10` and the base modules, which stay as accepted, and the outside anchors of
`Conventions`) stay where they are; `REVIEW-CHECKS.md` lists those about given objects that no general proof uses, by the statement of the paper they test, generated
from the Lean code by a tool of the source repository. Every declaration of `PaperTests` is pinned in `Statements.lean`
and its axioms in `Verify.lean`; like `NonVacuity`'s, the 24 new tests have no registry key. Made with Claude Code
(model `claude-opus-5-5`).

## New file: `PionCompletenessChallenge`

`PionCompletenessChallenge.lean` (its own library, not a default target) is the Challenge for Palomar's comparator:
the main theorem in the paper's form, the three statements of `Paper` (`every_coordinate_zero_contains_a_family_member`,
`family_members_are_minimal_zeros`, `minimal_coordinate_zeros_are_the_list`), with `sorry` as their proofs, and the 28
definitions they use, copied character for character from the library under the same names (each section heading names
the module copied from). It imports only Mathlib: the 14 modules the library imports on its way to `Paper`. Its
`sorry`s are by design, and no module imports it: `lake build` (the default target) does not build it, and `Verify` does not
cover it. `comparator.json` names the Challenge, the solution module (`PionCompleteness.Paper`), the three theorems and
the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`). Comparator (`lake comparator` from Lean `v4.35.0`
on, or the standalone `leanprover/comparator`) then checks that `Paper` proves the three statements with definitions
equal to the Challenge's and no other axiom, in the Lean kernel; `lake comparator --paranoid` also runs the other
kernels bundled with Lean. The three anonymous `Decidable` instances among the copied definitions got docstrings in the
library for it (`Base.TreeRectangleZero`, `Base.PionZeros`); nothing else changed in the library. Made with Claude Code
(model `claude-opus-5-5`).
