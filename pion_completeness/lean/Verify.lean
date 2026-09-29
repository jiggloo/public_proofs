import PionCompleteness

/-!
# Verification entry point for Theorem Π (pion completeness)

Compile with `lake env lean Verify.lean` after `lake build`. Expected: each `#print axioms` line lists exactly
`[propext, Classical.choice, Quot.sound]` (Lean's standard axioms) — no `sorryAx`, no custom axiom.
The imported library files contain some unrelated statements that are still open (`sorry`); they are not in the
dependency closure of the theorems below, which is what `#print axioms` checks.
-/

-- The three statements of Theorem Π (clause 1: completeness; clause 2: minimality; "hence": characterisation).
#check @PiZ.pi_clause1
#check @PiZ.pi_clause2
#check @PiZ.pi_minimal_iff

#print axioms PiZ.pi_clause1
#print axioms PiZ.pi_clause2
#print axioms PiZ.pi_minimal_iff

-- The three analytic inputs (formerly explicit hypotheses of the M2 statements), now theorems.
#print axioms PiZ.germ_input
#print axioms PiZ.resChild_input
#print axioms PiZ.stZero_input
