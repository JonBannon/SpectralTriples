/-
Axiom-trace report for the tracked headline declarations.

Run:  lake env lean scripts/axiom_report.lean > audit/axiom-report.txt

`#print axioms D` prints the COMPLETE transitive axiom dependency of `D`
and surfaces any `sorryAx`. Committing the output as a golden file and
diffing it in CI guarantees, permanently, that:
  * no tracked headline secretly depends on a `sorry` (`sorryAx`), and
  * any change to a headline's axiom set is a reviewed diff.

This file is NOT part of the build root (`scripts/` is outside the
`SpectralTriples` lean_lib); it is a standalone checker. Keep the list in
sync with the headline declarations in README "Current status" and in
audit/FAITHFULNESS.md.
-/
import SpectralTriples

open LinearPMap

-- Basic.lean — the two core definitions and their API.
#print axioms IsOddSpectralTriple
#print axioms IsEvenSpectralTriple
#print axioms IsOddSpectralTriple.dense_domain_dirac
#print axioms IsOddSpectralTriple.isClosed_dirac
#print axioms IsOddSpectralTriple.exists_comm_bound
#print axioms IsEvenSpectralTriple.grading_sq
#print axioms IsEvenSpectralTriple.grading_commute
#print axioms IsEvenSpectralTriple.grading_conj_dirac
#print axioms IsEvenSpectralTriple.mem_unitary_iff_sq_eq_one
#print axioms IsEvenSpectralTriple.exists_grading_eigen_decomp

-- Resolvent.lean — resolvent set / resolvent of a LinearPMap.
#print axioms LinearPMap.inverseAsLinearMap
#print axioms LinearPMap.resolventSet
#print axioms LinearPMap.resolvent
#print axioms LinearPMap.range_resolvent

-- FinitelySummable.lean — self-adjoint resolvent estimates + the structure.
#print axioms IsSelfAdjoint.norm_resolvent_apply_ge
#print axioms IsSelfAdjoint.injective_resolvent_apply
#print axioms IsFinitelySummableSpectralTriple
