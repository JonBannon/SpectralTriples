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
#print axioms IsSelfAdjoint.dense_range_resolvent_apply
#print axioms IsFinitelySummableSpectralTriple

-- FinitelySummable.lean (continued) — the basic self-adjointness criterion (Im z ≠ 0 ⇒ z ∈ ρ(D)).
#print axioms IsSelfAdjoint.isClosed_range_subDirac
#print axioms IsSelfAdjoint.mem_resolventSet
#print axioms IsOddSpectralTriple.mem_resolventSet
#print axioms IsOddSpectralTriple.toIsFinitelySummableSpectralTriple
#print axioms IsFinitelySummableSpectralTriple.resolvent_mem

-- Index.lean — the graded-kernel index of an even spectral triple.
#print axioms SpectralTriples.Dkernel
#print axioms SpectralTriples.index
#print axioms SpectralTriples.finiteDimensional_Dkernel
#print axioms SpectralTriples.grading_mem_Dkernel
#print axioms IsEvenSpectralTriple.index

-- DiagonalOperator.lean — block-diagonal operators on ℓ² and the compactness criterion.
#print axioms lpDiag.diagL
#print axioms lpDiag.norm_diagL_le
#print axioms lpDiag.isCompactOperator_diagL_of_support_finite
#print axioms lpDiag.isCompactOperator_diagL

-- Examples/Torus.lean — the concrete T² Dirac spectral triple (even, finitely summable).
#print axioms SpectralTriples.Torus.diracDirac
#print axioms SpectralTriples.Torus.diracDirac_isSelfAdjoint
#print axioms SpectralTriples.Torus.mem_resolventSet_I
#print axioms SpectralTriples.Torus.isCompactOperator_resolvent_I
#print axioms SpectralTriples.Torus.grading
#print axioms SpectralTriples.Torus.isSelfAdjoint_grading
#print axioms SpectralTriples.Torus.grading_mul_self
#print axioms SpectralTriples.Torus.grading_anticomm
#print axioms SpectralTriples.Torus.algebra
#print axioms SpectralTriples.Torus.rep
#print axioms SpectralTriples.Torus.isOddSpectralTriple
#print axioms SpectralTriples.Torus.isEvenSpectralTriple
#print axioms SpectralTriples.Torus.isFinitelySummableSpectralTriple
#print axioms SpectralTriples.Torus.index_eq_zero
