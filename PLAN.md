# SpectralTriples — implementation plan and status

*Last updated: 2026-08-20. This is the source of truth for implementation
status and names. [`SpectralTriples/docs/DESIGN.md`](SpectralTriples/docs/DESIGN.md)
records the broader mathematical vision, while
[`SpectralTriples/docs/INDEX_PAIRING.md`](SpectralTriples/docs/INDEX_PAIRING.md)
scopes the geometric `T²` operator bridge.*

## Encoding and terminology

The unbounded `LinearPMap` picture is the project spine:

- `IsOddSpectralTriple A D π` and `IsEvenSpectralTriple A D π γ` package the
  self-adjoint Dirac core, domain invariance, bounded commutators, and grading
  axioms. The operator data are parameters; the structures are `Prop`-valued.
- `IsCompactResolventSpectralTriple A D π` extends the odd core with genuine
  resolvent membership at `i` and compactness of that resolvent.
- Compact resolvent is deliberately not called finite or `p`-summability. The
  former `FinitelySummable.lean` module and declaration names remain only as
  compatibility imports/aliases.
- `SpectralTriples.Fredholm.IsFredholm` is currently an operator-level
  predicate. General odd/even Fredholm modules and the projection pairing have
  not yet been introduced.
- `gradedKernelIndex D γ` is the difference between the `±1`-graded kernel
  dimensions. It is not yet proved equal to the Fredholm index of a constructed
  chiral operator `D⁺`.

The algebra assumptions used by the spectral-triple core are
`[Semiring A] [StarRing A] [Algebra 𝕜 A]`; there is no `StarModule` assumption.

## Current implementation

All rows below are implemented without `sorry` or project axioms.

| File | Main content | Status |
|---|---|---|
| `SpectralTriples/Basic.lean` | odd/even cores; dense/closed Dirac domain; domain and bounded extended commutators; grading API | **Done** |
| `SpectralTriples/Resolvent.lean` | inverse of a bijective `LinearPMap`, resolvent set/resolvent, range API | **Done** |
| `SpectralTriples/CompactResolvent.lean` | self-adjoint resolvent estimate; dense and closed range; `Im z ≠ 0 ⇒ z ∈ ρ(D)`; compact-resolvent structure and constructor | **Done** |
| `SpectralTriples/FinitelySummable.lean` | compatibility import for the superseded name | **Done** |
| `SpectralTriples/Fredholm.lean` | minimal Fredholm predicate and index for linear maps | **Done** |
| `SpectralTriples/CompactOperators.lean` | finite-rank approximation; compact adjoint; `1 - K` is Fredholm for compact `K` | **Done** |
| `SpectralTriples/Index.lean` | `Dkernel`, `gradedKernelIndex`, finite-dimensionality of `ker D` under compact resolvent, grading invariance | **Done** |
| `SpectralTriples/DiagonalOperator.lean` | block-diagonal `ℓ²` operators; norm and compactness criteria; self-adjoint unbounded diagonal operator | **Done** |
| `SpectralTriples/Examples/Circle.lean` | odd `S¹` core with compact resolvent | **Done** |
| `SpectralTriples/Examples/Torus.lean` | even flat-`T²` core with compact resolvent and graded-kernel invariant `0` | **Done** |
| `SpectralTriples/Examples/Shift.lean` | explicit Fredholm witness for the unilateral shift; index `-1` | **Done** |
| `SpectralTriples/Examples/MagneticDirac.lean` | bounded flux-`k` magnetic phase; explicit Fredholm witness; index `k`; finite Weyl translations | **Done (model level)** |
| `SpectralTriples/Examples/ThetaSections.lean` | `k` independent positive-degree theta sections | **Done** |
| `SpectralTriples/FourierHolomorphic.lean` | exact positive-degree holomorphic dimension `k`; explicit `thetaHolSectionBasis`; negative-degree holomorphic space is zero | **Done (function-theoretic)** |
| `SpectralTriples/HermiteL2.lean` | Hermite polynomial integral; normalized real/complex `L²(ℝ)` orthonormal family | **Done through orthonormality** |

## What these results do not yet establish

These boundaries are important for downstream statements and documentation:

- `finiteDimensional_Dkernel` proves finite-dimensionality of the full Dirac
  kernel. By itself it does not construct `D⁺`, prove that the chiral
  restriction is Fredholm, or identify its Fredholm index with
  `gradedKernelIndex`.
- The vanishing negative-degree holomorphic section space is a
  function-theoretic theorem. Identifying it with an operator cokernel requires
  the missing analytic/geometric bridge.
- `magneticPhase` is the bounded backward shift on the Landau-level model. The
  unbounded weighted lowering operator and its unitary equivalence with a
  twisted geometric Dirac operator on `T²` are not formalized.
- `orthonormal_hermiteFunctionL2` gives an orthonormal family, not a
  `HilbertBasis`; density/completeness is the remaining Hermite theorem.
- `Fredholm.isFredholm_one_sub` proves Fredholmness of `1 - K`; the additional
  classical assertion that its index is zero is not proved here.

## Prioritized next work

### 1. Complete the Hermite `L²` basis

Prove density of the span of `Polynomial.hermiteFunctionL2` and package the
orthonormal family as a Mathlib `HilbertBasis`. This is the next self-contained
step toward the Landau/Hermite route and should remain independent of the torus
bundle construction.

### 2. Build the geometric operator bridge

Following `INDEX_PAIRING.md`, define the weighted `L²` space of quasi-periodic
degree-`k` sections and the relevant closed, densely defined operator. Then
construct the Landau/Hermite decomposition and relate its bounded phase to
`MagneticDirac.magneticPhase`. Only after this equivalence is proved should the
model index `k` be described as the geometric twisted-Dirac index.

### 3. Add the chiral Fredholm layer

Construct the `±1` grading subspaces and the chiral restriction `D⁺`, prove its
closed range and finite-dimensional kernel/cokernel under appropriate
hypotheses, and compare `Fredholm.index D⁺` with `gradedKernelIndex`. The general
pairing with a projection representing a `K₀` class remains a subsequent phase.
The unbounded bounded-transform bridge still depends on functional calculus not
present in the pinned Mathlib API.

### 4. Keep research extensions downstream

Connes' spectral distance, cyclic cohomology/Chern character, the general
manifold construction, equivariance, and Kasparov-module generalizations remain
valuable later phases. They should not obscure the three concrete gaps above.

### 5. Upgrade dependencies separately

The repository remains pinned to Lean/Mathlib `v4.30.0`. Use the existing manual
dependency-update workflow to prepare a dedicated migration PR to a newer
stable release, rebuilding all Lean, the blueprint, API documentation, and the
axiom certificate. Do not combine a toolchain migration with mathematical or
status-document changes.

## Repository synchronization contract

For each public headline added, renamed, moved, or removed, update in the same
change:

1. the root import `SpectralTriples.lean` when module coverage changes;
2. `scripts/axiom_report.lean` and the generated `audit/axiom-report.txt`;
3. the blueprint declaration and prose;
4. `audit/FAITHFULNESS.md` when the informal/formal correspondence changes; and
5. the README, this plan, and `formalization.yaml` when project status changes.

CI checks that every declaration named by the blueprint is covered by the axiom
report. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the local commands.
