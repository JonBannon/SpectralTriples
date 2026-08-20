# SpectralTriples

A Lean 4 + Mathlib formalization of spectral triples from noncommutative
geometry. The project uses an unbounded `LinearPMap` Dirac operator as its
spine, develops compact-resolvent and Fredholm infrastructure, and tests that
infrastructure on Fourier, shift, torus, magnetic-phase, theta-function, and
Hermite-function examples.

📐 **[Blueprint](https://JonBannon.github.io/SpectralTriples/blueprint/)** ·
📚 **[API documentation](https://JonBannon.github.io/SpectralTriples/docs/)** ·
🗺️ **[Implementation plan](PLAN.md)** ·
🧭 **[Geometric index roadmap](SpectralTriples/docs/INDEX_PAIRING.md)** ·
🤝 **[Contributing](CONTRIBUTING.md)**

## Current status

The current Lean sources are `sorry`-free and use no project axioms. The
tracked public headlines depend only on Lean's standard three axioms
(`propext`, `Classical.choice`, and `Quot.sound`), as checked by the committed
kernel report. The repository is presently pinned to Mathlib `v4.30.0`.

| File | Formalized content |
|---|---|
| [`Basic.lean`](SpectralTriples/Basic.lean) | odd/even core predicates, domain invariance, and the derived everywhere-defined `boundedCommutator` |
| [`Resolvent.lean`](SpectralTriples/Resolvent.lean) | `LinearPMap.resolventSet`, `resolvent`, and inverse/range lemmas, adapted from Mathlib PR [#29624](https://github.com/leanprover-community/mathlib4/pull/29624) |
| [`CompactResolvent.lean`](SpectralTriples/CompactResolvent.lean) | self-adjoint resolvent estimates, the off-real-axis resolvent criterion, and `IsCompactResolventSpectralTriple` |
| [`FinitelySummable.lean`](SpectralTriples/FinitelySummable.lean) | compatibility import for the former name; compact resolvent alone is not finite or `p`-summability |
| [`Fredholm.lean`](SpectralTriples/Fredholm.lean) | a minimal `Fredholm.IsFredholm` predicate and kernel-minus-cokernel index for linear maps |
| [`CompactOperators.lean`](SpectralTriples/CompactOperators.lean) | finite-rank approximation, compact adjoints, and Fredholmness of `1 - K` for compact `K` |
| [`Index.lean`](SpectralTriples/Index.lean) | `gradedKernelIndex` and finite-dimensionality of `ker D` under compact resolvent |
| [`DiagonalOperator.lean`](SpectralTriples/DiagonalOperator.lean) | bounded and unbounded block-diagonal operators on `ℓ²`, including compactness and self-adjointness criteria |
| [`FourierHolomorphic.lean`](SpectralTriples/FourierHolomorphic.lean) | Fourier-recursion proof of dimension `k` and an explicit `thetaHolSectionBasis` for the positive-degree holomorphic section space; the negative-degree space vanishes |
| [`HermiteL2.lean`](SpectralTriples/HermiteL2.lean) | Gaussian-weighted Hermite orthogonality and a normalized orthonormal family in real or complex `L²(ℝ)`; completeness is still open |
| [`Examples/Circle.lean`](SpectralTriples/Examples/Circle.lean) | an odd circle spectral-triple core with compact resolvent |
| [`Examples/Torus.lean`](SpectralTriples/Examples/Torus.lean) | an even flat-torus spectral-triple core with compact resolvent and graded-kernel invariant `0` |
| [`Examples/Shift.lean`](SpectralTriples/Examples/Shift.lean) | an explicit Fredholm witness for the unilateral shift and Fredholm index `-1` |
| [`Examples/MagneticDirac.lean`](SpectralTriples/Examples/MagneticDirac.lean) | the bounded flux-`k` magnetic phase, an explicit Fredholm witness, index `k`, and finite Weyl translations |
| [`Examples/ThetaSections.lean`](SpectralTriples/Examples/ThetaSections.lean) | `k` linearly independent holomorphic automorphic theta functions |

The project deliberately distinguishes results that are sometimes conflated in
informal descriptions:

- `IsCompactResolventSpectralTriple` states compact resolvent, not finite or
  Schatten `p`-summability.
- `gradedKernelIndex` is a difference of finite graded-kernel dimensions. The
  chiral operator `D⁺` and an equality with its Fredholm index have not yet been
  formalized.
- `magneticPhase` is a bounded backward-shift model. Its equivalence with the
  geometric twisted Dirac operator on a line bundle over `T²` remains open.
- The Hermite functions are packaged as an orthonormal family; an `L²` basis
  still requires a completeness proof.

See [`PLAN.md`](PLAN.md) for the prioritized next steps and
[`INDEX_PAIRING.md`](SpectralTriples/docs/INDEX_PAIRING.md) for the detailed
operator bridge.

## Building

Install Lean through Elan, then run:

```sh
lake exe cache get
lake build SpectralTriples
```

The complete local verification sequence is documented in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

## References

Connes, *Noncommutative Geometry* (1994); Gracia-Bondía–Várilly–Figueroa,
*Elements of Noncommutative Geometry* (2001); Higson–Roe, *Analytic
K-Homology* (2000). Reference notes live in
[`SpectralTriples/refs/`](SpectralTriples/refs/).

## Assurance

| Artifact | Role |
|---|---|
| [`formalization.yaml`](formalization.yaml) | machine-readable project/status card |
| [`audit/FAITHFULNESS.md`](audit/FAITHFULNESS.md) | informal-to-formal correspondence and encoding divergences |
| [`scripts/axiom_report.lean`](scripts/axiom_report.lean) | tracked public declarations whose transitive axioms are printed by Lean |
| [`audit/axiom-report.txt`](audit/axiom-report.txt) | generated, committed kernel report; CI fails on drift |
| [`scripts/check_axiom_coverage.py`](scripts/check_axiom_coverage.py) | verifies that every declaration marked in the blueprint is tracked by the axiom report |
| [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) | project-axiom policy and current count (`0`) |
| [`audit/vetting/policy.yml`](audit/vetting/policy.yml) | axiom-vetting strictness (`L1` while there are no project axioms) |

## Authors and license

Jon Bannon and Michael R. Douglas. Released under the
[Apache License 2.0](LICENSE).
