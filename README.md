# SpectralTriples

A Lean 4 + Mathlib formalization of **spectral triples** from Alain Connes'
noncommutative geometry: odd and even (Z₂-graded) spectral triples, the
resolvent of the Dirac operator, and finitely-summable triples — working
toward the Fredholm index pairing.

📐 **[Blueprint](https://JonBannon.github.io/SpectralTriples/blueprint/)** ·
🗺️ **[Design notes](SpectralTriples/docs/DESIGN.md)** ·
📋 **[Implementation plan & status](PLAN.md)**

## Current status

All source is `sorry`-free and `axiom`-free. Built against Mathlib `v4.30.0`.

| File | Contents |
|------|----------|
| [`SpectralTriples/Basic.lean`](SpectralTriples/Basic.lean) | `IsOddSpectralTriple`, `IsEvenSpectralTriple` (Dirac operator `D` as an unbounded `LinearPMap`) and their basic API |
| [`SpectralTriples/Resolvent.lean`](SpectralTriples/Resolvent.lean) | `LinearPMap.resolventSet` / `resolvent` (adapted from Mathlib PR [#29624](https://github.com/leanprover-community/mathlib4/pull/29624), Moritz Doll) |
| [`SpectralTriples/FinitelySummable.lean`](SpectralTriples/FinitelySummable.lean) | self-adjoint resolvent estimates and `IsFinitelySummableSpectralTriple` (compact resolvent) |

The encoding decision: the unbounded `LinearPMap` picture is the spine, with a
bounded Fredholm-module layer planned at Phase 2 for the index pairing. See
[`PLAN.md`](PLAN.md) for the rationale, the immediate next step, and the phase
outline; [`DESIGN.md`](SpectralTriples/docs/DESIGN.md) for the full
mathematical vision and worked examples.

## Building

```sh
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

## References

Connes, *Noncommutative Geometry* (1994); Gracia-Bondía–Várilly–Figueroa,
*Elements of Noncommutative Geometry* (2001); Higson–Roe, *Analytic
K-Homology* (2000). Reference notes live in
[`SpectralTriples/refs/`](SpectralTriples/refs/).

## Assurance

This project follows the assurance conventions of
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance)
(verification / validation / faithfulness, axiom vetting, `formalization.yaml`,
comparator). Local settings:

| Setting | Where |
|---|---|
| Project card | [`formalization.yaml`](formalization.yaml) |
| Faithfulness map (informal ↔ formal) | [`docs/FAITHFULNESS.md`](docs/FAITHFULNESS.md) |
| Kernel axiom certificate (generated, CI-diffed) | [`docs/axiom-report.txt`](docs/axiom-report.txt) |
| Axiom audit | [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — **0 project axioms** |
| Vetting strictness | [`docs/vetting/policy.yml`](docs/vetting/policy.yml) — `L1` |

All tracked headlines are `sorry`-free and **axiom-clean** (standard-three only:
`propext`, `Classical.choice`, `Quot.sound`); CI regenerates `docs/axiom-report.txt`
from `#print axioms` and fails on drift. Regenerate locally with:

```sh
lake env lean scripts/axiom_report.lean > docs/axiom-report.txt
```

## Authors & license

Jon Bannon, Michael R. Douglas. Released under the Apache 2.0 license.
