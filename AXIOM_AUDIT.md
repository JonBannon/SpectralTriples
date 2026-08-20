# Axiom audit — SpectralTriples

*Last updated 2026-08-20.*

## Current result

**Active project axioms in the build: 0.** The public declarations tracked by
[`scripts/axiom_report.lean`](scripts/axiom_report.lean) depend only on Lean's
standard three axioms (`propext`, `Classical.choice`, and `Quot.sound`) and do
not depend on `sorryAx`.

The kernel-generated source of truth is
[`audit/axiom-report.txt`](audit/axiom-report.txt). CI regenerates that file and
fails on any diff. A separate coverage check ensures that every declaration
named by the blueprint is included in the tracked report. Neither file should
be edited by hand to conceal a change in dependencies.

## Policy

A project `axiom` is permitted only as an explicit, temporary boundary around a
mathematically established result that cannot yet be discharged in the
available library. Before any downstream theorem relies on it, the change must
include:

1. a precise statement and literature reference;
2. an explanation of why an ordinary theorem hypothesis is insufficient;
3. a proof or upstreaming strategy;
4. a vetting record under `audit/vetting/`;
5. an entry in this file and the generated kernel report; and
6. an increase of `audit/vetting/policy.yml` from `L1` to at least `L2`.

An explicit parameter or structure field such as
`(rellichKondrachov : IsCompactOperator inclusion)` is an ordinary hypothesis,
not a Lean project axiom. It is the preferred way to keep future manifold
assembly conditional on unavailable analysis. A local `sorry` is not an
acceptable substitute.

## Active axioms

None.

## Anticipated analytic boundary

The general manifold construction is expected to require
Rellich–Kondrachov compactness of the Sobolev inclusion
`H¹(M, E) ↪ L²(M, E)`. The default plan is to expose that result as an explicit
hypothesis until it is proved or imported. If the project later chooses to
introduce it as a Lean `axiom`, the policy above must be completed in the same
change before any downstream use.
