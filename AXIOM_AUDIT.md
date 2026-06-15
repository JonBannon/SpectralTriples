# Axiom audit — SpectralTriples

*Last updated 2026-06-15.*

## Purpose

In this project an **axiom** would be a *vetted, provable theorem with a vetted
discharge plan* — a staging point, not a fundamental assumption.

---

**Active project axioms in build: 0.** The tracked headlines depend only on the
standard three (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
*(Source of truth: the generated [`audit/axiom-report.txt`](audit/axiom-report.txt),
CI-diffed against the kernel — do not hand-edit.)*

---

## Active axioms

None.

## Anticipated

The only planned axiom is **Rellich–Kondrachov** compactness of the Sobolev
inclusion `H¹(M, E) ↪ L²(M, E)`, to be introduced as an explicit hypothesis for
the Phase-4 manifold construction (DESIGN.md §3.7) rather than proved (a separate
multi-year PDE effort). When introduced it will get a vetting record under
`audit/vetting/` and a row here, and the vetting strictness in
`audit/vetting/policy.yml` will be raised to L2.
