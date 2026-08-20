<!-- Describe the mathematical and implementation change in 1–3 sentences. -->

## Summary



## Checklist

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for the complete verification and
synchronization policy.

**Build and correctness**

- [ ] `lake build SpectralTriples` succeeds without project warnings.
- [ ] The change introduces no `sorry`/`admit` and no unreviewed project `axiom`.
- [ ] New or changed public statements use mathematically conservative names
      (compact resolvent vs. summability, graded-kernel invariant vs. chiral
      Fredholm index, bounded magnetic phase vs. geometric Dirac operator).

**Blueprint and assurance**

- [ ] `python3 scripts/check_axiom_coverage.py` passes.
- [ ] Every added/renamed blueprint headline is present in
      `scripts/axiom_report.lean`; removed names have been dropped.
- [ ] `lake env lean scripts/axiom_report.lean > audit/axiom-report.txt` was run
      and the generated diff was reviewed and committed.
- [ ] The blueprint text and dependencies reflect the exact Lean statements.
- [ ] `audit/FAITHFULNESS.md` was updated when an informal/formal statement,
      encoding choice, or literature correspondence changed.

**Status and downstream synchronization**

- [ ] New modules are imported by `SpectralTriples.lean` and downstream users
      compile.
- [ ] `README.md`, `PLAN.md`, and `formalization.yaml` reflect any status,
      terminology, or roadmap change.
- [ ] Compatibility aliases and deprecations are documented when a public name
      changed.

**Project axioms** — complete only if this PR intentionally introduces one

- [ ] The declaration has a docstring with its precise statement, source, and
      discharge strategy, following [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
- [ ] A row and count update were added to `AXIOM_AUDIT.md`.
- [ ] A vetting record was added under `audit/vetting/` before downstream use,
      and vetting strictness was raised to at least `L2`.

<!-- Keep code, blueprint, assurance artifacts, and status prose in one PR. -->
