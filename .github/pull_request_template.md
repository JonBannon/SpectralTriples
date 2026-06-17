<!-- Describe the change in 1–3 sentences. -->

## Summary



## Checklist

**Build & correctness**
- [ ] `lake build SpectralTriples` is clean (no errors, no warnings).
- [ ] No new `sorry` and no new `axiom` (search the diff).
- [ ] New/changed headline declarations are axiom-clean: `#print axioms` shows only
      `propext`, `Classical.choice`, `Quot.sound`.

**Assurance sync** — *do this whenever a tracked declaration is added, renamed, moved, or removed:*
- [ ] `scripts/axiom_report.lean` lists every new/renamed headline declaration (and drops removed ones).
- [ ] Regenerated the golden trace: `lake env lean scripts/axiom_report.lean > audit/axiom-report.txt`
      (committed in **this** PR, so the CI `axiom-report` diff passes).
- [ ] [`audit/FAITHFULNESS.md`](../audit/FAITHFULNESS.md) updated: a row for each new headline
      object/statement, with the **correct `file:line`**; fixed any references to files this PR
      moved/deleted.
- [ ] README "Current status" table reflects new files / examples.

**Definition changes** — *if this PR changes a definition (signature, fields, file location):*
- [ ] Updated every downstream user (examples, dependent lemmas) in the same PR.
- [ ] Updated the relevant "Faithfulness divergences" notes if the encoding changed.

**Axioms** — *if this PR introduces a project `axiom`:*
- [ ] Docstring with statement + reference + proof-strategy (per `~/.claude/CLAUDE.md`).
- [ ] Row added to `AXIOM_AUDIT.md` with rating + sources; counts updated in README.
- [ ] Vetting record under `audit/vetting/` before anything downstream relies on it.

<!-- The two lapses this checklist exists to prevent: (1) a moved/renamed decl leaving a
stale `file:line` in FAITHFULNESS.md or a stale entry in axiom_report.lean; (2) a new headline
result (e.g. an example triple) not being added to the golden axiom trace, so CI never
machine-checks its axiom-cleanliness. -->
