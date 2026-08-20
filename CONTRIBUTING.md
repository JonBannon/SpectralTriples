# Contributing to SpectralTriples

Thank you for improving the formalization. A change is complete when the Lean
code, mathematical prose, blueprint, and assurance artifacts describe the same
result.

## Set up and build

Install Lean with [Elan](https://github.com/leanprover/elan), clone the
repository, and run:

```sh
lake exe cache get
lake build SpectralTriples
```

The project pins its Lean and Mathlib versions in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Do not update those files as part of
an unrelated mathematical or documentation change.

## Verification before a pull request

Run the project build and the two assurance checks:

```sh
lake build SpectralTriples
python3 scripts/check_axiom_coverage.py
lake env lean scripts/axiom_report.lean | diff -u audit/axiom-report.txt -
```

The final command is silent on success. If a deliberate declaration or proof
change alters the report, regenerate and review the tracked file:

```sh
lake env lean scripts/axiom_report.lean > audit/axiom-report.txt
git diff -- audit/axiom-report.txt
```

Do not accept a new `sorryAx`, an unexplained project axiom, or any nonstandard
axiom dependency as mechanical report churn.

The documentation workflow builds the web/PDF blueprint, checks every
`\lean{...}` declaration with `checkdecls`, and builds the API documentation.
If `leanblueprint` is installed locally, `leanblueprint web` and
`leanblueprint pdf` provide the corresponding local checks. The generated
`blueprint/lean_decls` file can also be checked with:

```sh
lake exe checkdecls blueprint/lean_decls
```

## Synchronizing a public API change

When adding, renaming, moving, or removing a public headline, update all
applicable surfaces in the same pull request:

1. Import a new module from `SpectralTriples.lean`.
2. Add the declaration to `scripts/axiom_report.lean`, then regenerate
   `audit/axiom-report.txt`.
3. Update `blueprint/src/content.tex`. Every `\lean{...}` declaration must be
   present in the axiom-report script; CI enforces this coverage.
4. Update `audit/FAITHFULNESS.md` when the mathematical statement, encoding, or
   literature correspondence changes.
5. Update `README.md`, `PLAN.md`, and `formalization.yaml` when the project
   status or next steps change.

Prefer declaration names and file paths over brittle source line numbers in
new documentation. If an existing exact line reference is retained, verify it
after all Lean edits are complete.

## Mathematical claim boundaries

Use the repository's current names and avoid strengthening theorems in prose:

- Say **compact resolvent**, not finite or `p`-summability, unless a Schatten or
  trace estimate has actually been proved.
- Call `gradedKernelIndex` the graded-kernel invariant until a chiral operator
  is constructed, proved Fredholm, and compared with it.
- Call `MagneticDirac.magneticPhase` the bounded magnetic phase/model, not the
  geometric twisted Dirac operator.
- Call `orthonormal_hermiteFunctionL2` an orthonormal family, not a basis, until
  completeness is proved.
- The positive/negative-degree holomorphic-section results are
  function-theoretic; an operator kernel/cokernel interpretation requires the
  geometric analytic bridge.

When a theorem is intentionally conditional on missing analysis, expose the
missing result as an ordinary parameter or structure field. Do not use a local
`sorry`. A proposed Lean `axiom` must follow [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md)
and have a vetting record before downstream use.

## Pull requests

Keep changes focused and explain the informal mathematical statement together
with the exact Lean declaration. For a dependency migration, use the manual
“Update Dependencies” workflow and submit a dedicated pull request that
rebuilds the source, blueprint, API documentation, and axiom report.

By submitting a contribution for inclusion, you agree that it is licensed
under the repository's [Apache License 2.0](LICENSE).
