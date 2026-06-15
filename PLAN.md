# SpectralTriples — implementation plan & status

*Last updated: 2026-06-15. Companion to [`SpectralTriples/docs/DESIGN.md`](SpectralTriples/docs/DESIGN.md),
which holds the durable mathematical vision and the worked example
computations. This file records the living implementation: the encoding
decision actually taken, the real declaration/file names, what is done,
and the immediate next step. Where the two disagree, **this file wins on
implementation; `DESIGN.md` wins on mathematics**.*

## Central encoding decision (supersedes DESIGN.md §3.1 / §5.1)

The unbounded `LinearPMap` picture is the **spine**; the bounded
Fredholm-module picture is a **tool introduced at Phase 2** for the index
pairing only.

* **Unbounded spine.** Definitions (`IsOddSpectralTriple`,
  `IsEvenSpectralTriple`), finitely-summable triples (compact resolvent),
  and — later — Connes' spectral distance live here. This matches
  Connes / GBF verbatim, and Mathlib's `LinearPMap` adjoint / self-adjoint
  API plus Moritz Doll's resolvent PR are **sufficient to state and prove**
  this layer today.
* **Bounded tool at Phase 2.** The Fredholm index pairing is the one place
  with no unbounded-native route in current Mathlib: the bounded transform
  `F = D (1 + D²)^(-1/2)` needs Borel functional calculus for *unbounded*
  self-adjoint operators, which Mathlib lacks (only bounded `cfc` exists).
  At Phase 2 we introduce a bounded `FredholmModule`/`GradedFredholmModule`
  and prove the index pairing there; the bounded-transform bridge back to
  `D` is deferred until the unbounded functional calculus exists.

DESIGN.md's earlier decision — "stay bounded, the unbounded structure is a
stub" — is reversed for the definition/finitely-summable layer, because the
premise ("Mathlib lacks unbounded self-adjoint API") turned out to be false
for that layer. It remains correct *only* for the index pairing.

## Current state

All files below are `sorry`-free and `axiom`-free.

| File | Contents | Status |
|------|----------|--------|
| `SpectralTriples/Basic.lean` | `IsOddSpectralTriple`, `IsEvenSpectralTriple` (unbounded `D : H →ₗ.[𝕜] H`) + API: `dense_domain_dirac`, `isClosed_dirac`, `exists_comm_bound`, `grading_sq`, `grading_commute`, `grading_conj_dirac`, `mem_unitary_iff_sq_eq_one`, `exists_grading_eigen_decomp` | **Done** |
| `SpectralTriples/Resolvent.lean` | `LinearPMap.inverseAsLinearMap`, `resolventSet`, `resolvent` + API (vendored from Mathlib PR #29624, Moritz Doll) | **Done** |
| `SpectralTriples/FinitelySummable.lean` | `IsSelfAdjoint.norm_resolvent_apply_ge`, `IsSelfAdjoint.injective_resolvent_apply`, `IsFinitelySummableSpectralTriple` | **Done** |

Naming note: the implemented structures are `Is`-prefixed Prop classes
(`IsOddSpectralTriple` …), **not** the `FredholmModule` / `SpectralTriple`
names used throughout DESIGN.md. The algebra is `[Semiring A] [StarRing A]
[Algebra 𝕜 A]` (no `[StarModule 𝕜 A]`, `Semiring` not `Ring`), and the even
triple takes `γ` as a structure *parameter*, not a bundled field.

## Immediate next step — close Chapter 1

**`basic-criterion-self-adjoint`** (blueprint's one open node):
`Im z ≠ 0 ⇒ z ∈ ρ(D)` — i.e. upgrade the existing injectivity of `z − D`
(`injective_resolvent_apply`) to *bijectivity*. This makes `z = i ∈ ρ(D)`
a theorem and lets `resolvent_mem` drop out of
`IsFinitelySummableSpectralTriple` (per Jon's "z is generally just i").

No deep Mathlib gap — two standard lemmas, proved in-project (~80–120 lines):

1. **`range (z − D)ᗮ = ker ((conj z − D)†)`** — density of range from
   injectivity of the adjoint. ~20 lines via `mem_adjoint_domain_of_exists`.
2. **Closed (graph-closed) bounded-below operator ⇒ closed range.** Mathlib
   has `closed_range_of_antilipschitz` only for bounded `ContinuousLinearMap`;
   the unbounded closed-operator version is missing. Standard
   Cauchy-preimage-via-closed-graph argument, ~40–60 lines. Upstream candidate.

Then: closed range + dense range ⇒ surjective; with injectivity ⇒ bijective
⇒ `z ∈ resolventSet`.

## Phase outline (see DESIGN.md §3.6 for full detail)

* **Phase 1 / 1.5 — definitions + finitely-summable.** Done, modulo the
  open node above.
* **Phase 2 — index pairing.** Introduce bounded `FredholmModule`; this is
  where the bounded tool enters. The only phase blocked on a *large* Mathlib
  gap (unbounded functional calculus) if attempted unbounded-native.
* **Phase 2.5 — Connes' spectral distance.** Natural fit for the unbounded
  spine (DESIGN.md §2.7); does not need the index pairing.
* **Phase 3 / 3.5 — examples (S¹, T² + line bundle).** Diagonal operators on
  ℓ²; stress-test the abstract API. Do before the general manifold case.
* **Phase 4 — manifold construction.** De-risked by our in-house
  `differential-geometry` repo (Rellich–Kondrachov, connection-Laplacian
  resolvent, Lichnerowicz already formalized — for the Laplacian, not Dirac,
  but the hard analysis scaffolding exists).

## Repo hygiene TODO

* `README.md` is still GitHub-template boilerplate — replace with a real
  project description and a "Current Status" section.
* No `AXIOM_AUDIT.md` yet (currently moot: zero axioms). Add a stub if/when
  an axiom is introduced.
