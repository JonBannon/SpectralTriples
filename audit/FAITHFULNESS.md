# FAITHFULNESS — the informal ↔ formal correspondence

A certificate that the Lean formalization *faithfully transcribes* the spectral-triple
definitions and their first consequences. For each object we give the informal content,
its exact Lean form, and the literature reference; for each statement, the informal claim
and the Lean theorem.

This is the **faithfulness** layer of *validation* — *"do the formal statements mean what
the mathematics means?"* (note `proved ≠ faithful`). The adjacent concerns live elsewhere:
**verification** — *"are the proofs valid relative to explicit assumptions?"* — is the
kernel check (`lake build`) plus the axiom certificate in
[`axiom-report.txt`](axiom-report.txt); axiom soundness review (none needed yet — no
project axioms) would live in `AXIOM_AUDIT.md`.

**Status legend:** ✓ = proved and `lake build` succeeds; **axiom-clean** =
`#print axioms` is `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`,
no project axioms), machine-checked in [`axiom-report.txt`](axiom-report.txt) (CI-diffed).
References: Connes, *Noncommutative Geometry* (1994), Ch. VI; Gracia-Bondía–Várilly–Figueroa
(GBF), *Elements of NCG* (2001), Ch. 9–11; Higson–Roe, *Analytic K-Homology* (2000).

Carrier throughout: a complex (or real) Hilbert space and a `*`-algebra,
`{A H 𝕜} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H]`
`[InnerProductSpace 𝕜 H] [CompleteSpace H]`, Dirac operator `D : H →ₗ.[𝕜] H`, and
representation `π : A →⋆ₐ[𝕜] (H →L[𝕜] H)`.

---

## Primary objects

| Object | Informal content | Reference | Lean |
|---|---|---|---|
| Odd spectral triple | self-adjoint `D`; `π a` preserves `dom D`; `[D, π a]` bounded | Connes Ch. VI; GBF §9 | `IsOddSpectralTriple` — `Basic.lean:28` |
| Even (Z₂-graded) triple | odd triple + grading `γ`: self-adjoint, involutive (`γ² = 1`), `[γ, π a] = 0`, `γ D + D γ = 0` | Connes Ch. VI | `IsEvenSpectralTriple` — `Basic.lean:37` |
| Resolvent set | `{ z : z·1 − D bijective on dom D }` | standard | `LinearPMap.resolventSet` — `Resolvent.lean:117` |
| Resolvent | `(z·1 − D)⁻¹` as an everywhere-defined `LinearMap`, for `z ∈ ρ(D)` | standard | `LinearPMap.resolvent` — `Resolvent.lean:122` |
| Finitely summable triple | odd triple whose `D` has **compact resolvent** at some `z` | Connes Ch. VI | `IsFinitelySummableSpectralTriple` — `FinitelySummable.lean:101` |

## Headline statements

| Claim | Lean | Status |
|---|---|---|
| `dom D` is dense | `IsOddSpectralTriple.dense_domain_dirac` — `Basic.lean:54` | ✓ axiom-clean |
| `D` is a closed operator | `IsOddSpectralTriple.isClosed_dirac` — `Basic.lean:58` | ✓ axiom-clean |
| `[D, π a]` is bounded by a finite real `C` on the unit ball | `IsOddSpectralTriple.exists_comm_bound` — `Basic.lean:65` | ✓ axiom-clean |
| `γ² = 1` (defining field of the even triple) | `IsEvenSpectralTriple.grading_sq` — `Basic.lean:42` | ✓ axiom-clean |
| `γ` commutes with `π a` | `IsEvenSpectralTriple.grading_commute` — `Basic.lean:89` | ✓ axiom-clean |
| `γ D γ = −D` on `dom D` | `IsEvenSpectralTriple.grading_conj_dirac` — `Basic.lean:95` | ✓ axiom-clean |
| self-adjoint unitary involution ⇔ `γ² = 1` | `IsEvenSpectralTriple.mem_unitary_iff_sq_eq_one` — `Basic.lean:103` | ✓ axiom-clean |
| every vector decomposes into `±1`-eigenvectors of `γ` | `IsEvenSpectralTriple.exists_grading_eigen_decomp` — `Basic.lean:109` | ✓ axiom-clean |
| `range (resolvent z) = dom D` | `LinearPMap.range_resolvent` — `Resolvent.lean:132` | ✓ axiom-clean |
| `|Im z|·‖x‖ ≤ ‖z·x − D x‖` for self-adjoint `D` | `IsSelfAdjoint.norm_resolvent_apply_ge` — `FinitelySummable.lean:43` | ✓ axiom-clean |
| `z·1 − D` injective on `dom D` when `Im z ≠ 0` | `IsSelfAdjoint.injective_resolvent_apply` — `FinitelySummable.lean:82` | ✓ axiom-clean |
| range of `z·1 − D` is dense | `IsSelfAdjoint.dense_range_resolvent_apply` — `FinitelySummable.lean:155` | ✓ axiom-clean |
| range of `z·1 − D` is closed | `IsSelfAdjoint.isClosed_range_subDirac` — `FinitelySummable.lean:191` | ✓ axiom-clean |
| **basic criterion:** `Im z ≠ 0 ⇒ z ∈ ρ(D)` (`z·1 − D` bijective) | `IsSelfAdjoint.mem_resolventSet` — `FinitelySummable.lean:231` | ✓ axiom-clean |
| odd triple: `Im z ≠ 0 ⇒ z ∈ ρ(D)` (so `i ∈ ρ(D)`) | `IsOddSpectralTriple.mem_resolventSet` — `FinitelySummable.lean:265` | ✓ axiom-clean |
| finitely summable triple from odd + compact resolvent (no `resolvent_mem` needed) | `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` — `FinitelySummable.lean:301` | ✓ axiom-clean |

> The basic-criterion lemmas moved from a former `SelfAdjoint.lean` into
> `FinitelySummable.lean` when PR #4 hard-coded `i` into the finitely-summable definition;
> the file `SelfAdjoint.lean` no longer exists.

## Reusable analytic infrastructure

| Object / Claim | Informal content | Lean | Status |
|---|---|---|---|
| Block-diagonal operator on `ℓ²` | `(diagL T) a = (i ↦ Tᵢ aᵢ)` for a uniformly bounded block family | `lpDiag.diagL` — `DiagonalOperator.lean:69` | ✓ axiom-clean |
| its operator-norm bound | `‖diagL T‖ ≤ C` when `‖Tᵢ‖ ≤ C` | `lpDiag.norm_diagL_le` — `DiagonalOperator.lean:97` | ✓ axiom-clean |
| **compactness criterion** | block norms `→ 0` (cofinite) + finite-dim fibres ⇒ `diagL T` compact (finite-rank truncations converge in operator norm) | `lpDiag.isCompactOperator_diagL` — `DiagonalOperator.lean:185` | ✓ axiom-clean |

## Concrete example: the Dirac spectral triple of the 2-torus `T²`

A worked, fully assembled **even, finitely-summable** spectral triple, on the Fourier side
`H = ℓ²(ℤ²; ℂ²)`, `D₍ₘ,ₙ₎ = 2π(σ₁ m + σ₂ n)`, chirality `γ = σ₃`, algebra = the Fourier
image of the trigonometric polynomials `ℂ[ℤ²]` (the dense `*`-subalgebra of `C(T²)`).
Reference: Connes Ch. VI; GBF §9–12 (canonical triple of a spin manifold, here `T²`).

| Object / Claim | Lean | Status |
|---|---|---|
| Dirac operator `D` (block-diagonal, unbounded) | `SpectralTriples.Torus.diracDirac` — `Examples/Torus.lean:131` | ✓ axiom-clean |
| `D` self-adjoint | `SpectralTriples.Torus.diracDirac_isSelfAdjoint` — `Examples/Torus.lean:211` | ✓ axiom-clean |
| `i ∈ ρ(D)` | `SpectralTriples.Torus.mem_resolventSet_I` — `Examples/Torus.lean:231` | ✓ axiom-clean |
| `(D − i·1)⁻¹` is compact | `SpectralTriples.Torus.isCompactOperator_resolvent_I` — `Examples/Torus.lean:509` | ✓ axiom-clean |
| grading `γ = σ₃` (CLM) | `SpectralTriples.Torus.grading` — `Examples/Torus.lean:592` | ✓ axiom-clean |
| `γ` self-adjoint | `SpectralTriples.Torus.isSelfAdjoint_grading` — `Examples/Torus.lean:608` | ✓ axiom-clean |
| `γ² = 1` | `SpectralTriples.Torus.grading_mul_self` — `Examples/Torus.lean:612` | ✓ axiom-clean |
| `D γ = −γ D` on `dom D` | `SpectralTriples.Torus.grading_anticomm` — `Examples/Torus.lean:631` | ✓ axiom-clean |
| algebra `ℂ[ℤ²]` (shift `*`-subalgebra) | `SpectralTriples.Torus.algebra` — `Examples/Torus.lean:871` | ✓ axiom-clean |
| representation (inclusion `StarAlgHom`) | `SpectralTriples.Torus.rep` — `Examples/Torus.lean:876` | ✓ axiom-clean |
| **`(A, H, D)` is an odd spectral triple** | `SpectralTriples.Torus.isOddSpectralTriple` — `Examples/Torus.lean:931` | ✓ axiom-clean |
| **`(A, H, D, γ)` is an even spectral triple** | `SpectralTriples.Torus.isEvenSpectralTriple` — `Examples/Torus.lean:984` | ✓ axiom-clean |
| **finitely summable at `i`** | `SpectralTriples.Torus.isFinitelySummableSpectralTriple` — `Examples/Torus.lean:994` | ✓ axiom-clean |

*Faithfulness note for the example.* The chosen algebra is the trigonometric polynomials
`ℂ[ℤ²]` (Fourier dual of `C(T²)`), represented by the coordinate shift unitaries — the
standard *smooth/pre-`C*`* algebra of the noncommutative-geometry torus, not the full `C(T²)`.
This is the genuine spectral triple of `T²` at the level of its dense smooth subalgebra; the
bounded commutator `[D, π a]` is exact (`[D, Wg] = −(σ·g) Wg`, the Clifford action of `g`).

## Faithfulness divergences (encoding choices, reviewer attention)

1. **Bounded-commutator axiom.** `IsOddSpectralTriple.comm` is stated as
   `⨆ x ∈ closedBall 0 1, ‖π a (D x) − D (π a x)‖ₑ < ∞` (an `ℝ≥0∞` supremum), rather than
   "`[D, π a]` extends to a bounded operator." The genuine finite real bound is recovered
   as `exists_comm_bound`. *Equivalent* to the literature statement on `dom D`; the `ℝ≥0∞`
   form is chosen so the field is a clean `Prop` without carrying the extension as data.
2. **Self-adjointness.** Encoded as Mathlib's `IsSelfAdjoint D` (`D† = D`) for the
   `LinearPMap` `D`, which already entails dense domain and closedness (used directly by
   `dense_domain_dirac` / `isClosed_dirac`). Matches the literature's "self-adjoint (hence
   densely defined and closed)."
3. **Resolvent set for non-closed `D`.** `resolventSet` is defined via bijectivity of
   `z·1 − D` as a `LinearPMap`; for non-closed `D` this can be nonempty where the
   conventional definition is empty. Documented in the `Resolvent.lean` docstring; harmless
   because spectral-triple `D` is closed.
4. **Grading bundling.** `IsEvenSpectralTriple` takes `γ` as a structure *parameter* (with
   self-adjointness and `γ² = 1` as fields), not a bundled data field — consistent with the
   project's predicate-style convention (see `PLAN.md`).

---

*Keep the headline list in sync with `scripts/axiom_report.lean` and the README "Current
status" table. The "axiom-clean" claims are machine-checked once `axiom-report.txt` is
generated by the kernel and CI-diffed.*
