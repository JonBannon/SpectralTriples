# FAITHFULNESS — informal ↔ formal correspondence

This map records what the Lean declarations actually say and separates proved formal content
from classical interpretations that still need a bridge. It is the validation layer of the
project: kernel checking answers “is the proof valid?”, while this file asks “does the formal
statement mean what the prose says?”

Verification is provided by `lake build` and the generated
[`axiom-report.txt`](axiom-report.txt). “Axiom-clean” below means that the tracked declaration
uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom.

## Core spectral-triple data

The carrier is a real or complex Hilbert space `H`, an algebra `A`, an unbounded
`LinearPMap D : H →ₗ.[𝕜] H`, and a representation
`π : A →⋆ₐ[𝕜] (H →L[𝕜] H)`.

| Informal object / claim | Lean declaration | Source | Status |
|---|---|---|---|
| Odd spectral-triple **core**: self-adjoint `D`, domain invariance, bounded commutators | `IsOddSpectralTriple` | `Basic.lean` | ✓ axiom-clean |
| Even core: odd core plus self-adjoint involutive grading commuting with `π` and anticommuting with `D` | `IsEvenSpectralTriple` | `Basic.lean` | ✓ axiom-clean |
| `dom D` is dense | `IsOddSpectralTriple.dense_domain_dirac` | `Basic.lean` | ✓ axiom-clean |
| `D` is closed | `IsOddSpectralTriple.isClosed_dirac` | `Basic.lean` | ✓ axiom-clean |
| algebraic domain commutator `[D,π(a)]` | `domainRepresentation`, `commutatorOnDomain` | `Basic.lean` | ✓ axiom-clean |
| homogeneous norm bound on the domain commutator | `IsOddSpectralTriple.exists_commutator_bound` | `Basic.lean` | ✓ axiom-clean |
| unique bounded extension to all of `H`, agreeing on `dom D` | `boundedCommutator`, `boundedCommutator_apply`, `boundedCommutator_unique` | `Basic.lean` | ✓ axiom-clean |
| grading commutes with `π(a)` | `IsEvenSpectralTriple.grading_commute` | `Basic.lean` | ✓ axiom-clean |
| `γDγ = -D` on `dom D` | `IsEvenSpectralTriple.grading_conj_dirac` | `Basic.lean` | ✓ axiom-clean |
| self-adjoint involution is unitary iff `γ² = 1` | `IsEvenSpectralTriple.mem_unitary_iff_sq_eq_one` | `Basic.lean` | ✓ axiom-clean |
| every vector decomposes into `±1` grading eigenvectors | `IsEvenSpectralTriple.exists_grading_eigen_decomp` | `Basic.lean` | ✓ axiom-clean |

**Terminology boundary.** Standard definitions also require compact resolvent. The two `Basic`
predicates intentionally isolate the reusable core axioms; they are not by themselves complete
spectral triples in that standard sense. Compact resolvent is added below. Genuine finite or
`p`-summability, which requires Schatten/trace decay, is not yet formalized.

## Resolvent and compact resolvent

| Informal object / claim | Lean declaration | Source | Status |
|---|---|---|---|
| resolvent set `{z | z·1 - D is bijective}` | `LinearPMap.resolventSet` | `Resolvent.lean` | ✓ axiom-clean |
| algebraic inverse on the resolvent set | `LinearPMap.resolvent` | `Resolvent.lean` | ✓ axiom-clean |
| `range (resolvent z) = dom D` | `LinearPMap.range_resolvent` | `Resolvent.lean` | ✓ axiom-clean |
| `|Im z|‖x‖ ≤ ‖(z-D)x‖` for self-adjoint `D` | `IsSelfAdjoint.norm_resolvent_apply_ge` | `CompactResolvent.lean` | ✓ axiom-clean |
| `z-D` is injective off the real axis | `IsSelfAdjoint.injective_resolvent_apply` | `CompactResolvent.lean` | ✓ axiom-clean |
| range of `z-D` is dense and closed | `dense_range_resolvent_apply`, `isClosed_range_subDirac` | `CompactResolvent.lean` | ✓ axiom-clean |
| off-real points lie in `ρ(D)` | `IsSelfAdjoint.mem_resolventSet` | `CompactResolvent.lean` | ✓ axiom-clean |
| spectral-triple core plus compact resolvent at `i` | `IsCompactResolventSpectralTriple` | `CompactResolvent.lean` | ✓ axiom-clean |
| smart constructor from an odd core and compactness | `IsOddSpectralTriple.toIsCompactResolventSpectralTriple` | `CompactResolvent.lean` | ✓ axiom-clean |

The fixed point is `RCLike.I`. Over `ℂ`, self-adjointness supplies `i ∈ ρ(D)`. Over `ℝ`,
`RCLike.I = 0`, so the structure explicitly requires `0 ∈ ρ(D)` and the smart constructor’s
off-real hypothesis is unavailable. This layer is therefore primarily useful over `ℂ` until the
resolvent point is parameterized.

## Fredholm infrastructure

| Informal object / claim | Lean declaration | Source | Status |
|---|---|---|---|
| linear map with finite kernel, closed range, finite cokernel | `SpectralTriples.Fredholm.IsFredholm` | `Fredholm.lean` | ✓ axiom-clean |
| `dim ker - dim coker` | `SpectralTriples.Fredholm.index` | `Fredholm.lean` | ✓ axiom-clean |
| bijections are Fredholm of index zero | `isFredholm_of_bijective`, `index_of_bijective` | `Fredholm.lean` | ✓ axiom-clean |
| compact operators admit finite-rank norm approximants | `IsCompactOperator.exists_finiteRank_norm_sub_lt` | `CompactOperators.lean` | ✓ axiom-clean |
| adjoint of a compact operator is compact | `IsCompactOperator.adjoint` | `CompactOperators.lean` | ✓ axiom-clean |
| `1-K` is Fredholm for compact `K` | `SpectralTriples.Fredholm.isFredholm_one_sub` | `CompactOperators.lean` | ✓ axiom-clean |

The project proves the structural Fredholm statement for `1-K`; it does not yet prove the
additional classical assertion that this operator has index zero.

## Graded kernel

| Informal object / claim | Lean declaration | Source | Status |
|---|---|---|---|
| unbounded kernel as a subspace of `H` | `SpectralTriples.Dkernel` | `Index.lean` | ✓ axiom-clean |
| difference of the two graded kernel dimensions | `SpectralTriples.gradedKernelIndex` | `Index.lean` | ✓ axiom-clean |
| compact resolvent makes the full kernel finite-dimensional | `SpectralTriples.finiteDimensional_Dkernel` | `Index.lean` | ✓ axiom-clean |
| grading preserves the kernel | `SpectralTriples.grading_mem_Dkernel` | `Index.lean` | ✓ axiom-clean |
| invariant attached to an even core | `IsEvenSpectralTriple.gradedKernelIndex` | `Index.lean` | ✓ axiom-clean |

**Important boundary.** Lean has not yet defined the chiral restriction `D⁺`, proved its range
closed or cokernel finite-dimensional, or proved
`Fredholm.index D⁺ = gradedKernelIndex D γ`. Thus the formal invariant is not yet a formal
Fredholm index, even though that equality is the classical target.

## Reusable diagonal-operator infrastructure

| Informal object / claim | Lean declaration | Source | Status |
|---|---|---|---|
| uniformly bounded block-diagonal operator on `ℓ²` | `lpDiag.diagL` | `DiagonalOperator.lean` | ✓ axiom-clean |
| its operator-norm bound | `lpDiag.norm_diagL_le` | `DiagonalOperator.lean` | ✓ axiom-clean |
| finite-support block diagonals are compact | `lpDiag.isCompactOperator_diagL_of_support_finite` | `DiagonalOperator.lean` | ✓ axiom-clean |
| block norms tending to zero imply compactness | `lpDiag.isCompactOperator_diagL` | `DiagonalOperator.lean` | ✓ axiom-clean |
| maximal-domain unbounded block diagonal | `lpDiag.diracDirac` | `DiagonalOperator.lean` | ✓ axiom-clean |
| symmetric finite-dimensional blocks give a self-adjoint operator | `lpDiag.diracDirac_isSelfAdjoint` | `DiagonalOperator.lean` | ✓ axiom-clean |

## Concrete examples

| Example / claim | Lean declaration | Source | Status |
|---|---|---|---|
| odd circle core | `SpectralTriples.Circle.isOddSpectralTriple` | `Examples/Circle.lean` | ✓ axiom-clean |
| circle compact resolvent | `Circle.isCompactResolventSpectralTriple` | `Examples/Circle.lean` | ✓ axiom-clean |
| even flat-torus core | `Torus.isEvenSpectralTriple` | `Examples/Torus.lean` | ✓ axiom-clean |
| torus compact resolvent | `Torus.isCompactResolventSpectralTriple` | `Examples/Torus.lean` | ✓ axiom-clean |
| flat-torus graded-kernel invariant is zero | `Torus.gradedKernelIndex_eq_zero` | `Examples/Torus.lean` | ✓ axiom-clean |
| unilateral shift is Fredholm | `Shift.isFredholm_shift` | `Examples/Shift.lean` | ✓ axiom-clean |
| unilateral-shift index is `-1` | `Shift.fredholmIndex_shift` | `Examples/Shift.lean` | ✓ axiom-clean |
| bounded flux-`k` phase model | `MagneticDirac.magneticPhase` | `Examples/MagneticDirac.lean` | ✓ axiom-clean |
| phase model is Fredholm | `MagneticDirac.isFredholm_magneticPhase` | `Examples/MagneticDirac.lean` | ✓ axiom-clean |
| phase-model index is `k` | `MagneticDirac.fredholmIndex_magneticPhase` | `Examples/MagneticDirac.lean` | ✓ axiom-clean |
| clock/shift Weyl relation and commutation with the phase | `magneticTranslation_weyl`, `magClock_comm_dirac`, `magShift_comm_dirac` | `Examples/MagneticDirac.lean` | ✓ axiom-clean |

The magnetic phase is a bounded unweighted backward shift. The geometric Landau lowering
operator has `√(n+1)` weights and is unbounded, so no unitary equivalence between them is claimed.
The future bridge should identify the backward shift with the weighted operator’s polar phase,
or prove directly that they have the same kernel, cokernel, and index.

## Theta/Fourier function theory

| Function-theoretic claim | Lean declaration | Source | Status |
|---|---|---|---|
| explicit holomorphic automorphic theta functions | `ThetaSections.thetaSection`, `differentiable_thetaSection` | `Examples/ThetaSections.lean` | ✓ axiom-clean |
| lattice automorphy and translation eigenvalues | `thetaSection_periodic`, `thetaSection_quasiPeriodic`, `thetaSection_translate` | `Examples/ThetaSections.lean` | ✓ axiom-clean |
| the `k` theta functions are linearly independent | `thetaSection_linearIndependent` | `Examples/ThetaSections.lean` | ✓ axiom-clean |
| contour shift for entire periodic functions | `periodIntegral_eq_of_periodic` | `FourierHolomorphic.lean` | ✓ axiom-clean |
| Fourier recursion determines a section from `k` coefficients | `holCoeff_recursion`, `holSection_finrank_le` | `FourierHolomorphic.lean` | ✓ axiom-clean |
| exact positive-degree section count `finrank = k` | `holSection_finrank_eq` | `FourierHolomorphic.lean` | ✓ axiom-clean |
| the explicit theta family is a basis, with coordinate equivalence to `Fin k → ℂ` | `thetaHolSectionBasis`, `thetaHolSectionEquiv` | `FourierHolomorphic.lean` | ✓ axiom-clean |
| negative-degree section space is zero | `holSectionNeg_eq_bot`, `holSectionNeg_finrank_eq_zero` | `FourierHolomorphic.lean` | ✓ axiom-clean |

These are spaces of entire functions satisfying automorphy relations. No geometric
`L²(L_k)`, twisted `∂̄`, elliptic regularity, Serre duality, or operator kernel/cokernel
identification is formalized, so the table deliberately makes no operator-index claim.

## Hermite analysis

| Analytic claim | Lean declaration | Source | Status |
|---|---|---|---|
| `H'ₙ₊₁ = (n+1)Hₙ` | `Polynomial.derivative_hermite` | `HermiteL2.lean` | ✓ axiom-clean |
| polynomial times `e^{-x²/2}` is integrable | `Polynomial.integrable_aeval_mul_gaussian` | `HermiteL2.lean` | ✓ axiom-clean |
| weighted Hermite orthogonality and diagonal norm | `hermite_integral_eq_zero_of_ne`, `hermite_integral_self`, `hermite_orthogonality` | `HermiteL2.lean` | ✓ axiom-clean |
| normalized function `Hₙe^{-x²/4}/√(n!√(2π))` lies in `L²` | `hermiteFunctionL2` | `HermiteL2.lean` | ✓ axiom-clean |
| normalized family is orthonormal over `ℝ` or `ℂ` | `orthonormal_hermiteFunctionL2` | `HermiteL2.lean` | ✓ axiom-clean |

Completeness of this family—needed to construct a `HilbertBasis`—is still open.

## Reviewer-attention divergences

1. `IsOddSpectralTriple` / `IsEvenSpectralTriple` are core predicates without compact
   resolvent. `IsCompactResolventSpectralTriple` supplies that missing standard axiom.
2. Finite/`p`-summability is not formalized. The deprecated former name for the
   compact-resolvent structure must not be interpreted as a Schatten condition.
3. The commutator field is encoded as a finite `ℝ≥0∞` supremum on the unit ball of `dom D`.
   `boundedCommutator` now derives the literature-style continuous extension to all of `H`,
   with domain agreement and uniqueness proved by `boundedCommutator_apply` and
   `boundedCommutator_unique`.
4. `LinearPMap.resolventSet` uses algebraic bijectivity. For non-closed operators this can
   differ from the conventional definition, but spectral-triple `D` is closed.
5. `gradedKernelIndex` is not yet connected in Lean to a chiral Fredholm operator.
6. The theta/Fourier results are function-theoretic, and the magnetic result is a bounded
   phase model; the geometric operator bridge remains future work.

Keep this file, the README status table, the blueprint’s `\lean` declarations, and
[`scripts/axiom_report.lean`](../scripts/axiom_report.lean) synchronized whenever a headline
declaration changes.
