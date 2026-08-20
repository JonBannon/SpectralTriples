# Index pairing — roadmap from the magnetic phase model to geometric `T²`

*Status: implementation roadmap, synchronized with the Lean sources on 2026-08-20.
Classical geometric statements below are targets unless a Lean declaration is named.*

## What is proved now

The repository contains three related, but logically distinct, index computations.

| example | proved Lean declaration | result | scope |
|---|---|---:|---|
| flat `T²` spectral triple | `SpectralTriples.Torus.gradedKernelIndex_eq_zero` | `0` | `isEvenSpectralTriple.gradedKernelIndex = 0` |
| unilateral forward shift | `SpectralTriples.Shift.fredholmIndex_shift` | `−1` | bounded Fredholm index; `isFredholm_shift` proves well-definedness |
| flux-`k` magnetic phase | `SpectralTriples.MagneticDirac.fredholmIndex_magneticPhase` | `k` | bounded Fredholm index; `isFredholm_magneticPhase` proves well-definedness |

The first row is a difference of the two graded pieces of the kernel of the full
self-adjoint Dirac operator. It is **not yet** a theorem about a chiral restriction
`D⁺`, nor a formalized K-theoretic compression pairing. The other two rows use
`SpectralTriples.Fredholm.index` for explicit bounded operators whose kernel, closed
range, and cokernel have been computed.

The historical name `magneticDirac` denotes a bounded backward shift on
`ℓ²(ℕ × Fin k)`. New roadmap text calls it `magneticPhase`, its accurate public name:

```text
(magneticPhase k ψ) (n, j) = ψ (n + 1, j).
```

It has a `k`-dimensional kernel and is surjective. The formalized magnetic translations
`magClock` and `magShift` satisfy the Weyl relation and commute with this phase model.
The code does not yet identify them with unitary translations of a geometric line
bundle, nor prove an irreducibility theorem.

## Keep the three mathematical layers separate

### 1. Function theory — proved

For positive `k`, `ThetaSections.lean` and `FourierHolomorphic.lean` formalize entire
functions with the degree-`k` automorphy factors. In particular:

- `thetaSection_linearIndependent` constructs `k` linearly independent theta sections;
- `holSection_finrank_eq` proves the function space `holSection k` has dimension `k`;
- `thetaHolSectionBasis` packages those explicit sections as a basis;
- `holSectionNeg_eq_bot` proves the corresponding negative-degree holomorphic-section
  space is zero.

These are honest theorems about automorphic entire functions. They do **not** yet say
that `holSection k` is the kernel of a closed operator on a line-bundle `L²` space.
Likewise, `holSectionNeg_eq_bot` is not by itself a formalization of Serre duality,
`H¹(L_k) = 0`, or the cokernel of `D⁺_{L_k}`.

### 2. Bounded operator model — proved

`magneticPhase k` is the unweighted backward shift, the phase expected in the polar
decomposition of the Landau lowering operator. Its Fredholm index is `k`. This is a
complete bounded-operator result, including `k = 0`, but it is currently a model rather
than the geometric twisted Dirac operator.

### 3. Geometric operator — open

For `T² = ℂ / (ℤ + τℤ)`, `Im τ > 0`, and a positive degree-`k` line bundle `L_k`, the
classical target is

```text
D⁺_{L_k} = √2 ∂̄_A,
dim ker D⁺_{L_k} = k,
dim coker D⁺_{L_k} = 0,
index D⁺_{L_k} = k = c₁(L_k)[T²].
```

No `L²(T²; S ⊗ L_k)`, twisted `∂̄_A`, chiral restriction, or geometric Fredholm index
appears in Lean yet. Those identifications must be constructed rather than inferred from
the function-space and phase-model results.

## The correct weighted-to-unweighted bridge

Under a Landau-level unitary, the geometric chiral operator should become, up to a
nonzero scalar, the **unbounded weighted lowering operator**

```text
(a_k ψ) (n, j) = √(n + 1) ψ (n + 1, j),
```

on its natural weighted domain in `ℓ²(ℕ × Fin k)`. The weights are unbounded, so `a_k`
cannot be unitarily equivalent to the bounded operator `magneticPhase k`.

The intended bridge has two separate statements:

1. construct a unitary `U` with `U D⁺_{L_k} U⁻¹ = c • a_k` for `c ≠ 0`;
2. prove that the partial-isometry phase of `a_k` is `magneticPhase k` and justify
   equality of the relevant Fredholm indices.

This replaces the invalid shortcut `U D⁺ U⁻¹ = magneticDirac k`. Kernel and cokernel
dimensions happen to agree for the weighted lowering and its phase, but equality of
those dimensions—or an appropriate polar-decomposition theorem—still has to be proved
in the formal operator setting.

## Milestones

- **M1 — geometric Hilbert space and operator (open).** Define the weighted `L²` space
  of quasi-periodic sections of `L_k`, the covariant derivatives, and the densely defined
  closed operator `D⁺_{L_k}`. State domains and boundary identifications explicitly.

- **M2 — explicit positive-degree theta sections (done).** The theta functions,
  automorphy laws, nonvanishing, and linear independence are in
  `Examples/ThetaSections.lean`.

- **M3 — exact function-theoretic counts (done).** Fourier contour shift, coefficient
  recursion, completeness/identity-theorem argument, and the negative-degree vanishing
  theorem are in `FourierHolomorphic.lean`. The output is
  `finrank (holSection k) = k` and `holSectionNeg k = ⊥`, not an operator index.

- **MH — Hermite analysis (partly done).** `HermiteL2.lean` now defines the normalized
  probabilists' Hermite functions

  ```text
  h_n(x) = H_n(x) exp(-x²/4) / √(n! √(2π))
  ```

  and proves `orthonormal_hermiteFunctionL2`. The exponent is `−x²/4`: squaring the
  function produces the `exp(−x²/2)` weight in `hermite_orthogonality`. Completeness of
  this orthonormal family, and hence a packaged `HilbertBasis`, remain open.

- **M4 — weighted Landau decomposition (open).** Define `a_k`, prove its domain,
  closedness, adjoint/range/kernel facts, construct its phase, and identify that phase
  with `magneticPhase k`. Use Hermite completeness plus the guiding-center reduction to
  build the geometric Landau-level unitary.

- **M5 — operator/function comparison and geometric index (open).** Either use the
  Landau unitary directly or prove an elliptic-regularity/Weyl lemma identifying the
  `L²` kernels with the automorphic holomorphic spaces. Then prove chiral Fredholmness
  and transport the index `k`.

## Compact resolvent is not the missing chiral theorem

`CompactResolvent.lean` proves the basic self-adjoint resolvent criterion and packages
compact resolvent as `IsCompactResolventSpectralTriple`. `Index.lean` then proves that the
kernel of the **full self-adjoint** `D` is finite-dimensional and defines
`gradedKernelIndex`.

This does not by itself provide a Lean theorem that a geometric chiral restriction
`D⁺ : H⁺ → H⁻` is Fredholm. In particular, the current project must not cite compact
resolvent of `D` as though `IsFredholm D⁺` had already been assembled. For the bounded
magnetic phase, Fredholmness is instead proved directly by `isFredholm_magneticPhase`.

Compact resolvent is also strictly weaker than finite or `p`-summability. The repository
does not currently define Schatten-class summability; the old
`IsFinitelySummableSpectralTriple` spelling is only a deprecated compatibility alias for
the compact-resolvent structure.

## Recommended implementation order

1. Prove completeness of `hermiteFunctionL2` and package the family as a `HilbertBasis`.
2. Implement the closed weighted lowering operator `a_k` and its adjoint; compute its
   kernel and range directly.
3. Prove its polar phase is `magneticPhase k`, with a precise index-preservation lemma.
4. Construct the weighted quasi-periodic `L²` space and Landau/guiding-center unitary.
5. Identify the geometric operator with `a_k`; only then state the chiral Fredholm and
   geometric index theorems.

Route A (elliptic regularity for weak `∂̄_A` solutions) remains mathematically valid but
requires substantially more analysis than Route B (Hermite/Landau decomposition). The
completed orthonormal-family milestone makes Route B the nearer path, while completeness
is still its first blocking lemma.

## Verification targets for each bridge patch

- `lake build SpectralTriples`, `python3 scripts/check_axiom_coverage.py`, and
  `lake exe checkdecls blueprint/lean_decls` remain green;
- no `sorry`, `admit`, or unvetted new axiom is introduced;
- the weighted lowering is genuinely unbounded (do not package it as a
  `ContinuousLinearMap`);
- any claimed unitary intertwining includes operator domains;
- any use of `Fredholm.index` is accompanied by an `IsFredholm` theorem;
- function-theoretic theorems are not documented as kernel/cokernel theorems until the
  comparison map is formalized.

## Current dependency inventory

| need | status |
|---|---|
| Jacobi theta functions | present in Mathlib and used in `ThetaSections.lean` |
| exact positive/negative automorphic function counts | done in `FourierHolomorphic.lean` |
| normalized Hermite `L²` orthonormal family | done in `HermiteL2.lean` |
| Hermite completeness / `HilbertBasis` | open |
| weighted lowering operator and polar-phase identification | open |
| weighted quasi-periodic `L²` sections | open |
| elliptic regularity / Weyl lemma for `∂̄` | absent; optional alternative route |
| bounded Fredholm API and `1 − K` theorem | done in `Fredholm.lean` / `CompactOperators.lean` |
| bounded magnetic phase Fredholmness and index | done in `Examples/MagneticDirac.lean` |
| chiral Fredholm theorem for the geometric twisted Dirac | open |
