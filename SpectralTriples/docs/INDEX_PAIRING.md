# Index pairing — roadmap for connecting the magnetic model to the geometric `T²`

*Status: design / scoping. No Lean yet for the items marked **TODO**. Companion to
[`DESIGN.md`](DESIGN.md). The formalized pieces referenced below are on `main`.*

## Where we are

Three index examples are formalized, sorry-free and axiom-clean:

| example | Lean | index |
|---|---|---|
| flat `T²` Dirac (degree 0) | `SpectralTriples.Torus.index_eq_zero` | `0` |
| unilateral shift / Toeplitz (`S¹`, odd) | `SpectralTriples.Shift.fredholmIndex_shift` | `−1` |
| flux-`k` magnetic Dirac (`T²`, even) — **model** | `SpectralTriples.MagneticDirac.fredholmIndex_magneticDirac` | `k` |

The flux-`k` result is proved for the **Landau-level / magnetic-translation model**
`magneticDirac k` on `ℓ²(ℕ) ⊗ ℂᵏ` (backward shift ⊗ `1`), with the magnetic translations
`magClock`/`magShift` realizing the Weyl relation `Ĉ Ŝ = ω Ŝ Ĉ` (`ω = e^{2πi/k}`) and
commuting with the Dirac operator. What it does **not** yet prove is that this model *is* the
Dirac operator of the geometric torus coupled to a degree-`k` line bundle. **This doc scopes
that bridge.**

## The goal

Establish a unitary equivalence

  `U : L²(T²; S ⊗ L_k) ≅ ℓ²(ℕ) ⊗ ℂᵏ ⊗ ℂ²`,  `U D⁺_{L_k} U⁻¹ = (lowering) ⊗ 1_{ℂᵏ}`,

so that `index(D⁺_{L_k}) = index(magneticDirac k) = k = c₁(L_k)`. This upgrades the model's
`index = k` to the **geometric** statement (`= deg L_k = ∫_{T²} c₁(L_k)`), i.e. a genuine,
if special, case of Atiyah–Singer / Riemann–Roch on `T²`.

## The geometric side (precise setup)

Write `T² = ℂ / Λ`, `Λ = ℤ + ℤτ`, `Im τ > 0` (specialize to `τ = i` first). The degree-`k`
line bundle `L_k` is given by the factor of automorphy

  `ψ(z + 1) = ψ(z)`,  `ψ(z + τ) = e^{-πi k (2z + τ)} ψ(z)`,

i.e. sections are entire-in-the-fibre functions on `ℂ` with this quasi-periodicity. A
constant-curvature connection gives the magnetic field `B` with `∫_{T²} B = 2πk`. On the
trivial spin structure, the chiral Dirac operator is (up to a positive constant and the
`K^{1/2}` twist, which has degree 0 on `T²`)

  `D⁺_{L_k} = √2 · ∂̄_{A}`  on `L²(T²; S⁺ ⊗ L_k)`,

the `∂̄` operator twisted by the connection `A`.

### Kernel and cokernel (the answer we are targeting)

- `ker D⁺_{L_k} = H⁰(T², L_k) =` holomorphic sections `=` span of the **`k` theta functions
  with characteristics** `θ[a/k, 0](k z, k τ)`, `a = 0, …, k−1`. So `dim ker D⁺ = k`.
- `ker D⁻_{L_k} = H¹(T², L_k) = 0` for `k > 0` (Serre duality: `h¹(L_k) = h⁰(L_k^{-1}) = 0`
  since `deg L_k^{-1} < 0`).
- `index = k − 0 = k`.

## The bridge: magnetic-translation diagonalization

The magnetic translations `U_a` (`a ∈ Λ/k`) commute with `D` and generate the finite
Heisenberg group with `U₁ U₂ = ω U₂ U₁`. Decompose

  `L²(T²; S⁺ ⊗ L_k) ≅ ⨁_{n ∈ ℕ} (Landau level n)`,   `Landau level n ≅ ℂᵏ`,

where `n` is the eigenvalue index of the magnetic harmonic oscillator `a†a` and the `ℂᵏ` is
the guiding-center degeneracy carrying the Heisenberg `k`-dim irrep. Under this decomposition
`D⁺` is the oscillator lowering `a` (`a : level n → level n−1`, `ker a = level 0 ≅ ℂᵏ`),
i.e. exactly the model `magneticDirac k` (a backward shift on `ℕ` ⊗ `1_{ℂᵏ}`; the geometric
`a` carries the `√n` weights but has the *same* kernel/cokernel/index).

## Crux lemmas (what must be proved) — milestones

- **M1 — geometric Hilbert space + operator (TODO).** `L²` of quasi-periodic sections of
  `L_k` (as a closed subspace of `L²_{loc}(ℂ)` cut out by the automorphy factor, or `L²` of a
  fundamental domain with the twisted boundary identification), and the twisted `∂̄_A` as a
  densely-defined unbounded operator. *Mathlib gap:* no line-bundle `L²`-sections; build by
  hand. Reuse our `LinearPMap` self-adjoint/resolvent API for the operator-theoretic layer.

- **M2 — lower bound `dim ker ≥ k` (TODO; most tractable).** Construct the `k` explicit
  zero modes via `jacobiTheta₂` (Mathlib **has** `Mathlib.NumberTheory.ModularForms.JacobiTheta`),
  verify they satisfy the automorphy factor and `∂̄_A ψ_a = 0`, and prove linear independence
  (their theta-characteristics differ ⇒ distinct quasi-periodicities ⇒ independent). This is a
  genuine, self-contained result: *the flux-`k` Dirac has at least `k` Landau ground states.*

- **M3 — upper bound `dim ker = k` and `coker = 0` (TODO; the research frontier).** The
  completeness half. The *index-theorem route* (`index = ∫ Â ch = c₁ = k`) is **Mathlib-blocked**
  (no Atiyah–Singer). Instead use the **Fourier-coefficient recursion** — an *algebraic* route
  that needs no `L²`/ODE machinery for the holomorphic count, splitting M3 into three pieces:

  - **M3a — the holomorphic-section space is *exactly* `k`-dimensional (recommended next; tractable).**
    A holomorphic section `ψ` of `L_k` is entire with `ψ(z+1) = ψ(z)`, so it has a Laurent/`q`-expansion
    `ψ(z) = ∑_{m ∈ ℤ} a_m e^{2πimz}` (`q = e^{2πiz}`). The `τ`-quasi-periodicity
    `ψ(z+τ) = e^{-πik(2z+τ)}ψ(z)` forces, comparing coefficients of `e^{2πimz}`, the **recursion**

    > `a_{m+k} = e^{πiτ(2m+k)} a_m`.

    So the whole coefficient sequence is determined by `(a_0, …, a_{k-1})`, and the restriction map
    `ψ ↦ (a_0,…,a_{k-1})` is an **injective** linear map into `ℂᵏ` (injectivity: `a_0=…=a_{k-1}=0`
    ⇒ all `a_m = 0` ⇒ `ψ = 0` by Fourier completeness + the identity theorem), giving `dim ≤ k`.
    With **M2** (`≥ k`) this yields `dim H⁰(L_k) = k`, with **no index theorem and no `L²` analysis**.

    *The one genuine analytic crux* (not yet in Mathlib): extracting the `a_m` and deriving the
    recursion. The right tool is **`fourierCoeff` on `AddCircle 1`** applied to the line-restrictions
    `ψ(· + iy)` — **not** `Function.Periodic.cuspFunction`, which assumes the section is meromorphic
    at the cusp; here the theta sections **grow like `e^{πk(Im z)²}`** (Gaussian, intrinsic to a
    positive line bundle), so `cuspFunction` does not apply. The recursion comes from the
    **holomorphic contour-shift** `fourierCoeff(ψ(·+iy)) m = a_m · e^{−2πmy}` (relating coefficients on
    different horizontal lines via Cauchy/holomorphy) combined with the τ-quasi-periodicity. That
    contour-shift is the substantive lemma to build; given it, the recursion + injectivity is easy.

  - **M3b — `coker = 0` (`H¹(L_k) = 0` for `k > 0`).** The anti-holomorphic sections (`ker D⁻`)
    satisfy the *conjugate* recursion `a_{m+k} = e^{-πiτ̄(…)} a_m`, whose factor has modulus `> 1`,
    forcing `|a_m| → ∞` — no nonzero convergent (entire) solution. So `dim ker D⁻ = 0`, again
    algebraically. (Equivalently, Serre duality `h¹(L_k) = h⁰(L_k^{-1}) = 0`, `deg < 0`.)

  - **M3c — `L²` ↔ holomorphic (elliptic regularity).** Connects the *operator* kernel
    `ker D⁺ ⊆ L²(L_k)` to the *entire* holomorphic sections counted in M3a/M2 (an `L²` solution of
    `∂̄ψ = 0` is smooth/holomorphic). This is the genuinely analytic piece and the real Mathlib gap
    (no elliptic regularity for `∂̄` on the torus). M3a+M2+M3b already give the *function-theoretic*
    answer `dim H⁰(L_k) = k`, `dim H¹ = 0`; M3c (with M1/M4) upgrades it to the operator.

  Mathlib inventory for M3a: `fourierCoeff`/`AddCircle` and Fourier completeness are present; the
  recursion and injectivity are then elementary. The **one piece to build is the contour-shift**
  `fourierCoeff(ψ(·+iy)) m = a_m e^{−2πmy}` (a Cauchy/holomorphy lemma). **M3a is the recommended next
  build**, modulo that single analytic lemma; it closes the dimension count to exactly `k`.

- **M4 — the unitary equivalence to the model (TODO).** Assemble `U` from M1–M3:
  `U D⁺_{L_k} U⁻¹ = magneticDirac k` (or the oscillator-lowering variant with the same index),
  and identify the geometric magnetic translations with `magClock`/`magShift`. Then
  `index(D⁺_{L_k}) = fredholmIndex (magneticDirac k) = k` transports the **formalized** model
  result to the geometric operator.

## Progress / recommended next step

- **M2 — done** (`SpectralTriples.Examples.ThetaSections`, `thetaSection_linearIndependent`):
  `dim H⁰(L_k) ≥ k` via the `k` explicit theta zero modes. Sorry-free, axiom-clean.
- **M3a — done** (`SpectralTriples.FourierHolomorphic`): the upper bound `dim ≤ k` via the
  contour shift (`periodIntegral_eq_of_periodic`) + the Fourier-coefficient recursion
  (`holCoeff_recursion`) + completeness (`eq_zero_of_holCoeff_eq_zero`, through the lift to
  `AddCircle 1` and Mathlib's Fourier completeness + the identity theorem). Combined with M2 this
  gives the **exact** count `holSection_finrank_eq : dim H⁰(L_k) = k` — a complete dimension
  theorem with **no index theorem and no `L²` analysis**. Sorry-free, axiom-clean.
- **M3b — done** (`SpectralTriples.FourierHolomorphic`): `coker = 0`. `holSectionNeg_eq_bot` —
  the holomorphic sections of `L_{-k}` vanish, via the opposite-sign recursion
  (`holCoeffNeg_recursion`, growth factor `> 1`) clashing with Parseval coefficient decay
  (`holCoeff_tendsto_atTop_zero`) ⇒ all coefficients `0` ⇒ `f = 0`. By Serre duality this is
  `H¹(L_k) = 0 = coker D⁺`. Sorry-free, axiom-clean.
- **M3c / M1 / M4** (the `L²`/elliptic-regularity bridge from the operator kernel to the
  holomorphic sections, and the unitary equivalence to `magneticDirac k`) — the genuinely analytic
  frontier, where the only true Mathlib gap lives (no elliptic regularity / index theorem).

## Mathlib inventory (for the bridge)

| need | status |
|---|---|
| Jacobi theta functions `jacobiTheta₂(z, τ)` | ✅ `Mathlib.NumberTheory.ModularForms.JacobiTheta` |
| Gaussian integrals, Hermite polynomials | ✅ present (analysis / special functions) |
| `L²` sections of a line bundle / quasi-periodic `L²` | ❌ build by hand |
| theta functions *with characteristics*, their dimension `= k` | ❌ build (from `jacobiTheta₂`) |
| Atiyah–Singer / Riemann–Roch / Kodaira vanishing | ❌ absent (use the explicit Fourier/Gaussian route instead) |
| magnetic translations / finite Heisenberg irrep | ✅ formalized in `MagneticDirac.lean` (`magClock`/`magShift`, Weyl relation) |
