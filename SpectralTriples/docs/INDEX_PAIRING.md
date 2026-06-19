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

- **M3 — upper bound `dim ker = k` and `coker = 0` (TODO; hard).** The completeness half.
  Two possible routes:
  - *Index-theorem route:* `index = ∫ Â ch = c₁ = k`. **Mathlib-blocked** (no Atiyah–Singer).
  - *Explicit Fourier/Gaussian route:* expand a section in the quasi-periodic Fourier basis;
    the `∂̄_A ψ = 0` equation becomes, per guiding center, a first-order ODE whose `L²`
    solution is a unique Gaussian. Counting guiding centers gives exactly `k`, and the
    `n ≥ 1` levels are non-zero-energy (so `coker = 0`). This avoids abstract index theory but
    needs Gaussian-integral / Hermite-function analysis. *Mathlib has* Gaussian integrals and
    Hermite polynomials, so this route is feasible but substantial.

- **M4 — the unitary equivalence to the model (TODO).** Assemble `U` from M1–M3:
  `U D⁺_{L_k} U⁻¹ = magneticDirac k` (or the oscillator-lowering variant with the same index),
  and identify the geometric magnetic translations with `magClock`/`magShift`. Then
  `index(D⁺_{L_k}) = fredholmIndex (magneticDirac k) = k` transports the **formalized** model
  result to the geometric operator.

## Recommended next step

**M2** (the theta-function lower bound). It uses real Mathlib infrastructure
(`jacobiTheta₂`), is self-contained, and delivers a genuine geometric statement (`≥ k` ground
states for flux `k`) without the index-theorem ceiling. M3/M4 are the research frontier; M3 is
where the only true Mathlib gap lives (no index theorem — the Gaussian/Fourier completeness is
the realistic path).

## Mathlib inventory (for the bridge)

| need | status |
|---|---|
| Jacobi theta functions `jacobiTheta₂(z, τ)` | ✅ `Mathlib.NumberTheory.ModularForms.JacobiTheta` |
| Gaussian integrals, Hermite polynomials | ✅ present (analysis / special functions) |
| `L²` sections of a line bundle / quasi-periodic `L²` | ❌ build by hand |
| theta functions *with characteristics*, their dimension `= k` | ❌ build (from `jacobiTheta₂`) |
| Atiyah–Singer / Riemann–Roch / Kodaira vanishing | ❌ absent (use the explicit Fourier/Gaussian route instead) |
| magnetic translations / finite Heisenberg irrep | ✅ formalized in `MagneticDirac.lean` (`magClock`/`magShift`, Weyl relation) |
