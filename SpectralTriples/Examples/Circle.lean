/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.SelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The Dirac spectral triple of the circle `S¹`

The simplest concrete (odd, finitely summable) spectral triple, built on the Fourier side so
that the Dirac operator is **diagonal**, bypassing spin bundles and Sobolev theory.

* `H = ℓ²(ℤ)` (`lp (fun _ : ℤ => ℂ) 2`), the Fourier model of `L²(S¹)` with orthonormal
  basis `(eₙ)_{n∈ℤ}`.
* `D = -i d/dθ`, acting diagonally as `eₙ ↦ n · eₙ`, with maximal domain
  `dom D = { a ∈ ℓ²(ℤ) : Σ n² |aₙ|² < ∞ }` (the `H¹` Sobolev space).
* `π : C^∞(S¹) → 𝓑(ℓ²(ℤ))` by Fourier convolution; `[D, π(f)] = π(-i f')` is bounded.

`D` is self-adjoint with **compact resolvent** (`(D + i)⁻¹` is diagonal with eigenvalues
`1/(n+i) → 0`), so the data is a finitely summable spectral triple at `z = i` — which the
`IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` constructor turns into the structure
without a separate `resolvent_mem` proof.

## Construction status and plan

The space, the `H¹` domain, and the **diagonal Dirac operator itself** (`diracDirac`) are
built and `sorry`-free; the remaining analytic core (self-adjointness, compact resolvent,
representation) is absent from Mathlib and is the multi-step work ahead — shared with the
`T²` example, which reuses the same diagonal-operator machinery over `ℤ²`.

1. **Diagonal operator** — done (`diracDirac`, with `diracDirac_apply : (D a)ₙ = n · aₙ`).
   To reuse for `T²`, generalize to eigenvalues `μ : ι → ℝ` over an arbitrary index `ι`.
2. **Self-adjointness** `IsSelfAdjoint diracDirac` (eigenvalues real): symmetry from
   `inner_eq_tsum` + reality of `μ`; the adjoint-domain inclusion from testing against
   `lp.single 2 n 1` (`inner_single_left/right`) to read off `(D† b)ₙ = μ n • bₙ`.
3. **Compact resolvent** `IsCompactOperator ((diagonalPMap μ).resolvent i)` when `|μ| → ∞`
   (proper level sets): the resolvent is the bounded diagonal operator `bₙ ↦ bₙ/(μ n + i)`,
   a norm limit of finite-rank truncations since `1/(μ n + i) → 0`.
4. **Representation** `π : C^∞(S¹) → (ℓ²(ℤ) →L[ℂ] ℓ²(ℤ))` by convolution with Fourier
   coefficients; `dom_comp` and the commutator bound `[D, π f] = π(f')` from rapid decay.
5. **Assemble** via `IsOddSpectralTriple` and
   `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple … (z := Complex.I)`.

See `IsSelfAdjoint.mem_resolventSet` (off-real-axis bijectivity) and
`IsSelfAdjoint.isClosed_range_subDirac` for the criterion this construction feeds.
-/

@[expose] public section

open LinearPMap

namespace SpectralTriples.Circle

/-- The Fourier model `ℓ²(ℤ)` of `L²(S¹)`: square-summable bi-infinite sequences of complex
numbers, a separable complex Hilbert space with orthonormal basis `(eₙ)_{n ∈ ℤ}`. -/
abbrev L2 : Type := lp (fun _ : ℤ => ℂ) 2

noncomputable instance : NormedAddCommGroup L2 := inferInstance
noncomputable instance : InnerProductSpace ℂ L2 := inferInstance
instance : CompleteSpace L2 := inferInstance

/-- The eigenvalues of the circle Dirac operator `D = -i d/dθ`: `D eₙ = n · eₙ`, so the `n`-th
eigenvalue is the real number `n`. These are real (hence `D` is symmetric) and satisfy
`|n| → ∞` (hence `D` has compact resolvent). -/
def diracEigen : ℤ → ℝ := fun n => (n : ℝ)

/-- The maximal domain of the circle Dirac operator: the `H¹` Sobolev space
`{ a ∈ ℓ²(ℤ) : Σ n² |aₙ|² < ∞ }`, i.e. those `a` for which `n ↦ n · aₙ` is again in `ℓ²(ℤ)`.
This is the domain on which the diagonal Dirac operator `(D a)ₙ = n · aₙ` will be defined. -/
def diracDomain : Submodule ℂ L2 where
  carrier := {a | Memℓp (fun n => (diracEigen n : ℂ) * a n) 2}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply, mul_add] at *
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at *
    have hrw : (fun n => (diracEigen n : ℂ) * (c * a n))
        = c • fun n => (diracEigen n : ℂ) * a n := by
      funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]; exact ha.const_smul c

theorem mem_diracDomain_iff (a : L2) :
    a ∈ diracDomain ↔ Memℓp (fun n => (diracEigen n : ℂ) * a n) 2 := Iff.rfl

/-- Coordinatewise multiplication by the eigenvalue sequence `(n)`, as an element of `ℓ²(ℤ)`,
given a proof that the result is square-summable. -/
def applyDirac (a : L2) (h : Memℓp (fun n => (diracEigen n : ℂ) * a n) 2) : L2 :=
  ⟨fun n => (diracEigen n : ℂ) * a n, h⟩

@[simp] theorem coe_applyDirac (a : L2) (h) (n : ℤ) :
    (applyDirac a h) n = (diracEigen n : ℂ) * a n := rfl

/-- The circle Dirac operator `D = -i d/dθ` as an unbounded `LinearPMap`: diagonal on the
Fourier basis, `(D a)ₙ = n · aₙ`, with domain the `H¹` Sobolev space `diracDomain`. -/
noncomputable def diracDirac : L2 →ₗ.[ℂ] L2 where
  domain := diracDomain
  toFun :=
    { toFun := fun a => applyDirac (a : L2) ((mem_diracDomain_iff _).mp a.2)
      map_add' := fun a b => by
        ext n
        simp only [coe_applyDirac, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        ext n
        simp only [coe_applyDirac, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, mul_left_comm] }

@[simp] theorem diracDirac_apply (a : diracDomain) (n : ℤ) :
    (diracDirac a) n = (diracEigen n : ℂ) * (a : L2) n := rfl

/- TODO (next steps), the analytic core (reusable for the `T²` example over `ℤ²`):
* `IsSelfAdjoint diracDirac` — symmetry from `inner_eq_tsum` + reality of `diracEigen`;
  the adjoint-domain inclusion by testing against `lp.single 2 n 1` (`inner_single_left/right`)
  to read off `(D† b)ₙ = n · bₙ`.
* `IsCompactOperator (diracDirac.resolvent Complex.I)` — the resolvent is the bounded diagonal
  operator `bₙ ↦ bₙ/(n+i)`, a norm limit of finite-rank truncations since `1/(n+i) → 0`.
Then assemble via `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple … (z := Complex.I)`. -/

end SpectralTriples.Circle
