/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The Dirac spectral triple of the 2-torus `T²`

The simplest **even** (`Z₂`-graded) concrete spectral triple, built on the Fourier side. The
flat torus `T² = ℝ²/ℤ²` has trivial spin structure; the spinor bundle is rank 2, and on the
Fourier mode `(m, n) ∈ ℤ²` the Dirac operator acts on the spinor fibre `ℂ²` by the
self-adjoint block
`D₍ₘ,ₙ₎ = 2π (σ₁ m + σ₂ n) = 2π · !![0, m - i·n; m + i·n, 0]`,
with eigenvalues `± 2π √(m² + n²)`. The chirality is `γ = σ₃ = diag(1, -1)`.

* `H = ℓ²(ℤ²; ℂ²)` (`lp (fun _ : ℤ × ℤ => EuclideanSpace ℂ (Fin 2)) 2`), the Hilbert space.
* `D` is block-diagonal, self-adjoint, with `(D + i)⁻¹` compact (`|2π√(m²+n²)| → ∞`).
* `γ` is a self-adjoint unitary involution, commuting with the (scalar) representation and
  anticommuting with `D` (since each block is off-diagonal and `γ` is diagonal).

This reuses the `S¹` strategy (a diagonal operator on `lp 2`, self-adjointness by testing
against `lp.single`, compact resolvent by finite-rank truncation), upgraded from scalar
eigenvalues to **self-adjoint 2×2 blocks** on the spinor fibre.

## Construction status and plan

This file is the **scaffold**: the Hilbert space, the eigenvalue magnitude, and the `H¹`
domain are set up. The block-diagonal operator and the analytic core are the work ahead.

1. **Hilbert space** `H = ℓ²(ℤ²; ℂ²)` — done.
2. **Dirac block** `diracBlock (m,n) : ℂ² →L[ℂ] ℂ²`, the self-adjoint matrix above; then the
   block-diagonal `D : H →ₗ.[ℂ] H`, `(D a)₍ₘ,ₙ₎ = diracBlock (m,n) (a ₍ₘ,ₙ₎)`, on the `H¹`
   domain `diracDomain` below.
3. **Self-adjointness** `IsSelfAdjoint D`: the block version of the `S¹` argument — symmetry
   from `inner_eq_tsum` + self-adjointness of each block; the adjoint-domain inclusion by
   testing against `lp.single (m,n) eⱼ` for the fibre basis `eⱼ`.
4. **Compact resolvent** `IsCompactOperator (D.resolvent i)`: finite-rank truncation to
   `m² + n² ≤ N`, with the tail controlled by `1/(2π√(m²+n²)) → 0`.
5. **Grading** `γ : H →L[ℂ] H` (fibrewise `σ₃`): self-adjoint, `γ² = 1`, `γ D + D γ = 0`.
6. **Representation** `π : C^∞(T²) → 𝓑(H)` by Fourier convolution (scalar, so `[γ, π a] = 0`).
7. **Assemble** `IsEvenSpectralTriple`, and via
   `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` a finitely summable triple at `i`.
-/

@[expose] public section

open LinearPMap

namespace SpectralTriples.Torus

/-- The spinor fibre `ℂ²` (with its Hilbert-space structure). -/
abbrev Spinor : Type := EuclideanSpace ℂ (Fin 2)

/-- The Hilbert space `ℓ²(ℤ²; ℂ²)` of the `T²` Dirac triple: square-summable spinor-valued
sequences over the Fourier lattice `ℤ²`. -/
abbrev H : Type := lp (fun _ : ℤ × ℤ => Spinor) 2

noncomputable instance : NormedAddCommGroup H := inferInstance
noncomputable instance : InnerProductSpace ℂ H := inferInstance
instance : CompleteSpace H := inferInstance

/-- The magnitude of the Dirac eigenvalues on the Fourier mode `(m, n)`: the block
`2π(σ₁ m + σ₂ n)` has eigenvalues `± 2π √(m² + n²)`, all of magnitude `diracMagnitude (m, n)`.
This tends to `∞` as `(m, n) → ∞`, which is what makes the resolvent compact. -/
noncomputable def diracMagnitude : ℤ × ℤ → ℝ :=
  fun p => 2 * Real.pi * Real.sqrt ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)

/-- The Dirac block on the Fourier mode `(m, n)`: the self-adjoint matrix
`2π · !![0, m - i·n; m + i·n, 0]`, as a linear endomorphism of the spinor fibre `ℂ²`. -/
noncomputable def diracBlock (p : ℤ × ℤ) : Spinor →ₗ[ℂ] Spinor :=
  Matrix.toEuclideanLin <| (2 * Real.pi : ℂ) •
    !![0, (p.1 : ℂ) - (p.2 : ℂ) * Complex.I;
       (p.1 : ℂ) + (p.2 : ℂ) * Complex.I, 0]

/-- The maximal domain of the torus Dirac operator: the `H¹` Sobolev space, those `a` for which
`p ↦ D₍ₚ₎ (aₚ)` is again square-summable (equivalently `Σ (m²+n²) ‖aₚ‖² < ∞`). -/
def diracDomain : Submodule ℂ H where
  carrier := {a | Memℓp (fun p => diracBlock p (a p)) 2}
  zero_mem' := by
    have : (fun p => diracBlock p ((0 : H) p)) = 0 := by
      funext p; simp only [lp.coeFn_zero, Pi.zero_apply, _root_.map_zero]
    simp only [Set.mem_setOf_eq, this]; exact zero_memℓp
  add_mem' := fun {a b} ha hb => by
    have heq : (fun p => diracBlock p ((a + b) p))
        = (fun p => diracBlock p (a p)) + fun p => diracBlock p (b p) := by
      funext p; simp only [lp.coeFn_add, Pi.add_apply, _root_.map_add]
    rw [Set.mem_setOf_eq, heq]; exact ha.add hb
  smul_mem' := fun c a ha => by
    have heq : (fun p => diracBlock p ((c • a) p)) = c • fun p => diracBlock p (a p) := by
      funext p; simp only [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul]
    rw [Set.mem_setOf_eq, heq]; exact ha.const_smul c

theorem mem_diracDomain_iff (a : H) :
    a ∈ diracDomain ↔ Memℓp (fun p => diracBlock p (a p)) 2 := Iff.rfl

/-- Coordinatewise application of the Dirac blocks, as an element of `ℓ²(ℤ²; ℂ²)`, given a
proof that the result is square-summable. -/
noncomputable def applyDirac (a : H) (h : Memℓp (fun p => diracBlock p (a p)) 2) : H :=
  ⟨fun p => diracBlock p (a p), h⟩

@[simp] theorem coe_applyDirac (a : H) (h) (p : ℤ × ℤ) :
    (applyDirac a h) p = diracBlock p (a p) := rfl

/-- The torus Dirac operator as an unbounded `LinearPMap`: block-diagonal on the Fourier
lattice, `(D a)₍ₘ,ₙ₎ = D₍ₘ,ₙ₎ (a₍ₘ,ₙ₎)`, with domain the `H¹` Sobolev space `diracDomain`. -/
noncomputable def diracDirac : H →ₗ.[ℂ] H where
  domain := diracDomain
  toFun :=
    { toFun := fun a => applyDirac (a : H) ((mem_diracDomain_iff _).mp a.2)
      map_add' := fun a b => by
        refine lp.ext (funext fun p => ?_)
        simp only [coe_applyDirac, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, _root_.map_add]
      map_smul' := fun c a => by
        refine lp.ext (funext fun p => ?_)
        simp only [coe_applyDirac, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
          _root_.map_smul, RingHom.id_apply] }

@[simp] theorem diracDirac_apply (a : diracDomain) (p : ℤ × ℤ) :
    (diracDirac a) p = diracBlock p ((a : H) p) := rfl

end SpectralTriples.Torus
