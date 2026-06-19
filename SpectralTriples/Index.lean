/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # The index of an even spectral triple

For an **even** spectral triple the grading `γ` splits the kernel of the Dirac operator
`D` into its `±1`-eigenspaces, `ker D = (ker D)⁺ ⊕ (ker D)⁻`, and the **(super)index**

  `index D γ = dim (ker D)⁺ − dim (ker D)⁻`

is the Fredholm index of the chiral operator `D⁺ : H⁺ → H⁻`. This is the integer that the
Atiyah–Singer / McKean–Singer theory computes as `∫ Â(M) · ch(E)`; for the torus coupled to a
degree-`k` line bundle it equals `k`.

This file builds the **foundations**: the graded kernel, the index as an integer, and the
well-definedness theorem — that the kernel is finite-dimensional whenever `D` has compact
resolvent (so the two dimensions, and hence the index, are genuine). The point is that the
**compact resolvent makes `D⁺` Fredholm**: `ker D` embeds into a nonzero-eigenvalue eigenspace
of the (compact) resolvent, which is finite-dimensional by Riesz theory.

## Main definitions

* `SpectralTriples.Dkernel D` — `ker D`, as a subspace of `H`.
* `SpectralTriples.index D γ` — the graded-kernel index, an integer.

## Main results

* `SpectralTriples.finiteDimensional_Dkernel` — `ker D` is finite-dimensional when `D` is
  self-adjoint with compact resolvent at `i`.
-/

@[expose] public section

namespace SpectralTriples

open LinearPMap Module Module.End

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

/-- The kernel of an unbounded operator `D : H →ₗ.[𝕜] H`, as a subspace of `H`: the vectors in
`dom D` annihilated by `D`. -/
noncomputable def Dkernel (D : H →ₗ.[𝕜] H) : Submodule 𝕜 H :=
  (LinearMap.ker D.toFun).map D.domain.subtype

omit [CompleteSpace H] in
theorem mem_Dkernel_iff (D : H →ₗ.[𝕜] H) {x : H} :
    x ∈ Dkernel D ↔ ∃ hx : x ∈ D.domain, D ⟨x, hx⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, LinearMap.mem_ker.mp hy⟩
  · rintro ⟨hx, h0⟩
    exact ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr h0, rfl⟩

/-- The (super)index of an even Dirac datum `(D, γ)`: the difference of the dimensions of the
`+1`- and `−1`-graded parts of `ker D`. (Each `finrank` is `0` when the corresponding space is
infinite-dimensional; `finiteDimensional_Dkernel` guarantees finiteness under a compact
resolvent.) -/
noncomputable def index (D : H →ₗ.[𝕜] H) (γ : H →L[𝕜] H) : ℤ :=
  (finrank 𝕜 (Dkernel D ⊓ eigenspace (γ : Module.End 𝕜 H) 1 :) : ℤ)
    - (finrank 𝕜 (Dkernel D ⊓ eigenspace (γ : Module.End 𝕜 H) (-1) :) : ℤ)

/-- **The kernel of a Dirac operator with compact resolvent is finite-dimensional.** This is the
Fredholm property: for `x ∈ ker D`, the resolvent `R = (i·1 − D)⁻¹` satisfies `R x = i⁻¹ • x`, so
`ker D` embeds into the `i⁻¹`-eigenspace of the compact operator `R`, which is finite-dimensional
by Riesz theory. Consequently `index D γ` is a difference of genuine (finite) dimensions. -/
theorem finiteDimensional_Dkernel {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D)
    (hI : RCLike.im (RCLike.I : 𝕜) ≠ 0)
    (hc : IsCompactOperator (D.resolvent RCLike.I)) :
    FiniteDimensional 𝕜 (Dkernel D) := by
  have hI0 : (RCLike.I : 𝕜) ≠ 0 := fun h => hI (by rw [h]; simp)
  have hz : RCLike.I ∈ D.resolventSet := hD.mem_resolventSet hI
  set Res : H →L[𝕜] H := ⟨D.resolvent RCLike.I, hc.continuous⟩ with hRes
  have hcRes : IsCompactOperator Res := hc
  haveI hfd : FiniteDimensional 𝕜 (eigenspace Res.toLinearMap ((RCLike.I : 𝕜)⁻¹)) :=
    Res.finite_dimensional_eigenspace hcRes ((RCLike.I : 𝕜)⁻¹) (inv_ne_zero hI0)
  have hle : Dkernel D ≤ eigenspace Res.toLinearMap ((RCLike.I : 𝕜)⁻¹) := by
    intro x hx
    rw [mem_Dkernel_iff] at hx
    obtain ⟨hxdom, hx0⟩ := hx
    rw [mem_eigenspace_iff]
    -- The resolvent inverts `i·1 − D`; for `x ∈ ker D` this reads `R (i • x) = x`.
    have key : D.resolvent RCLike.I ((RCLike.I : 𝕜) • x) = x := by
      have hop : ((RCLike.I : 𝕜) • x : H)
          = (((RCLike.I : 𝕜) • LinearMap.id (R := 𝕜) (M := H)) +ᵥ (-D) : H →ₗ.[𝕜] H)
            ⟨x, hxdom⟩ := by
        simp only [LinearPMap.vadd_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          LinearPMap.neg_apply, hx0, neg_zero, add_zero]
      rw [hop, LinearPMap.resolvent_apply_eq (f := D) hz]
      exact LinearPMap.apply_inverseAsLinearMap_apply_cancel hz ⟨x, hxdom⟩
    have hlin : (RCLike.I : 𝕜) • (D.resolvent RCLike.I x) = x := by
      rw [← _root_.map_smul]; exact key
    change Res.toLinearMap x = (RCLike.I : 𝕜)⁻¹ • x
    have hRx : Res.toLinearMap x = D.resolvent RCLike.I x := rfl
    rw [hRx, eq_inv_smul_iff₀ hI0]
    exact hlin
  exact Submodule.finiteDimensional_of_le hle

/-! ### The index of an even spectral triple -/

variable {A : Type*} [Semiring A] [StarRing A] [Algebra 𝕜 A]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)} {γ : H →L[𝕜] H}

/-- The grading of an even spectral triple preserves the kernel of `D`: if `D x = 0` then
`D (γ x) = -γ (D x) = 0`. Hence `ker D` is `γ`-invariant, and splits into its `±1`-graded parts
whose dimensions enter `index`. -/
theorem grading_mem_Dkernel (hT : IsEvenSpectralTriple A D π γ) {x : H}
    (hx : x ∈ Dkernel D) : γ x ∈ Dkernel D := by
  rw [mem_Dkernel_iff] at hx ⊢
  obtain ⟨hxdom, hx0⟩ := hx
  refine ⟨hT.grading_dom ⟨x, hxdom⟩, ?_⟩
  have h := hT.grading_anticomm ⟨x, hxdom⟩
  rw [hx0, _root_.map_zero, neg_zero] at h
  exact h

/-- The **index** of an even spectral triple `(A, H, D, γ)`: the graded-kernel index of its
Dirac operator. Combined with `finiteDimensional_Dkernel` (under a compact resolvent), this is a
genuine integer — the Fredholm index of `D⁺`. -/
noncomputable def _root_.IsEvenSpectralTriple.index (_hT : IsEvenSpectralTriple A D π γ) : ℤ :=
  SpectralTriples.index D γ

end SpectralTriples
