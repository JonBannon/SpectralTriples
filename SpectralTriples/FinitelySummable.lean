/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.Basic
public import SpectralTriples.Resolvent
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Finitely summable spectral triples

In this file we define finitely summable spectral triples: odd spectral triples whose Dirac
operator `D` has a compact resolvent at some point `z` of its resolvent set.

## Main definitions

* `IsFinitelySummableSpectralTriple`

## Main results

* `IsSelfAdjoint.norm_resolvent_apply_ge`: for a self-adjoint operator `D` and any `z : 𝕜`,
  `|Im z| * ‖x‖ ≤ ‖(z • 1 - D) x‖` for `x ∈ D.domain`.
* `IsSelfAdjoint.injective_resolvent_apply`: consequently, `z • 1 - D` is injective whenever
  `Im z ≠ 0`.

-/

@[expose] public section

open LinearPMap

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

/-- For a self-adjoint operator `D` and any `z : 𝕜`, `|Im z| * ‖x‖ ≤ ‖(z • 1 - D) x‖` for
`x ∈ D.domain`.

This is the key estimate underlying the basic criterion of self-adjointness: it shows that
`z • 1 - D` is bounded below (hence injective) whenever `Im z ≠ 0`. -/
theorem IsSelfAdjoint.norm_resolvent_apply_ge {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D) (z : 𝕜)
    (x : D.domain) :
    |RCLike.im z| * ‖(x : H)‖ ≤ ‖z • (x : H) - D x‖ := by
  -- `D` self-adjoint, so `D.IsFormalAdjoint D`, i.e. `⟪D x, y⟫ = ⟪x, D y⟫` for `x y ∈ D.domain`.
  have hsa : D.IsFormalAdjoint D := by
    have hDD : D† = D := hD.star_eq
    have h := adjoint_isFormalAdjoint hD.dense_domain
    rwa [hDD] at h
  -- Hence `⟪x, D x⟫` is real.
  have hreal : (starRingEnd 𝕜) (inner 𝕜 (x : H) (D x)) = inner 𝕜 (x : H) (D x) := by
    have h1 : inner 𝕜 (D x) (x : H) = inner 𝕜 (x : H) (D x) := hsa x x
    calc (starRingEnd 𝕜) (inner 𝕜 (x : H) (D x))
        = (starRingEnd 𝕜) (inner 𝕜 (D x) (x : H)) := by rw [h1]
      _ = inner 𝕜 (x : H) (D x) := inner_conj_symm (x : H) (D x)
  have him : RCLike.im (inner 𝕜 (x : H) (D x)) = 0 := RCLike.conj_eq_iff_im.mp hreal
  have hw : inner 𝕜 (x : H) (z • (x : H) - D x) =
      z * inner 𝕜 (x : H) (x : H) - inner 𝕜 (x : H) (D x) := by
    rw [inner_sub_right, inner_smul_right]
  have him_w : RCLike.im (inner 𝕜 (x : H) (z • (x : H) - D x)) = RCLike.im z * ‖(x : H)‖ ^ 2 := by
    rw [hw, _root_.map_sub, him, sub_zero, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.im_mul_ofReal]
  have hbound : |RCLike.im z| * ‖(x : H)‖ ^ 2 ≤ ‖(x : H)‖ * ‖z • (x : H) - D x‖ := by
    calc |RCLike.im z| * ‖(x : H)‖ ^ 2
        = |RCLike.im z * ‖(x : H)‖ ^ 2| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(x : H)‖)]
      _ = |RCLike.im (inner 𝕜 (x : H) (z • (x : H) - D x))| := by rw [him_w]
      _ ≤ ‖inner 𝕜 (x : H) (z • (x : H) - D x)‖ := RCLike.abs_im_le_norm _
      _ ≤ ‖(x : H)‖ * ‖z • (x : H) - D x‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (x : H)) with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have h2 : ‖(x : H)‖ * (|RCLike.im z| * ‖(x : H)‖) ≤ ‖(x : H)‖ * ‖z • (x : H) - D x‖ := by
      have hring : ‖(x : H)‖ * (|RCLike.im z| * ‖(x : H)‖) = |RCLike.im z| * ‖(x : H)‖ ^ 2 := by
        ring
      rw [hring]
      exact hbound
    exact le_of_mul_le_mul_left h2 h0

/-- If `D` is self-adjoint and `Im z ≠ 0`, then `x ↦ z • x - D x` is injective on `D.domain`. -/
theorem IsSelfAdjoint.injective_resolvent_apply {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    Function.Injective (fun x : D.domain => z • (x : H) - D x) := by
  intro x y hxy
  simp only at hxy
  have hD' : D (x - y) = D x - D y := D.map_sub x y
  have hcoe : ((x - y : D.domain) : H) = (x : H) - (y : H) := rfl
  have hsub : z • ((x - y : D.domain) : H) - D (x - y) = 0 := by
    rw [hcoe, hD', smul_sub, sub_sub_sub_comm]
    exact sub_eq_zero.mpr hxy
  have hbound := hD.norm_resolvent_apply_ge z (x - y)
  rw [hsub, norm_zero, hcoe] at hbound
  have heq : |RCLike.im z| * ‖(x : H) - (y : H)‖ = 0 := le_antisymm hbound (by positivity)
  rcases mul_eq_zero.mp heq with h0 | h0
  · exact absurd (abs_eq_zero.mp h0) hz
  · exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h0))

/-- For a self-adjoint operator `D` and `z : 𝕜` with `Im z ≠ 0`, any vector orthogonal to the
range of `x ↦ z • x - D x` must be zero. Combined with the submodule orthogonality theory, this
gives density of the range. -/
private lemma inner_eq_zero_of_mem_ortho_resolvent_range {D : H →ₗ.[𝕜] H}
    (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) {y : H}
    (hy : ∀ x : D.domain, inner 𝕜 (z • (x : H) - D x) y = 0) : y = 0 := by
  have hdd := hD.dense_domain
  -- From ⟪z • x - D x, y⟫ = 0, derive star z * ⟪x, y⟫ = ⟪D x, y⟫.
  have hinner : ∀ x : D.domain,
      star z * inner 𝕜 (x : H) y = inner 𝕜 (D x) y := by
    intro x
    have h := hy x
    rw [inner_sub_left, inner_smul_left] at h
    exact sub_eq_zero.mp h
  -- Derive ⟪star z • y, x⟫ = ⟪y, D x⟫ by taking conjugates.
  have hadj : ∀ x : D.domain,
      inner 𝕜 (starRingEnd 𝕜 z • y) (x : H) = inner 𝕜 y (D x) := by
    intro x
    have lhs : inner 𝕜 (starRingEnd 𝕜 z • y) (x : H) = z * inner 𝕜 y (x : H) := by
      simp only [inner_smul_left, starRingEnd_apply, star_star]
    have rhs : inner 𝕜 y (D x) = z * inner 𝕜 y (x : H) :=
      calc inner 𝕜 y (D x)
          = starRingEnd 𝕜 (inner 𝕜 (D x) y)              := (inner_conj_symm y (D x)).symm
        _ = starRingEnd 𝕜 (star z * inner 𝕜 (x : H) y)   := by rw [← hinner x]
        _ = starRingEnd 𝕜 (star z) * starRingEnd 𝕜 (inner 𝕜 (x : H) y) := map_mul _ _ _
        _ = z * starRingEnd 𝕜 (inner 𝕜 (x : H) y)        := by
              simp only [starRingEnd_apply, star_star]
        _ = z * inner 𝕜 y (x : H)                        := by
              rw [inner_conj_symm y (x : H)]
    exact lhs.trans rhs.symm
  -- y lies in the adjoint domain: y ∈ D†.domain.
  have hmem : y ∈ D†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨starRingEnd 𝕜 z • y, hadj⟩
  -- D† y = star z • y.
  have happ : D† ⟨y, hmem⟩ = starRingEnd 𝕜 z • y :=
    LinearPMap.adjoint_apply_eq hdd ⟨y, hmem⟩ hadj
  -- D† is self-adjoint (since D† = D and D is self-adjoint).
  have hDA : D† = D := LinearPMap.isSelfAdjoint_def.mp hD
  have hDsa : IsSelfAdjoint D† := hDA.symm ▸ hD
  -- Apply the norm bound with w = starRingEnd 𝕜 z using the D† self-adjointness.
  have hzero : starRingEnd 𝕜 z • y - D† ⟨y, hmem⟩ = 0 := by rw [happ]; simp only [sub_self]
  have hbound := hDsa.norm_resolvent_apply_ge (starRingEnd 𝕜 z) ⟨y, hmem⟩
  rw [hzero, norm_zero] at hbound
  have him : |RCLike.im (starRingEnd 𝕜 z)| = |RCLike.im z| := by
    rw [RCLike.conj_im, abs_neg]
  rw [him] at hbound
  have heq : |RCLike.im z| * ‖y‖ = 0 := le_antisymm hbound (by positivity)
  rcases mul_eq_zero.mp heq with h | h
  · exact absurd (abs_eq_zero.mp h) hz
  · exact norm_eq_zero.mp h

/-- For a self-adjoint operator `D` and `z : 𝕜` with `Im z ≠ 0`, the range of `x ↦ z • x - D x`
(on `D.domain`) is dense in `H`.

This is the surjectivity half of the basic criterion of self-adjointness: together with
`IsSelfAdjoint.injective_resolvent_apply`, it shows `z ∈ ρ(D)`. -/
theorem IsSelfAdjoint.dense_range_resolvent_apply {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D)
    {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Dense (Set.range (fun x : D.domain => z • (x : H) - D x)) := by
  -- The range is the underlying set of a submodule (image of the linear map z - D).
  -- We prove density by showing that its orthogonal complement is ⊥.
  let zD : D.domain →ₗ[𝕜] H :=
    { toFun    := fun x => z • (x : H) - D x
      map_add' := fun x y => by simp [smul_add, D.map_add, sub_add_sub_comm]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, smul_sub, Submodule.coe_smul, D.map_smul, smul_comm z c] }
  have hrange : Set.range (fun x : D.domain => z • (x : H) - D x) = ↑(zD.range) := by
    ext v; simp [LinearMap.mem_range, zD]
  rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top,
      ← Submodule.orthogonal_orthogonal_eq_closure]
  suffices hbot : zD.rangeᗮ = ⊥ by rw [hbot]; exact Submodule.bot_orthogonal_eq_top
  ext y
  simp only [Submodule.mem_orthogonal, LinearMap.mem_range, Submodule.mem_bot]
  constructor
  · intro hy
    apply inner_eq_zero_of_mem_ortho_resolvent_range hD hz
    intro x
    exact hy (z • (x : H) - D x) ⟨x, rfl⟩
  · rintro rfl
    simp

/-- A spectral triple is finitely summable (with respect to `z`) if it is odd and its Dirac
operator has a compact resolvent at `z`. -/
structure IsFinitelySummableSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) (z : 𝕜)
    extends IsOddSpectralTriple A D π where
  resolvent_mem : z ∈ D.resolventSet
  compact_resolvent : IsCompactOperator (D.resolvent z)
