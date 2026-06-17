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

In this file we prove the basic criterion of self-adjointness (`Im z ≠ 0 → z ∈ ρ(D)`) and use
it to define finitely summable spectral triples: odd spectral triples whose Dirac operator has
compact resolvent at the imaginary unit `RCLike.I`.

## Main definitions

* `IsFinitelySummableSpectralTriple`: an odd spectral triple whose Dirac operator has compact
  resolvent at `RCLike.I`.

## Main results

* `IsSelfAdjoint.norm_resolvent_apply_ge`: `|Im z| * ‖x‖ ≤ ‖(z • 1 - D) x‖`.
* `IsSelfAdjoint.injective_resolvent_apply`: `z • 1 - D` is injective when `Im z ≠ 0`.
* `IsSelfAdjoint.dense_range_resolvent_apply`: the range of `z • 1 - D` is dense when `Im z ≠ 0`.
* `IsSelfAdjoint.isClosed_range_subDirac`: the range is also closed.
* `IsSelfAdjoint.mem_resolventSet`: combining the above, `z ∈ ρ(D)` when `Im z ≠ 0`.
* `IsOddSpectralTriple.mem_resolventSet`: corollary at the level of spectral triples.
* `IsFinitelySummableSpectralTriple.resolvent_mem`: field asserting `RCLike.I ∈ ρ(D)`.

-/

@[expose] public section

open LinearPMap

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

/-! ### Basic estimate and injectivity -/

/-- For a self-adjoint operator `D` and any `z : 𝕜`, `|Im z| * ‖x‖ ≤ ‖(z • 1 - D) x‖` for
`x ∈ D.domain`.

This is the key estimate underlying the basic criterion of self-adjointness: it shows that
`z • 1 - D` is bounded below (hence injective) whenever `Im z ≠ 0`. -/
theorem IsSelfAdjoint.norm_resolvent_apply_ge {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D) (z : 𝕜)
    (x : D.domain) :
    |RCLike.im z| * ‖(x : H)‖ ≤ ‖z • (x : H) - D x‖ := by
  have hsa : D.IsFormalAdjoint D := by
    have hDD : D† = D := hD.star_eq
    have h := adjoint_isFormalAdjoint hD.dense_domain
    rwa [hDD] at h
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
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have h2 : ‖(x : H)‖ * (|RCLike.im z| * ‖(x : H)‖) ≤ ‖(x : H)‖ * ‖z • (x : H) - D x‖ := by
      have hring : ‖(x : H)‖ * (|RCLike.im z| * ‖(x : H)‖) = |RCLike.im z| * ‖(x : H)‖ ^ 2 := by
        ring
      rw [hring]; exact hbound
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
    rw [hcoe, hD', smul_sub, sub_sub_sub_comm]; exact sub_eq_zero.mpr hxy
  have hbound := hD.norm_resolvent_apply_ge z (x - y)
  rw [hsub, norm_zero, hcoe] at hbound
  have heq : |RCLike.im z| * ‖(x : H) - (y : H)‖ = 0 := le_antisymm hbound (by positivity)
  rcases mul_eq_zero.mp heq with h0 | h0
  · exact absurd (abs_eq_zero.mp h0) hz
  · exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h0))

/-! ### Density of the range -/

/-- Any vector orthogonal to the range of `x ↦ z • x - D x` must be zero. -/
private lemma inner_eq_zero_of_mem_ortho_resolvent_range {D : H →ₗ.[𝕜] H}
    (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) {y : H}
    (hy : ∀ x : D.domain, inner 𝕜 (z • (x : H) - D x) y = 0) : y = 0 := by
  have hdd := hD.dense_domain
  have hinner : ∀ x : D.domain,
      star z * inner 𝕜 (x : H) y = inner 𝕜 (D x) y := by
    intro x
    have h := hy x
    rw [inner_sub_left, inner_smul_left] at h
    exact sub_eq_zero.mp h
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
        _ = z * starRingEnd 𝕜 (inner 𝕜 (x : H) y) :=
              by simp only [starRingEnd_apply, star_star]
        _ = z * inner 𝕜 y (x : H)                        := by rw [inner_conj_symm y (x : H)]
    exact lhs.trans rhs.symm
  have hmem : y ∈ D†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨starRingEnd 𝕜 z • y, hadj⟩
  have happ : D† ⟨y, hmem⟩ = starRingEnd 𝕜 z • y :=
    LinearPMap.adjoint_apply_eq hdd ⟨y, hmem⟩ hadj
  have hDA : D† = D := LinearPMap.isSelfAdjoint_def.mp hD
  have hDsa : IsSelfAdjoint D† := hDA.symm ▸ hD
  have hzero : starRingEnd 𝕜 z • y - D† ⟨y, hmem⟩ = 0 := by rw [happ]; simp only [sub_self]
  have hbound := hDsa.norm_resolvent_apply_ge (starRingEnd 𝕜 z) ⟨y, hmem⟩
  rw [hzero, norm_zero] at hbound
  have him : |RCLike.im (starRingEnd 𝕜 z)| = |RCLike.im z| := by rw [RCLike.conj_im, abs_neg]
  rw [him] at hbound
  have heq : |RCLike.im z| * ‖y‖ = 0 := le_antisymm hbound (by positivity)
  rcases mul_eq_zero.mp heq with h | h
  · exact absurd (abs_eq_zero.mp h) hz
  · exact norm_eq_zero.mp h

/-- For a self-adjoint operator `D` and `z : 𝕜` with `Im z ≠ 0`, the range of `x ↦ z • x - D x`
(on `D.domain`) is dense in `H`. -/
theorem IsSelfAdjoint.dense_range_resolvent_apply {D : H →ₗ.[𝕜] H} (hD : IsSelfAdjoint D)
    {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Dense (Set.range (fun x : D.domain => z • (x : H) - D x)) := by
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
    intro x; exact hy (z • (x : H) - D x) ⟨x, rfl⟩
  · rintro rfl; simp

/-! ### Closed range and the basic criterion -/

namespace IsSelfAdjoint

variable {D : H →ₗ.[𝕜] H}

/-- The operator `z • 1 - D`, restricted to `D.domain`, packaged as a `LinearMap`. -/
noncomputable def subDirac (D : H →ₗ.[𝕜] H) (z : 𝕜) : D.domain →ₗ[𝕜] H :=
  z • D.domain.subtype - D.toFun

omit [CompleteSpace H] in
@[simp] theorem subDirac_apply (z : 𝕜) (x : D.domain) :
    subDirac D z x = z • (x : H) - D x := rfl

/-- `z • 1 - D` is injective on `D.domain` when `Im z ≠ 0`. -/
theorem injective_subDirac (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Function.Injective (subDirac D z) := by
  simpa only [subDirac_apply] using hD.injective_resolvent_apply hz

/-- The range of `z • 1 - D` is closed when `Im z ≠ 0`.

Strategy: the bounded-below estimate `|Im z| · ‖x‖ ≤ ‖(z • 1 - D) x‖` makes any preimage
sequence Cauchy; its limit together with `D x = z • x - y` follows from closedness of the graph
of `D`, so the limit of `(z • 1 - D) xₙ` is again in the range. -/
theorem isClosed_range_subDirac (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    IsClosed (LinearMap.range (subDirac D z) : Set H) := by
  have hpos : (0 : ℝ) < |RCLike.im z| := abs_pos.mpr hz
  apply IsSeqClosed.isClosed
  intro Y y hY hYy
  simp only [SetLike.mem_coe, LinearMap.mem_range] at hY
  choose X hX using hY
  have hbound : ∀ n m, ‖(X n : H) - (X m : H)‖ ≤ ‖Y n - Y m‖ / |RCLike.im z| := by
    intro n m
    have hsub : subDirac D z (X n - X m) = Y n - Y m := by rw [_root_.map_sub, hX, hX]
    have hb := hD.norm_resolvent_apply_ge z (X n - X m)
    rw [← subDirac_apply, hsub, Submodule.coe_sub] at hb
    rw [le_div_iff₀ hpos, mul_comm]; exact hb
  have hCauchyX : CauchySeq (fun n => (X n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hYy.cauchySeq) (ε * |RCLike.im z|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hY' : ‖Y m - Y n‖ < ε * |RCLike.im z| := by
      have := hN m hm n hn; rwa [dist_eq_norm] at this
    rw [dist_eq_norm]
    calc ‖(X m : H) - (X n : H)‖ ≤ ‖Y m - Y n‖ / |RCLike.im z| := hbound m n
      _ < (ε * |RCLike.im z|) / |RCLike.im z| := by gcongr
      _ = ε := by rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchyX
  have heq : ∀ n, D (X n) = z • (X n : H) - Y n := by
    intro n; have h := hX n; rw [subDirac_apply] at h; rw [← h]; abel
  have hDX : Filter.Tendsto (fun n => D (X n)) Filter.atTop (nhds (z • x - y)) := by
    simp only [heq]; exact (hx.const_smul z).sub hYy
  have hmem : ((x, z • x - y) : H × H) ∈ D.graph :=
    hD.isClosed.mem_of_tendsto (hx.prodMk_nhds hDX)
      (Filter.Eventually.of_forall (fun n => D.mem_graph (X n)))
  rw [LinearPMap.mem_graph_iff] at hmem
  obtain ⟨x₀, hx1, hx2⟩ := hmem
  dsimp only at hx1 hx2
  rw [SetLike.mem_coe, LinearMap.mem_range]
  exact ⟨x₀, by rw [subDirac_apply, hx1, hx2]; abel⟩

/-- **Basic criterion of self-adjointness.** If `D` is self-adjoint and `Im z ≠ 0`, then
`z • 1 - D` is bijective on `D.domain`, i.e. `z` lies in the resolvent set of `D`. -/
theorem mem_resolventSet (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    z ∈ D.resolventSet := by
  have hrange : LinearMap.range (subDirac D z) = ⊤ := by
    have hdense : Dense (LinearMap.range (subDirac D z) : Set H) := by
      rw [LinearMap.coe_range]; exact hD.dense_range_resolvent_apply hz
    have hclosed := hD.isClosed_range_subDirac hz
    apply SetLike.coe_injective
    rw [Submodule.top_coe, ← hclosed.closure_eq]
    exact hdense.closure_eq
  have hsurj : Function.Surjective (subDirac D z) := LinearMap.range_eq_top.mp hrange
  have hbij : Function.Bijective (subDirac D z) := ⟨hD.injective_subDirac hz, hsurj⟩
  let op : H →ₗ.[𝕜] H := (z • LinearMap.id (R := 𝕜) (M := H)) +ᵥ (-D)
  change Function.Bijective ⇑op
  have hdom : op.domain = D.domain := rfl
  let e : op.domain ≃ₗ[𝕜] D.domain := LinearEquiv.ofEq op.domain D.domain hdom
  have hfun : ⇑op = ⇑(subDirac D z) ∘ ⇑e := by
    funext x
    simp only [op, e, Function.comp_apply, vadd_apply, LinearMap.smul_apply, LinearMap.id_apply,
      neg_apply, subDirac_apply, sub_eq_add_neg]
    congr 2
  rw [hfun]; exact hbij.comp e.bijective

end IsSelfAdjoint

/-! ### Corollary for odd spectral triples -/

namespace IsOddSpectralTriple

variable {A H 𝕜 : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)}

/-- For an odd spectral triple, every `z` off the real axis lies in the resolvent set of the
Dirac operator. In particular `RCLike.I ∈ ρ(D)`. -/
theorem mem_resolventSet (hT : IsOddSpectralTriple A D π) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    z ∈ D.resolventSet :=
  hT.self_adjoint.mem_resolventSet hz

end IsOddSpectralTriple

/-! ### Finitely summable spectral triples -/

/-- An odd spectral triple is finitely summable if `RCLike.I` lies in the resolvent set of the
Dirac operator and the resolvent `R(i, D)` is a compact operator on `H`.

The field `resolvent_mem` guards against the degenerate real case: when `𝕜 = ℝ`,
`RCLike.I = 0`, and `D.resolvent 0` falls back to the junk value `0` (which is trivially
compact) whenever `0 ∉ ρ(D)`. Requiring `resolvent_mem` as a field forces the caller to
verify that `i` is genuinely in the resolvent set. For `𝕜 = ℂ` this is supplied automatically
by `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` via `IsSelfAdjoint.mem_resolventSet`. -/
structure IsFinitelySummableSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H))
    extends IsOddSpectralTriple A D π where
  resolvent_mem : (RCLike.I : 𝕜) ∈ D.resolventSet
  compact_resolvent : IsCompactOperator (D.resolvent RCLike.I)

namespace IsOddSpectralTriple

variable {A H 𝕜 : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)}

/-- Build a finitely summable spectral triple from an odd one. The caller must supply
`hI : RCLike.im (RCLike.I : 𝕜) ≠ 0` (automatic for `𝕜 = ℂ`); `resolvent_mem` is then
derived from `IsSelfAdjoint.mem_resolventSet`. -/
def toIsFinitelySummableSpectralTriple (hT : IsOddSpectralTriple A D π)
    (hI : RCLike.im (RCLike.I : 𝕜) ≠ 0)
    (hc : IsCompactOperator (D.resolvent RCLike.I)) :
    IsFinitelySummableSpectralTriple A D π where
  toIsOddSpectralTriple := hT
  resolvent_mem := hT.mem_resolventSet hI
  compact_resolvent := hc

end IsOddSpectralTriple
