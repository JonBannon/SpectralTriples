/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Compact operators on Hilbert space are Fredholm perturbations of the identity

This file proves, for an inner product space `H`, that `1 - K` is a Fredholm linear map
(`SpectralTriples.Fredholm.IsFredholm`) whenever `K` is a compact operator on `H`. This is the
Hilbert-space case of the classical Riesz–Schauder theorem; it is not yet in Mathlib (only the
weaker spectral dichotomy `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` is), so we prove
it here from scratch.

## Main results

* `IsCompactOperator.exists_finiteRank_norm_sub_lt`: compact operators on a Hilbert space are
  norm-approximable by finite-rank operators.
* `IsCompactOperator.adjoint`: the adjoint of a compact operator on a Hilbert space is compact.
* `SpectralTriples.Fredholm.isFredholm_one_sub`: `1 - K` is Fredholm for `K` compact.
-/

@[expose] public section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

namespace IsCompactOperator

omit [CompleteSpace H] in
/-- A compact operator on a Hilbert space is approximable, in operator norm, by finite-rank
operators: for every `ε > 0` there is a finite-rank `F` with `‖K - F‖ ≤ ε`. The approximant is
built by composing `K` with the orthogonal projection onto the span of a finite `ε`-net of the
(relatively compact) image of the closed unit ball. -/
theorem exists_finiteRank_norm_sub_lt {K : H →L[𝕜] H} (hK : IsCompactOperator K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : H →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧ ‖K - F‖ ≤ ε := by
  obtain ⟨C, hC, hCsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded ε hε
  classical
  set V : Submodule 𝕜 H := Submodule.span 𝕜 t with hV
  haveI hVfd : FiniteDimensional 𝕜 V := Module.Finite.span_of_finite 𝕜 ht_fin
  set F : H →L[𝕜] H := V.starProjection ∘L K with hF
  have hrange : LinearMap.range F.toLinearMap ≤ V := by
    rintro - ⟨x, rfl⟩
    exact V.starProjection_apply_mem (K x)
  refine ⟨F, Submodule.finiteDimensional_of_le hrange, ?_⟩
  have hball : ∀ x : H, ‖x‖ ≤ 1 → ‖(K - F) x‖ ≤ ε := by
    intro x hx
    have hKx : K x ∈ C := hCsub ⟨x, by simpa using hx, rfl⟩
    obtain ⟨z, hz, hzball⟩ := Set.mem_iUnion₂.mp (ht_cov hKx)
    have hzV : z ∈ V := Submodule.subset_span hz
    have hbdd : BddBelow (Set.range fun v : V => ‖K x - (v : H)‖) :=
      ⟨0, fun _ ⟨_, hy⟩ => hy ▸ norm_nonneg _⟩
    have hmin : ‖K x - V.starProjection (K x)‖ ≤ ‖K x - z‖ := by
      rw [V.starProjection_minimal]
      exact ciInf_le hbdd ⟨z, hzV⟩
    have hzlt : ‖K x - z‖ < ε := by simpa [dist_eq_norm] using hzball
    have heq : (K - F) x = K x - V.starProjection (K x) := by
      rw [hF]; simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [heq]
    exact le_trans hmin hzlt.le
  have hgen : ∀ x : H, ‖(K - F) x‖ ≤ ε * ‖x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    set c : 𝕜 := ((‖x‖⁻¹ : ℝ) : 𝕜) with hc
    have hcnorm : ‖c‖ = ‖x‖⁻¹ := by
      rw [hc, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    have hcx : ‖c • x‖ = 1 := by
      rw [norm_smul, hcnorm, inv_mul_cancel₀ (ne_of_gt hnx)]
    have hball' := hball (c • x) hcx.le
    rw [_root_.map_smul, norm_smul, hcnorm] at hball'
    have := mul_le_mul_of_nonneg_left hball' hnx.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hnx), mul_comm ‖x‖ ε] at this
  exact ContinuousLinearMap.opNorm_le_bound _ hε.le hgen

end IsCompactOperator

/-- If a continuous linear map on an inner product space has finite-dimensional range, so does
its adjoint: `T†` vanishes on `(range T)ᗮ` (since `ker T† = (range T)ᗮ`), so `T† = T† ∘
starProjection (range T)`, and the image of a finite-dimensional space under any linear map is
finite-dimensional. -/
theorem ContinuousLinearMap.finiteDimensional_range_adjoint {T : H →L[𝕜] H}
    (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    FiniteDimensional 𝕜 (LinearMap.range (ContinuousLinearMap.adjoint T).toLinearMap) := by
  set W : Submodule 𝕜 H := LinearMap.range T.toLinearMap with hW
  have hker : ∀ x ∈ Wᗮ, ContinuousLinearMap.adjoint T x = 0 := by
    intro x hx
    have hx' : x ∈ LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap := by
      rw [← T.orthogonal_range]; exact hx
    simpa using hx'
  have hrange : LinearMap.range (ContinuousLinearMap.adjoint T).toLinearMap ≤
      Submodule.map (ContinuousLinearMap.adjoint T).toLinearMap W := by
    rintro - ⟨x, rfl⟩
    refine ⟨W.starProjection x, W.starProjection_apply_mem x, ?_⟩
    have hx : x - W.starProjection x ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
    have h0 : ContinuousLinearMap.adjoint T (x - W.starProjection x) = 0 := hker _ hx
    have heq : ContinuousLinearMap.adjoint T x - ContinuousLinearMap.adjoint T
        (W.starProjection x) = 0 := by
      rw [← _root_.map_sub]; exact h0
    exact (sub_eq_zero.mp heq).symm
  exact Submodule.finiteDimensional_of_le hrange

namespace IsCompactOperator

/-- The adjoint of a compact operator on a Hilbert space is compact. The adjoint is the
norm-limit of the adjoints of finite-rank approximants of `K` (finite-rank operators have
finite-rank adjoints, by `ContinuousLinearMap.finiteDimensional_range_adjoint`), and the
adjoint operation is norm-preserving. -/
theorem adjoint {K : H →L[𝕜] H} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) := by
  have happrox : ∀ n : ℕ, ∃ F : H →L[𝕜] H,
      FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧ ‖K - F‖ ≤ (1 : ℝ) / (n + 1) := by
    intro n
    exact hK.exists_finiteRank_norm_sub_lt (by positivity)
  choose F hFfd hFnorm using happrox
  -- Each finite-rank `F n` is compact: its image lies in the (finite-dimensional, hence
  -- proper) submodule `range (F n)`, so the image of the closed unit ball is contained in the
  -- compact image, under the inclusion, of a closed ball in that submodule.
  have hFcompact : ∀ n, IsCompactOperator (F n) := by
    intro n
    haveI := hFfd n
    set W : Submodule 𝕜 H := LinearMap.range (F n).toLinearMap with hW
    haveI : ProperSpace W := FiniteDimensional.proper 𝕜 W
    rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact (⇑(F n))]
    refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos,
      (Subtype.val : W → H) '' Metric.closedBall (0 : W) ‖F n‖,
      (isCompact_closedBall (0 : W) _).image continuous_subtype_val, ?_⟩
    rintro - ⟨x, hx, rfl⟩
    have hmem : (F n) x ∈ W := LinearMap.mem_range_self _ x
    refine ⟨⟨(F n) x, hmem⟩, ?_, rfl⟩
    have hx1 : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(⟨(F n) x, hmem⟩ : W)‖ = ‖(F n) x‖ := rfl
      _ ≤ ‖F n‖ * ‖x‖ := (F n).le_opNorm x
      _ ≤ ‖F n‖ := by nlinarith [norm_nonneg (F n)]
  -- The adjoints of the approximants are still finite-rank (hence compact), and converge to
  -- `K†` in norm since the adjoint operation is norm-preserving.
  have hFadjCompact : ∀ n, IsCompactOperator (ContinuousLinearMap.adjoint (F n)) := by
    intro n
    haveI := hFfd n
    have hC := (F n).finiteDimensional_range_adjoint this
    haveI := hC
    set W : Submodule 𝕜 H :=
      LinearMap.range (ContinuousLinearMap.adjoint (F n)).toLinearMap with hW
    haveI : ProperSpace W := FiniteDimensional.proper 𝕜 W
    rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact
      (⇑(ContinuousLinearMap.adjoint (F n)))]
    refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos,
      (Subtype.val : W → H) '' Metric.closedBall (0 : W) ‖ContinuousLinearMap.adjoint (F n)‖,
      (isCompact_closedBall (0 : W) _).image continuous_subtype_val, ?_⟩
    rintro - ⟨x, hx, rfl⟩
    have hmem : (ContinuousLinearMap.adjoint (F n)) x ∈ W := LinearMap.mem_range_self _ x
    refine ⟨⟨(ContinuousLinearMap.adjoint (F n)) x, hmem⟩, ?_, rfl⟩
    have hx1 : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(⟨(ContinuousLinearMap.adjoint (F n)) x, hmem⟩ : W)‖
        = ‖(ContinuousLinearMap.adjoint (F n)) x‖ := rfl
      _ ≤ ‖ContinuousLinearMap.adjoint (F n)‖ * ‖x‖ :=
          (ContinuousLinearMap.adjoint (F n)).le_opNorm x
      _ ≤ ‖ContinuousLinearMap.adjoint (F n)‖ := by
          nlinarith [norm_nonneg (ContinuousLinearMap.adjoint (F n))]
  have htendsto : Filter.Tendsto (fun n => ContinuousLinearMap.adjoint (F n)) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint K)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm_eq : ∀ n, ‖ContinuousLinearMap.adjoint (F n) - ContinuousLinearMap.adjoint K‖
        = ‖F n - K‖ := by
      intro n
      rw [← map_sub]
      exact (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := H) (F := H)).norm_map (F n - K)
    simp_rw [hnorm_eq, ← norm_sub_rev (K) (F _)]
    refine squeeze_zero (fun n => norm_nonneg _) hFnorm ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact isCompactOperator_of_tendsto htendsto (Filter.Eventually.of_forall hFadjCompact)

end IsCompactOperator
