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
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Compact operators on Hilbert space are Fredholm perturbations of the identity

This file proves, for an inner product space `H`, that `1 - K` is a Fredholm linear map
(`SpectralTriples.Fredholm.IsFredholm`) whenever `K` is a compact operator on `H`. This is the
structural part of the Hilbert-space case of the classical Riesz–Schauder theorem (finite
kernel, closed range, finite-dimensional cokernel); the further classical fact that the index
is `0` is not proved here. None of this is yet in Mathlib (only the weaker spectral dichotomy
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` is), so we prove it here from scratch.

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

namespace Submodule

/-- For a submodule of a Hilbert space with an orthogonal projection (e.g. one with closed
range), the quotient by it is linearly equivalent to its orthogonal complement. -/
noncomputable def quotientEquivOrthogonal (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    (H ⧸ K) ≃ₗ[𝕜] Kᗮ :=
  Submodule.quotientEquivOfIsCompl K Kᗮ Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

omit [CompleteSpace H] in
/-- The quotient by a submodule with an orthogonal projection has the same finite dimension as
its orthogonal complement. -/
theorem finrank_quotient_eq_finrank_orthogonal (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    Module.finrank 𝕜 (H ⧸ K) = Module.finrank 𝕜 Kᗮ :=
  (K.quotientEquivOrthogonal).finrank_eq

omit [CompleteSpace H] in
/-- The quotient by a submodule with an orthogonal projection is finite-dimensional whenever
its orthogonal complement is. -/
theorem finiteDimensional_quotient_of_finiteDimensional_orthogonal (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] [FiniteDimensional 𝕜 Kᗮ] :
    FiniteDimensional 𝕜 (H ⧸ K) :=
  FiniteDimensional.of_injective (K.quotientEquivOrthogonal).toLinearMap
    (K.quotientEquivOrthogonal).injective

end Submodule

namespace SpectralTriples.Fredholm

/-- **Fredholm-ness of compact perturbations of the identity** (the structural part of the
classical Riesz–Schauder theorem for compact operators on Hilbert space): if `K` is compact,
then `1 - K` is a Fredholm linear map — its kernel is finite-dimensional, its range is closed,
and its range has finite codimension. (The further classical fact that the index is `0`,
i.e. `dim (ker (1 - K)) = dim (coker (1 - K))`, is not proved here.) -/
theorem isFredholm_one_sub {K : H →L[𝕜] H} (hK : IsCompactOperator K) :
    IsFredholm ((1 - K : H →L[𝕜] H).toLinearMap) := by
  set T : H →L[𝕜] H := 1 - K with hTdef
  set N : Submodule 𝕜 H := LinearMap.ker T.toLinearMap with hNdef
  -- `N = ker T` is the eigenspace of `K` at the eigenvalue `1`, hence finite-dimensional.
  have hNeig : N = Module.End.eigenspace K.toLinearMap 1 := by
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff, one_smul]
      have hTx : T x = 0 := hx
      rw [hTdef] at hTx
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        sub_eq_zero] at hTx
      exact hTx.symm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have hx' : K x = x := by simpa using hx
      change T x = 0
      rw [hTdef]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      rw [hx', sub_self]
  haveI hNfd : FiniteDimensional 𝕜 N := by
    rw [hNeig]; exact K.finite_dimensional_eigenspace hK 1 one_ne_zero
  -- Step 1: `T` is bounded below on `Nᗮ`.
  have hbelow : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Nᗮ, c * ‖x‖ ≤ ‖T x‖ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ n : ℕ, ∃ x ∈ Nᗮ, ‖T x‖ < (1 / (n + 1 : ℝ)) * ‖x‖ := fun n =>
      hcon (1 / (n + 1)) (by positivity)
    choose x hxN hxlt using hseq
    have hxne : ∀ n, x n ≠ 0 := by
      intro n hx0
      have h := hxlt n
      rw [hx0] at h
      simp at h
    set y : ℕ → H := fun n => ((‖x n‖⁻¹ : ℝ) : 𝕜) • x n with hydef
    have hyN : ∀ n, y n ∈ Nᗮ := fun n => Nᗮ.smul_mem _ (hxN n)
    have hynorm : ∀ n, ‖y n‖ = 1 := by
      intro n
      rw [hydef, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hxne n))]
    have hTy_lt : ∀ n, ‖T (y n)‖ < 1 / (n + 1 : ℝ) := by
      intro n
      have h1 : T (y n) = ((‖x n‖⁻¹ : ℝ) : 𝕜) • T (x n) := by rw [hydef, _root_.map_smul]
      rw [h1, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x n‖⁻¹)]
      have hb := hxlt n
      have hxnpos : (0 : ℝ) < ‖x n‖ := norm_pos_iff.mpr (hxne n)
      calc ‖x n‖⁻¹ * ‖T (x n)‖ < ‖x n‖⁻¹ * ((1 / (↑n + 1)) * ‖x n‖) :=
            mul_lt_mul_of_pos_left hb (inv_pos.mpr hxnpos)
        _ = 1 / (↑n + 1) := by
              rw [show ‖x n‖⁻¹ * ((1 / (↑n + 1)) * ‖x n‖)
                  = (1 / (↑n + 1)) * (‖x n‖⁻¹ * ‖x n‖) by ring,
                inv_mul_cancel₀ (ne_of_gt hxnpos), mul_one]
    have hTy_tendsto : Filter.Tendsto (fun n => T (y n)) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hTy_lt n).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨C, hC, hCsub⟩ := hK.image_closedBall_subset_compact 1
    obtain ⟨z, _hzC, φ, hφ, hφy⟩ := hC.tendsto_subseq
      (x := fun n => K (y n)) (fun n => hCsub ⟨y n, by simp [hynorm n], rfl⟩)
    have hy_tendsto : Filter.Tendsto (fun n => y (φ n)) Filter.atTop (nhds z) := by
      have heq : ∀ n, T (y (φ n)) + K (y (φ n)) = y (φ n) := by
        intro n
        simp only [hTdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
        abel
      have htarget : Filter.Tendsto (fun n => T (y (φ n)) + K (y (φ n))) Filter.atTop (nhds z) := by
        simpa using (hTy_tendsto.comp hφ.tendsto_atTop).add hφy
      exact htarget.congr heq
    have hzN : z ∈ Nᗮ :=
      N.isClosed_orthogonal.mem_of_tendsto hy_tendsto
        (Filter.Eventually.of_forall fun n => hyN (φ n))
    have hzT0 : T z = 0 := by
      have h1 : Filter.Tendsto (fun n => T (y (φ n))) Filter.atTop (nhds (T z)) :=
        (T.continuous.tendsto z).comp hy_tendsto
      have h2 : Filter.Tendsto (fun n => T (y (φ n))) Filter.atTop (nhds 0) :=
        hTy_tendsto.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hz0 : z = 0 := by
      have hzNN : z ∈ N := hzT0
      have hmem : z ∈ N ⊓ Nᗮ := ⟨hzNN, hzN⟩
      rwa [(Submodule.orthogonal_disjoint N).eq_bot, Submodule.mem_bot] at hmem
    have hnorm_tendsto : Filter.Tendsto (fun n => ‖y (φ n)‖) Filter.atTop (nhds ‖z‖) :=
      (continuous_norm.tendsto z).comp hy_tendsto
    simp only [hynorm] at hnorm_tendsto
    have h1 : ‖z‖ = 1 := tendsto_nhds_unique hnorm_tendsto tendsto_const_nhds
    rw [hz0, norm_zero] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨c, hc0, hTbelow⟩ := hbelow
  haveI : CompleteSpace Nᗮ := N.isClosed_orthogonal.completeSpace_coe
  set T' : Nᗮ →L[𝕜] H := T.comp (Nᗮ.subtypeL) with hT'def
  have hT'bound : ∀ x : Nᗮ, ‖x‖ ≤ c⁻¹ * ‖T' x‖ := by
    intro x
    have hb := hTbelow x x.2
    have hT'x : T' x = T x := rfl
    rw [hT'x]
    have hmul := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc0.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc0), one_mul] at hmul
  have hanti : AntilipschitzWith (⟨c⁻¹, inv_nonneg.mpr hc0.le⟩ : NNReal) T' :=
    ContinuousLinearMap.antilipschitz_of_bound T' hT'bound
  have hclosed_range' : IsClosed (Set.range (T' : Nᗮ → H)) :=
    hanti.isClosed_range T'.uniformContinuous
  -- Step 2: the range of `T` coincides with the range of `T'`, hence is closed.
  have hrange_eq : LinearMap.range T.toLinearMap = LinearMap.range T'.toLinearMap := by
    apply le_antisymm
    · rintro - ⟨v, rfl⟩
      have hsub : v - Nᗮ.starProjection v ∈ N := by
        have h := Nᗮ.sub_starProjection_mem_orthogonal v
        rwa [Submodule.orthogonal_orthogonal N] at h
      have hTsub : T (v - Nᗮ.starProjection v) = 0 := LinearMap.mem_ker.mp hsub
      have hTv : T v = T' ⟨Nᗮ.starProjection v, Nᗮ.starProjection_apply_mem v⟩ := by
        have hsplit : T v = T (Nᗮ.starProjection v) + T (v - Nᗮ.starProjection v) := by
          rw [← _root_.map_add]; congr 1; abel
        rw [hsplit, hTsub, add_zero]; rfl
      exact ⟨⟨Nᗮ.starProjection v, Nᗮ.starProjection_apply_mem v⟩, hTv.symm⟩
    · rintro - ⟨u, rfl⟩
      exact ⟨(u : H), rfl⟩
  have hcoe_eq : (LinearMap.range T'.toLinearMap : Set H) = Set.range (T' : Nᗮ → H) := by
    ext y; simp [LinearMap.mem_range]
  have hclosed_T : IsClosed (LinearMap.range T.toLinearMap : Set H) := by
    rw [hrange_eq, hcoe_eq]; exact hclosed_range'
  haveI : CompleteSpace (LinearMap.range T.toLinearMap) := hclosed_T.completeSpace_coe
  -- Step 3: the cokernel is finite-dimensional, via the adjoint `T† = 1 - K†` (also a compact
  -- perturbation of the identity, since `K†` is compact) and `(range T)ᗮ = ker T†`.
  have hTadj : ContinuousLinearMap.adjoint T = 1 - ContinuousLinearMap.adjoint K := by
    rw [hTdef, map_sub]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  have hKadj : IsCompactOperator (ContinuousLinearMap.adjoint K) := hK.adjoint
  have hNadj : LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap =
      Module.End.eigenspace (ContinuousLinearMap.adjoint K).toLinearMap 1 := by
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff, one_smul]
      have hTx : (ContinuousLinearMap.adjoint T) x = 0 := hx
      rw [hTadj] at hTx
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        sub_eq_zero] at hTx
      exact hTx.symm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have hx' : (ContinuousLinearMap.adjoint K) x = x := by simpa using hx
      change (ContinuousLinearMap.adjoint T) x = 0
      rw [hTadj]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      rw [hx', sub_self]
  haveI hNadjfd : FiniteDimensional 𝕜
      (LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap) := by
    rw [hNadj]
    exact (ContinuousLinearMap.adjoint K).finite_dimensional_eigenspace hKadj 1 one_ne_zero
  haveI hcokerfd : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)ᗮ := by
    rw [T.orthogonal_range]; exact hNadjfd
  haveI : FiniteDimensional 𝕜 (H ⧸ LinearMap.range T.toLinearMap) :=
    (LinearMap.range T.toLinearMap).finiteDimensional_quotient_of_finiteDimensional_orthogonal
  exact ⟨hNfd, hclosed_T, ‹FiniteDimensional 𝕜 (H ⧸ LinearMap.range T.toLinearMap)›⟩

end SpectralTriples.Fredholm
