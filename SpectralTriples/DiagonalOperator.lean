/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Block-diagonal operators on `ℓ²`

Given a family of fibres `G : α → Type` (each a Hilbert space) and a uniformly bounded family
of block operators `T i : G i →L[𝕜] G i`, the **block-diagonal operator**
`(diagL T) a = (i ↦ T i (aᵢ))` is a bounded operator on `H = ℓ²(α; G)` with `‖diagL T‖ ≤ C`
where `C` bounds the blocks.

The headline result is that `diagL T` is a **compact operator** as soon as the block norms
vanish at infinity (`‖T i‖ → 0` along the cofinite filter) and each fibre is
finite-dimensional: the finitely-supported truncations are finite-rank, hence compact, and
they converge to `diagL T` in operator norm.

This is the analytic core shared by the `S¹` and `T²` Dirac examples, whose resolvents are
exactly such block-diagonal operators with block norms `→ 0`.

## Main definitions

* `lpDiag.diagL`: the block-diagonal operator `lp G 2 →L[𝕜] lp G 2`.

## Main results

* `lpDiag.norm_diagL_le`: `‖diagL T‖ ≤ C` when `‖T i‖ ≤ C`.
* `lpDiag.isCompactOperator_diagL`: `diagL T` is compact when the block norms vanish at
  infinity and the fibres are finite-dimensional.
-/

@[expose] public section

namespace lpDiag

open scoped Topology
open Filter

variable {α 𝕜 : Type*} [RCLike 𝕜] {G : α → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

/-- The coordinatewise image `i ↦ T i (aᵢ)` of a square-summable family under a uniformly
bounded block family is again square-summable. -/
theorem memℓp_diag (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C) (a : lp G 2) :
    Memℓp (fun i => T i (a i)) 2 := by
  refine (lp.memℓp ((C : 𝕜) • a)).mono' fun i => ?_
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC i)
  calc ‖T i (a i)‖ ≤ ‖T i‖ * ‖a i‖ := (T i).le_opNorm _
    _ ≤ C * ‖a i‖ := by gcongr; exact hC i
    _ = ‖(C : 𝕜)‖ * ‖a i‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg hC0]
    _ = ‖((C : 𝕜) • a) i‖ := by rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]

/-- The coordinatewise application `a ↦ (i ↦ T i (aᵢ))` as an element of `ℓ²(α; G)`. -/
noncomputable def diagApply (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (a : lp G 2) : lp G 2 :=
  ⟨fun i => T i (a i), memℓp_diag T hC a⟩

@[simp] theorem coe_diagApply (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (a : lp G 2) (i : α) : (diagApply T hC a) i = T i (a i) := rfl

/-- The block-diagonal operator `lp G 2 →L[𝕜] lp G 2`, `(diagL T) a = (i ↦ T i (aᵢ))`, of a
uniformly bounded block family. -/
noncomputable def diagL (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖T i‖ ≤ C) :
    lp G 2 →L[𝕜] lp G 2 :=
  LinearMap.mkContinuous
    { toFun := diagApply T hC
      map_add' := fun a b => by
        refine lp.ext (funext fun i => ?_)
        simp only [coe_diagApply, lp.coeFn_add, Pi.add_apply, _root_.map_add]
      map_smul' := fun c a => by
        refine lp.ext (funext fun i => ?_)
        simp only [coe_diagApply, lp.coeFn_smul, Pi.smul_apply, _root_.map_smul,
          RingHom.id_apply] }
    C fun a => by
      have hmono : ‖diagApply T hC a‖ ≤ ‖(C : 𝕜) • a‖ := by
        refine lp.norm_mono two_ne_zero fun i => ?_
        calc ‖(diagApply T hC a) i‖ = ‖T i (a i)‖ := by rw [coe_diagApply]
          _ ≤ ‖T i‖ * ‖a i‖ := (T i).le_opNorm _
          _ ≤ C * ‖a i‖ := by gcongr; exact hC i
          _ = ‖(C : 𝕜)‖ * ‖a i‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg hC0]
          _ = ‖((C : 𝕜) • a) i‖ := by rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]
      calc ‖diagApply T hC a‖ ≤ ‖(C : 𝕜) • a‖ := hmono
        _ = ‖(C : 𝕜)‖ * ‖a‖ := by rw [norm_smul]
        _ = C * ‖a‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg hC0]

@[simp] theorem diagL_apply (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖T i‖ ≤ C)
    (a : lp G 2) (i : α) : (diagL T hC0 hC a) i = T i (a i) := rfl

/-- The operator norm of a block-diagonal operator is bounded by any uniform bound on the
block norms. -/
theorem norm_diagL_le (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖T i‖ ≤ C) :
    ‖diagL T hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-! ### Compactness via finite-rank truncation -/

/-- The single-fibre block operator `a ↦ single i (T i aᵢ)`. It factors as
`single ∘ T i ∘ evalᵢ` through the fibre `G i`, hence is compact when `G i` is
finite-dimensional. -/
noncomputable def singleBlock [DecidableEq α] (T : ∀ i, G i →L[𝕜] G i) (i : α) :
    lp G 2 →L[𝕜] lp G 2 :=
  (lp.singleContinuousLinearMap 𝕜 G 2 i).comp ((T i).comp (lp.evalCLM 𝕜 G 2 i))

@[simp] theorem singleBlock_apply [DecidableEq α] (T : ∀ i, G i →L[𝕜] G i) (i : α) (a : lp G 2) :
    singleBlock T i a = lp.single 2 i (T i (a i)) := rfl

/-- A single-fibre block operator is compact when its fibre is finite-dimensional: it factors
through the locally compact space `G i`. -/
theorem isCompactOperator_singleBlock [DecidableEq α] (T : ∀ i, G i →L[𝕜] G i) (i : α)
    [FiniteDimensional 𝕜 (G i)] : IsCompactOperator (singleBlock T i) := by
  haveI : ProperSpace (G i) := FiniteDimensional.proper 𝕜 (G i)
  have hmid : IsCompactOperator (((T i).comp (lp.evalCLM 𝕜 G 2 i)) : lp G 2 →L[𝕜] G i) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  simpa only [singleBlock, ContinuousLinearMap.coe_comp] using
    hmid.clm_comp (lp.singleContinuousLinearMap 𝕜 G 2 i)

/-- A block-diagonal operator with finitely many nonzero blocks and finite-dimensional fibres is
a finite-rank operator, hence compact. -/
theorem isCompactOperator_diagL_of_support_finite (T : ∀ i, G i →L[𝕜] G i)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖T i‖ ≤ C) [∀ i, FiniteDimensional 𝕜 (G i)]
    (hfin : {i | T i ≠ 0}.Finite) :
    IsCompactOperator (diagL T hC0 hC) := by
  classical
  have hsum : diagL T hC0 hC = ∑ i ∈ hfin.toFinset, singleBlock T i := by
    refine ContinuousLinearMap.ext fun a => lp.ext (funext fun j => ?_)
    rw [ContinuousLinearMap.sum_apply]
    simp only [diagL_apply, singleBlock_apply, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_single, Finset.sum_pi_single]
    by_cases hj : j ∈ hfin.toFinset
    · rw [if_pos hj]
    · rw [if_neg hj]
      have : T j = 0 := by
        by_contra h; exact hj (hfin.mem_toFinset.mpr h)
      rw [this, ContinuousLinearMap.zero_apply]
  rw [hsum]
  refine Submodule.sum_mem (compactOperator (RingHom.id 𝕜) (lp G 2) (lp G 2)) fun i _ => ?_
  exact isCompactOperator_singleBlock T i

/-- Two block-diagonal operators differ pointwise by at most `D * ‖a‖` when their blocks differ
in norm by at most `D`. -/
private theorem norm_diagL_sub_apply_le (T T' : ∀ i, G i →L[𝕜] G i) {C C' : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (hC0' : 0 ≤ C') (hC' : ∀ i, ‖T' i‖ ≤ C') {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i, ‖T i - T' i‖ ≤ D) (a : lp G 2) :
    ‖diagL T hC0 hC a - diagL T' hC0' hC' a‖ ≤ D * ‖a‖ := by
  have key : ‖diagL T hC0 hC a - diagL T' hC0' hC' a‖ ≤ ‖(D : 𝕜) • a‖ :=
    lp.norm_mono two_ne_zero fun i => by
      rw [lp.coeFn_sub, Pi.sub_apply, diagL_apply, diagL_apply, ← ContinuousLinearMap.sub_apply]
      calc ‖(T i - T' i) (a i)‖ ≤ ‖T i - T' i‖ * ‖a i‖ := (T i - T' i).le_opNorm _
        _ ≤ D * ‖a i‖ := by gcongr; exact hD i
        _ = ‖((D : 𝕜) • a) i‖ := by
            rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hD0]
  calc ‖diagL T hC0 hC a - diagL T' hC0' hC' a‖ ≤ ‖(D : 𝕜) • a‖ := key
    _ = D * ‖a‖ := by rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hD0]

open Classical in
/-- The block family `T` truncated to the blocks of norm `≥ 1/(n+1)`. -/
private noncomputable def truncate (T : ∀ i, G i →L[𝕜] G i) (n : ℕ) (i : α) : G i →L[𝕜] G i :=
  if (1 : ℝ) / (n + 1) ≤ ‖T i‖ then T i else 0

private theorem norm_truncate_le (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (n : ℕ) (i : α) : ‖truncate T n i‖ ≤ C := by
  unfold truncate
  split
  · exact hC i
  · rw [norm_zero]; exact hC0

private theorem norm_sub_truncate_le (T : ∀ i, G i →L[𝕜] G i) (n : ℕ) (i : α) :
    ‖truncate T n i - T i‖ ≤ 1 / (n + 1) := by
  unfold truncate
  split
  · rw [sub_self, norm_zero]; positivity
  · rename_i h
    rw [zero_sub, norm_neg]
    exact le_of_lt (lt_of_not_ge h)

/-- **The block-diagonal operator is compact when its block norms vanish at infinity** (and each
fibre is finite-dimensional). The finitely-supported truncations are finite-rank, hence compact,
and converge to `diagL T` in operator norm. -/
theorem isCompactOperator_diagL (T : ∀ i, G i →L[𝕜] G i) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) [∀ i, FiniteDimensional 𝕜 (G i)]
    (hvanish : Tendsto (fun i => ‖T i‖) cofinite (𝓝 0)) :
    IsCompactOperator (diagL T hC0 hC) := by
  classical
  haveI : ∀ i, CompleteSpace (G i) := fun i => FiniteDimensional.complete 𝕜 (G i)
  -- The truncations, their bounds and finite supports.
  have hCn : ∀ n, ∀ i, ‖truncate T n i‖ ≤ C := fun n => norm_truncate_le T hC0 hC n
  have hsupp : ∀ n, {i | truncate T n i ≠ 0}.Finite := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hev := hvanish.eventually (Iio_mem_nhds hpos)
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i hi => ?_
    rw [Set.mem_setOf_eq] at hi
    rw [Set.mem_setOf_eq]
    intro hlt
    exact hi (by unfold truncate; rw [if_neg (not_le.mpr hlt)])
  -- Each truncation is finite-rank, hence compact.
  have hcompact : ∀ n, IsCompactOperator (diagL (truncate T n) hC0 (hCn n)) := fun n =>
    isCompactOperator_diagL_of_support_finite (truncate T n) hC0 (hCn n) (hsupp n)
  -- The truncations converge to `diagL T` in operator norm.
  have hop : ∀ n, ‖diagL (truncate T n) hC0 (hCn n) - diagL T hC0 hC‖ ≤ 1 / (n + 1) := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [ContinuousLinearMap.sub_apply]
    exact norm_diagL_sub_apply_le (truncate T n) T hC0 (hCn n) hC0 hC (by positivity)
      (norm_sub_truncate_le T n) a
  have htends : Tendsto (fun n => diagL (truncate T n) hC0 (hCn n)) atTop
      (𝓝 (diagL T hC0 hC)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hop ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact isCompactOperator_of_tendsto htends (Filter.Eventually.of_forall hcompact)

end lpDiag
