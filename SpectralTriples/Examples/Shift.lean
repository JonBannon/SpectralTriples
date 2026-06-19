/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import SpectralTriples.Fredholm

/-! # The unilateral shift on `ℓ²(ℕ)`

The forward unilateral shift on `ℓ²(ℕ)` is injective, and its range is the orthogonal complement
of the zeroth basis vector.  Its analytic Fredholm index is therefore `0 - 1 = -1`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace SpectralTriples.Shift

/-- The Hilbert space `ℓ²(ℕ)`, represented as `lp (fun _ : ℕ => ℂ) 2`. -/
abbrev H : Type := lp (fun _ : ℕ => ℂ) 2

noncomputable instance : NormedAddCommGroup H := inferInstance
noncomputable instance : InnerProductSpace ℂ H := inferInstance
instance : CompleteSpace H := inferInstance

/-- The coordinate function underlying the unilateral shift. -/
def shiftSeq (x : H) : ℕ → ℂ := fun n => if n = 0 then 0 else x (n - 1)

/-- At a successor coordinate, `shiftSeq` recovers the previous coordinate. -/
lemma shiftSeq_succ (x : H) (n : ℕ) : shiftSeq x (n + 1) = x n := by
  simp [shiftSeq]

/-- The shifted coordinate function is square-summable. -/
lemma shiftSeq_summable (x : H) :
    Summable fun n => ‖shiftSeq x n‖ ^ (2 : ℝ) := by
  have hx : Summable fun n => ‖x n‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  have htail : Summable fun n => ‖shiftSeq x (n + 1)‖ ^ (2 : ℝ) := by
    simpa [shiftSeq_succ] using hx
  exact (summable_nat_add_iff (f := fun n => ‖shiftSeq x n‖ ^ (2 : ℝ)) 1).1 htail

/-- The shifted coordinate function belongs to `ℓ²(ℕ)`. -/
lemma shiftSeq_memℓp (x : H) : Memℓp (shiftSeq x) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  simpa using shiftSeq_summable x

/-- The shifted coordinate function bundled as an element of `ℓ²(ℕ)`. -/
def shiftAux (x : H) : H := ⟨shiftSeq x, shiftSeq_memℓp x⟩

/-- The coordinate formula for the bundled shifted sequence. -/
@[simp] lemma shiftAux_apply (x : H) (n : ℕ) :
    shiftAux x n = if n = 0 then 0 else x (n - 1) := rfl

/-- The unilateral shift as a linear map before adding continuity. -/
noncomputable def shiftLinear : H →ₗ[ℂ] H where
  toFun := shiftAux
  map_add' := by
    intro x y
    refine lp.ext (funext fun n => ?_)
    change shiftAux (x + y) n = ((shiftAux x : ℕ → ℂ) + (shiftAux y : ℕ → ℂ)) n
    by_cases hn : n = 0
    · subst n
      simp [shiftAux_apply, Pi.add_apply]
    · simp only [shiftAux_apply, hn, ↓reduceIte, Pi.add_apply]
      change (((x + y : H) : ℕ → ℂ) (n - 1)) = x (n - 1) + y (n - 1)
      rw [lp.coeFn_add]
      rfl
  map_smul' := by
    intro c x
    refine lp.ext (funext fun n => ?_)
    change shiftAux (c • x) n = (c • (shiftAux x : ℕ → ℂ)) n
    by_cases hn : n = 0
    · subst n
      simp [shiftAux_apply, Pi.smul_apply]
    · simp only [shiftAux_apply, hn, ↓reduceIte, Pi.smul_apply]
      change (((c • x : H) : ℕ → ℂ) (n - 1)) = c • x (n - 1)
      rw [lp.coeFn_smul]
      rfl

/-- The square-sum of `shiftSeq x` equals the square-sum of `x`. -/
lemma shiftSeq_tsum (x : H) :
    (∑' n, ‖shiftSeq x n‖ ^ (2 : ℝ)) = ∑' n, ‖x n‖ ^ (2 : ℝ) := by
  calc
    (∑' n, ‖shiftSeq x n‖ ^ (2 : ℝ))
        = ‖shiftSeq x 0‖ ^ (2 : ℝ) +
            ∑' n, ‖shiftSeq x (n + 1)‖ ^ (2 : ℝ) := by
          exact (shiftSeq_summable x).tsum_eq_zero_add
    _ = 0 + ∑' n, ‖x n‖ ^ (2 : ℝ) := by simp [shiftSeq]
    _ = ∑' n, ‖x n‖ ^ (2 : ℝ) := by simp

/-- The bundled shifted sequence has the same `ℓ²` norm as the original sequence. -/
lemma shiftAux_norm (x : H) : ‖shiftAux x‖ = ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hpow : ‖shiftAux x‖ ^ (2 : ℝ≥0∞).toReal =
      ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
    simpa using shiftSeq_tsum x
  exact Real.rpow_left_injOn hp.ne' (norm_nonneg _) (norm_nonneg _) hpow

/-- The forward unilateral shift on `ℓ²(ℕ)`: it inserts `0` at coordinate `0` and moves each
coordinate one step forward. -/
noncomputable def shift : H →L[ℂ] H :=
  shiftLinear.mkContinuous 1 fun x => by
    simpa [one_mul] using le_of_eq (shiftAux_norm x)

/-- The coordinate formula for the forward unilateral shift. -/
@[simp] theorem shift_apply (x : H) (n : ℕ) :
    (shift x) n = if n = 0 then 0 else x (n - 1) := rfl

/-- The unilateral shift has trivial kernel. -/
theorem shift_ker_eq_bot : LinearMap.ker (shift : H →ₗ[ℂ] H) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  refine lp.ext (funext fun n => ?_)
  have hcoord : (shift x) (n + 1) = 0 := by
    simpa using congrArg (fun y : H => y (n + 1)) hx
  rw [shift_apply] at hcoord
  simp at hcoord
  simpa using hcoord

/-- The zeroth basis vector in `ℓ²(ℕ)`. -/
noncomputable def e0 : H := lp.single 2 0 (1 : ℂ)

/-- The unilateral shift sends the `n`-th basis vector to the `(n + 1)`-st basis vector. -/
theorem shift_single (n : ℕ) :
    shift (lp.single 2 n (1 : ℂ) : H) = lp.single 2 (n + 1) (1 : ℂ) := by
  refine lp.ext (funext fun k => ?_)
  rw [shift_apply]
  cases k with
  | zero => simp [lp.single_apply]
  | succ m =>
      by_cases hmn : m = n
      · subst m
        simp [lp.single_apply]
      · simp [lp.single_apply, hmn]

/-- The zeroth basis vector is nonzero. -/
theorem e0_ne_zero : e0 ≠ 0 := by
  intro h
  have hcoord := congrArg (fun x : H => x 0) h
  simp only [e0, lp.single_apply, Pi.single_eq_same, lp.coeFn_zero, Pi.zero_apply] at hcoord
  exact one_ne_zero hcoord

/-- The orthogonal complement of the shift range is the span of the zeroth basis vector. -/
theorem range_shift_orthogonal :
    (LinearMap.range (shift : H →ₗ[ℂ] H))ᗮ = ℂ ∙ e0 := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_span_singleton]
    refine ⟨y 0, ?_⟩
    refine lp.ext (funext fun n => ?_)
    cases n with
    | zero =>
        simp [e0, lp.single_apply]
    | succ m =>
        have hrange : (lp.single 2 (m + 1) (1 : ℂ) : H) ∈
            LinearMap.range (shift : H →ₗ[ℂ] H) := by
          rw [LinearMap.mem_range]
          exact ⟨lp.single 2 m (1 : ℂ), shift_single m⟩
        have hinner : inner ℂ y (lp.single 2 (m + 1) (1 : ℂ) : H) = 0 :=
          (Submodule.mem_orthogonal' (LinearMap.range (shift : H →ₗ[ℂ] H)) y).1 hy
            _ hrange
        rw [lp.inner_single_right] at hinner
        have hycoord : y (m + 1) = 0 := by
          have h' := congrArg (starRingEnd ℂ) hinner
          simpa [RCLike.inner_apply] using h'
        simp [e0, lp.single_apply, hycoord]
  · intro y hy
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨c, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [LinearMap.mem_range] at hu
    rcases hu with ⟨x, rfl⟩
    rw [inner_smul_left]
    change (starRingEnd ℂ) c * inner ℂ (lp.single 2 0 (1 : ℂ) : H) (shift x) = 0
    rw [lp.inner_single_left]
    rw [shift_apply]
    simp [RCLike.inner_apply]

/-- The orthogonal complement of the shift range is one-dimensional. -/
theorem range_shift_orthogonal_finrank :
    Module.finrank ℂ ↥((LinearMap.range (shift : H →ₗ[ℂ] H))ᗮ) = 1 := by
  rw [range_shift_orthogonal]
  exact finrank_span_singleton e0_ne_zero

/-- For a closed range in a Hilbert space, the quotient cokernel has the same dimension as the
orthogonal-complement cokernel. -/
theorem finrank_quotient_range_eq_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hclosed : IsClosed (LinearMap.range (T : H →ₗ[ℂ] H) : Set H)) :
    Module.finrank ℂ (H ⧸ LinearMap.range (T : H →ₗ[ℂ] H))
      = Module.finrank ℂ (LinearMap.range (T : H →ₗ[ℂ] H))ᗮ := by
  let K : Submodule ℂ H := LinearMap.range (T : H →ₗ[ℂ] H)
  change Module.finrank ℂ (H ⧸ K) = Module.finrank ℂ ↥Kᗮ
  haveI : CompleteSpace K := hclosed.completeSpace_coe
  exact (Submodule.quotientEquivOfIsCompl K Kᗮ
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection).finrank_eq

/-- The range of the unilateral shift is closed. -/
theorem isClosed_range_shift :
    IsClosed (LinearMap.range (shift : H →ₗ[ℂ] H) : Set H) := by
  change IsClosed (Set.range (shift : H → H))
  have hanti : AntilipschitzWith 1 (shift : H → H) := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    simp only [NNReal.coe_one, one_mul]
    have hsub : shift x - shift y = shift (x - y) := by
      exact (_root_.map_sub (shift : H →L[ℂ] H) x y).symm
    rw [hsub]
    change ‖x - y‖ ≤ ‖shiftAux (x - y)‖
    exact le_of_eq (shiftAux_norm (x - y)).symm
  exact hanti.isClosed_range shift.uniformContinuous

/-- The forward unilateral shift on `ℓ²(ℕ)` is Fredholm of index `-1`. -/
theorem fredholmIndex_shift :
    SpectralTriples.Fredholm.index (shift : H →ₗ[ℂ] H) = -1 := by
  unfold SpectralTriples.Fredholm.index
  rw [shift_ker_eq_bot, finrank_bot,
    finrank_quotient_range_eq_orthogonal shift isClosed_range_shift,
    range_shift_orthogonal_finrank]
  norm_num

end SpectralTriples.Shift
