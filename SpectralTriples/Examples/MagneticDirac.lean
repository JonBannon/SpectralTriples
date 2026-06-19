/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.Examples.Shift
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # A magnetic Dirac model with flux `k`

This file formalizes the Landau-level / magnetic-translation model of the flux-`k` Dirac
operator on the two-torus after reduction to `ℓ²(ℕ) ⊗ ℂᵏ`.  The unitary equivalence between
this lowest-Landau-level-adapted model and the geometric PDE on the torus is not formalized here;
that analytic comparison is deferred.

In this model the chiral magnetic Dirac operator is the backward shift on the Landau-level index,
tensored with the `k`-dimensional guiding-center degeneracy.  Its kernel is the lowest Landau
level, identified with `Fin k → ℂ`, and its cokernel is trivial, so the Fredholm index is `k`.
The magnetic translations act on the `Fin k` factor by clock and cyclic shift operators satisfying
the finite Weyl relation `Ĉ Ŝ = omega Ŝ Ĉ`, certifying that the `ℂᵏ` factor is the flux-`k`
degeneracy.
-/

@[expose] public section

open scoped ENNReal NNReal

open SpectralTriples.Shift

namespace SpectralTriples.MagneticDirac

/-- The product index set for `ℓ²(ℕ) ⊗ ℂᵏ`. -/
abbrev Idx (k : ℕ) : Type := ℕ × Fin k

/-- The Hilbert space `ℓ²(ℕ) ⊗ ℂᵏ`, represented as `lp (fun _ : ℕ × Fin k => ℂ) 2`. -/
abbrev H (k : ℕ) : Type := lp (fun _ : Idx k => ℂ) 2

noncomputable instance (k : ℕ) : NormedAddCommGroup (H k) := inferInstance
noncomputable instance (k : ℕ) : InnerProductSpace ℂ (H k) := inferInstance
instance (k : ℕ) : CompleteSpace (H k) := inferInstance

/-- The coordinate injection that drops the zeroth Landau level. -/
def succIdx {k : ℕ} (i : Idx k) : Idx k := (i.1 + 1, i.2)

/-- The coordinate injection `succIdx` is injective. -/
lemma succIdx_injective {k : ℕ} : Function.Injective (succIdx (k := k)) := by
  intro a b h
  apply Prod.ext
  · exact Nat.succ.inj (by simpa [succIdx, Nat.succ_eq_add_one] using congrArg Prod.fst h)
  · simpa [succIdx] using congrArg Prod.snd h

/-- The coordinate function underlying the magnetic Dirac operator. -/
def magneticDiracSeq {k : ℕ} (x : H k) : Idx k → ℂ := fun i => x (succIdx i)

/-- The magnetic Dirac coordinate function is square-summable. -/
lemma magneticDiracSeq_summable {k : ℕ} (x : H k) :
    Summable fun i : Idx k => ‖magneticDiracSeq x i‖ ^ (2 : ℝ) := by
  have hx : Summable fun i : Idx k => ‖x i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa [magneticDiracSeq, Function.comp_def] using hx.comp_injective succIdx_injective

/-- The magnetic Dirac coordinate function belongs to `ℓ²(ℕ × Fin k)`. -/
lemma magneticDiracSeq_memℓp {k : ℕ} (x : H k) : Memℓp (magneticDiracSeq x) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  simpa using magneticDiracSeq_summable x

/-- The magnetic Dirac coordinate function bundled as an element of `ℓ²(ℕ × Fin k)`. -/
def magneticDiracAux {k : ℕ} (x : H k) : H k :=
  ⟨magneticDiracSeq x, magneticDiracSeq_memℓp x⟩

/-- The coordinate formula for the bundled magnetic Dirac sequence. -/
@[simp] lemma magneticDiracAux_apply {k : ℕ} (x : H k) (n : ℕ) (j : Fin k) :
    magneticDiracAux x (n, j) = x (n + 1, j) := rfl

/-- The bundled magnetic Dirac sequence has norm at most the original vector. -/
lemma magneticDiracAux_norm_le {k : ℕ} (x : H k) : ‖magneticDiracAux x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).1
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  have hx : Summable fun i : Idx k => ‖x i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa [magneticDiracAux, magneticDiracSeq] using
    Summable.tsum_le_tsum_of_inj (e := succIdx (k := k)) succIdx_injective
      (fun _ _ => by positivity) (fun _ => le_rfl) (magneticDiracSeq_summable x) hx

/-- The magnetic Dirac operator before adding continuity. -/
noncomputable def magneticDiracLinear (k : ℕ) : H k →ₗ[ℂ] H k where
  toFun := magneticDiracAux
  map_add' := by
    intro x y
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magneticDiracAux (x + y) (n, j) =
      ((magneticDiracAux x : Idx k → ℂ) + (magneticDiracAux y : Idx k → ℂ)) (n, j)
    change ((x + y : H k) : Idx k → ℂ) (n + 1, j) =
      x (n + 1, j) + y (n + 1, j)
    rw [lp.coeFn_add]
    rfl
  map_smul' := by
    intro c x
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magneticDiracAux (c • x) (n, j) = (c • (magneticDiracAux x : Idx k → ℂ)) (n, j)
    simp [magneticDiracAux_apply, lp.coeFn_smul]

/-- The flux-`k` magnetic Dirac model: the backward shift on the Landau-level index. -/
noncomputable def magneticDirac (k : ℕ) : H k →L[ℂ] H k :=
  (magneticDiracLinear k).mkContinuous 1 fun x => by
    change ‖magneticDiracAux x‖ ≤ 1 * ‖x‖
    simpa [one_mul] using magneticDiracAux_norm_le x

/-- Coordinate formula for the flux-`k` magnetic Dirac model. -/
@[simp] theorem magneticDirac_apply {k : ℕ} (x : H k) (n : ℕ) (j : Fin k) :
    magneticDirac k x (n, j) = x (n + 1, j) := rfl

/-- A vector supported on the lowest Landau level. -/
def lowestLevelSeq {k : ℕ} (v : Fin k → ℂ) : Idx k → ℂ :=
  fun i => if i.1 = 0 then v i.2 else 0

/-- Lowest-level vectors have finite support, hence belong to every `ℓᵖ`. -/
lemma lowestLevelSeq_memℓp {k : ℕ} (v : Fin k → ℂ) : Memℓp (lowestLevelSeq v) 2 := by
  refine (memℓp_zero ?_).of_exponent_ge zero_le
  refine (Set.finite_range fun j : Fin k => ((0, j) : Idx k)).subset ?_
  intro i hi
  change lowestLevelSeq v i ≠ 0 at hi
  by_cases h : i.1 = 0
  · exact ⟨i.2, Prod.ext h.symm rfl⟩
  · simp [lowestLevelSeq, h] at hi

/-- A lowest-Landau-level vector bundled as an element of `ℓ²(ℕ × Fin k)`. -/
def lowestLevel {k : ℕ} (v : Fin k → ℂ) : H k :=
  ⟨lowestLevelSeq v, lowestLevelSeq_memℓp v⟩

/-- Coordinate formula for lowest-Landau-level vectors. -/
@[simp] lemma lowestLevel_apply {k : ℕ} (v : Fin k → ℂ) (n : ℕ) (j : Fin k) :
    lowestLevel v (n, j) = if n = 0 then v j else 0 := rfl

/-- Lowest-level vectors lie in the kernel of the magnetic Dirac operator. -/
lemma lowestLevel_mem_ker {k : ℕ} (v : Fin k → ℂ) :
    lowestLevel v ∈ LinearMap.ker (magneticDirac k : H k →ₗ[ℂ] H k) := by
  rw [LinearMap.mem_ker]
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, j⟩
  change magneticDirac k (lowestLevel v) (n, j) = 0
  rw [magneticDirac_apply, lowestLevel_apply]
  simp

/-- The kernel of the magnetic Dirac model is the lowest Landau level `ℂᵏ`. -/
noncomputable def magneticDiracKerEquiv (k : ℕ) [NeZero k] :
    LinearMap.ker (magneticDirac k : H k →ₗ[ℂ] H k) ≃ₗ[ℂ] (Fin k → ℂ) where
  toFun x := fun j => (x : H k) (0, j)
  invFun v := ⟨lowestLevel v, lowestLevel_mem_ker v⟩
  map_add' := by
    intro x y
    ext j
    change ((x : H k) + (y : H k)) (0, j) = (x : H k) (0, j) + (y : H k) (0, j)
    rw [lp.coeFn_add]
    rfl
  map_smul' := by
    intro c x
    ext j
    change (c • (x : H k)) (0, j) = c • (x : H k) (0, j)
    simp [lp.coeFn_smul]
  left_inv := by
    intro x
    apply Subtype.ext
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    cases n with
    | zero =>
        change lowestLevelSeq (fun j => (x : H k) (0, j)) (0, j) = (x : H k) (0, j)
        simp [lowestLevelSeq]
    | succ n =>
        have hx : magneticDirac k (x : H k) = 0 := by
          exact (LinearMap.mem_ker.mp x.2)
        have hcoord : (x : H k) (n + 1, j) = 0 := by
          have h := congrArg (fun y : H k => y (n, j)) hx
          change (x : H k) (n + 1, j) = 0 at h
          exact h
        change lowestLevelSeq (fun j => (x : H k) (0, j)) (n + 1, j) = (x : H k) (n + 1, j)
        simp [lowestLevelSeq, hcoord]
  right_inv := by
    intro v
    ext j
    change lowestLevelSeq v (0, j) = v j
    simp [lowestLevelSeq]

/-- The kernel of the magnetic Dirac model has dimension `k`. -/
theorem magneticDirac_ker_finrank (k : ℕ) [NeZero k] :
    Module.finrank ℂ (LinearMap.ker (magneticDirac k : H k →ₗ[ℂ] H k)) = k := by
  calc
    Module.finrank ℂ (LinearMap.ker (magneticDirac k : H k →ₗ[ℂ] H k))
        = Module.finrank ℂ (Fin k → ℂ) := (magneticDiracKerEquiv k).finrank_eq
    _ = k := Module.finrank_fin_fun ℂ

/-- The magnetic Dirac operator sends the `(m+1,j)` basis vector to the `(m,j)` basis vector. -/
theorem magneticDirac_single_succ {k : ℕ} (m : ℕ) (j : Fin k) :
    magneticDirac k (lp.single 2 ((m + 1, j) : Idx k) (1 : ℂ) : H k) =
      lp.single 2 ((m, j) : Idx k) (1 : ℂ) := by
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, l⟩
  rw [magneticDirac_apply]
  by_cases hn : n = m
  · subst n
    by_cases hl : l = j
    · subst l
      simp [lp.single_apply]
    · simp [lp.single_apply, hl]
  · simp [lp.single_apply, hn]

/-- The orthogonal complement of the magnetic Dirac range is trivial. -/
theorem range_magneticDirac_orthogonal (k : ℕ) :
    (LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k))ᗮ = ⊥ := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_bot]
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨m, j⟩
    have hrange : (lp.single 2 ((m, j) : Idx k) (1 : ℂ) : H k) ∈
        LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k) := by
      rw [LinearMap.mem_range]
      exact ⟨lp.single 2 ((m + 1, j) : Idx k) (1 : ℂ), magneticDirac_single_succ m j⟩
    have hinner : inner ℂ y (lp.single 2 ((m, j) : Idx k) (1 : ℂ) : H k) = 0 :=
      (Submodule.mem_orthogonal' (LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k)) y).1 hy
        _ hrange
    rw [lp.inner_single_right] at hinner
    have hycoord : y (m, j) = 0 := by
      have h' := congrArg (starRingEnd ℂ) hinner
      simpa [RCLike.inner_apply] using h'
    simpa using hycoord
  · intro y hy
    rw [Submodule.mem_bot] at hy
    subst y
    exact zero_mem _

/-- The cokernel contribution to the magnetic Dirac Fredholm index has dimension `0`. -/
theorem range_magneticDirac_orthogonal_finrank (k : ℕ) :
    Module.finrank ℂ ↥((LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k))ᗮ) = 0 := by
  rw [range_magneticDirac_orthogonal, finrank_bot]

/-- A right-inverse coordinate sequence for the backward-shift magnetic Dirac operator. -/
def magneticDiracPreimageSeq {k : ℕ} (y : H k) : Idx k → ℂ :=
  fun i => if i.1 = 0 then 0 else y (i.1 - 1, i.2)

/-- The right-inverse sequence shifts back to the original vector. -/
@[simp] lemma magneticDiracPreimageSeq_succ {k : ℕ} (y : H k) (n : ℕ) (j : Fin k) :
    magneticDiracPreimageSeq y (n + 1, j) = y (n, j) := by
  simp [magneticDiracPreimageSeq]

/-- The right-inverse coordinate sequence is square-summable. -/
lemma magneticDiracPreimageSeq_memℓp {k : ℕ} (y : H k) :
    Memℓp (magneticDiracPreimageSeq y) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  have hy : Summable fun i : Idx k => ‖y i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp y).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  have hyprod :
      (∀ n : ℕ, Summable fun j : Fin k => ‖y (n, j)‖ ^ (2 : ℝ)) ∧
        Summable fun n : ℕ => ∑' j : Fin k, ‖y (n, j)‖ ^ (2 : ℝ) := by
    exact (summable_prod_of_nonneg
      (f := fun i : ℕ × Fin k => ‖y i‖ ^ (2 : ℝ)) (fun _ => by positivity)).1 hy
  have htail : Summable fun n : ℕ =>
      ∑' j : Fin k, ‖magneticDiracPreimageSeq y (n + 1, j)‖ ^ (2 : ℝ) := by
    simpa [magneticDiracPreimageSeq] using hyprod.2
  have hlevels : Summable fun n : ℕ =>
      ∑' j : Fin k, ‖magneticDiracPreimageSeq y (n, j)‖ ^ (2 : ℝ) :=
    (summable_nat_add_iff
      (f := fun n : ℕ =>
        ∑' j : Fin k, ‖magneticDiracPreimageSeq y (n, j)‖ ^ (2 : ℝ)) 1).1 htail
  exact (summable_prod_of_nonneg
    (f := fun i : ℕ × Fin k => ‖magneticDiracPreimageSeq y i‖ ^ (2 : ℝ))
    (fun _ => by positivity)).2 ⟨fun _ => Summable.of_finite, hlevels⟩

/-- A bundled right inverse for the magnetic Dirac operator. -/
def magneticDiracPreimage {k : ℕ} (y : H k) : H k :=
  ⟨magneticDiracPreimageSeq y, magneticDiracPreimageSeq_memℓp y⟩

/-- Coordinate formula for the bundled right inverse. -/
@[simp] lemma magneticDiracPreimage_apply {k : ℕ} (y : H k) (n : ℕ) (j : Fin k) :
    magneticDiracPreimage y (n, j) = if n = 0 then 0 else y (n - 1, j) := rfl

/-- The magnetic Dirac operator is surjective. -/
theorem range_magneticDirac_eq_top (k : ℕ) :
    LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨magneticDiracPreimage y, ?_⟩
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, j⟩
  simp [magneticDirac_apply]

/-- The quotient cokernel of the magnetic Dirac operator has dimension `0`. -/
theorem magneticDirac_coker_finrank (k : ℕ) :
    Module.finrank ℂ (H k ⧸ LinearMap.range (magneticDirac k : H k →ₗ[ℂ] H k)) = 0 := by
  rw [range_magneticDirac_eq_top]
  haveI : Subsingleton (H k ⧸ (⊤ : Submodule ℂ (H k))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- The flux-`k` magnetic Dirac model has Fredholm index `k`. -/
theorem fredholmIndex_magneticDirac (k : ℕ) [NeZero k] :
    SpectralTriples.Fredholm.index (magneticDirac k : H k →ₗ[ℂ] H k) = (k : ℤ) := by
  unfold SpectralTriples.Fredholm.index
  rw [magneticDirac_ker_finrank, magneticDirac_coker_finrank]
  norm_num

/-- A primitive `k`-th root of unity used in the magnetic clock operator. -/
noncomputable def omega (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (k : ℂ))

/-- The magnetic phase `omega k` is nonzero. -/
lemma omega_ne_zero (k : ℕ) : omega k ≠ 0 := by
  unfold omega
  exact Complex.exp_ne_zero _

/-- The magnetic phase `omega k` has norm `1`. -/
lemma norm_omega (k : ℕ) : ‖omega k‖ = 1 := by
  unfold omega
  rw [Complex.norm_exp]
  simp

/-- The magnetic phase is a `k`-th root of unity. -/
lemma omega_pow_card (k : ℕ) [NeZero k] : omega k ^ k = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  have hk : k ≠ 0 := NeZero.ne k
  rw [show (↑k : ℂ) * (2 * ↑Real.pi * Complex.I / ↑k) = 2 * ↑Real.pi * Complex.I by
    field_simp [Nat.cast_ne_zero.mpr hk]]
  simp

/-- The clock phase advances by `omega k` under the cyclic predecessor on `Fin k`. -/
lemma omega_mul_pow_pred (k : ℕ) [NeZero k] (j : Fin k) :
    omega k * omega k ^ (((j - 1 : Fin k) : ℕ)) = omega k ^ (j : ℕ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  by_cases hj : j = 0
  · subst j
    rw [show (((0 : Fin (m + 1)) - 1 : Fin (m + 1)) : ℕ) = m by simp]
    rw [← pow_succ', omega_pow_card]
    simp
  · rw [Fin.val_sub_one_of_ne_zero hj]
    have hjpos : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr ((Fin.val_ne_zero_iff).2 hj)
    rw [← pow_succ']
    congr
    exact Nat.sub_add_cancel hjpos

/-- The coordinate permutation underlying the magnetic shift. -/
def finShiftIdx {k : ℕ} [NeZero k] (i : Idx k) : Idx k := (i.1, i.2 - 1)

/-- The cyclic shift on the guiding-center coordinate is injective. -/
lemma finShiftIdx_injective {k : ℕ} [NeZero k] :
    Function.Injective (finShiftIdx (k := k)) := by
  intro a b h
  apply Prod.ext
  · simpa [finShiftIdx] using congrArg Prod.fst h
  · exact (sub_left_injective (b := (1 : Fin k))) (by
      simpa [finShiftIdx] using congrArg Prod.snd h)

/-- The coordinate function underlying the magnetic clock operator. -/
noncomputable def magClockSeq {k : ℕ} (x : H k) : Idx k → ℂ :=
  fun i => (omega k) ^ (i.2 : ℕ) * x i

/-- The clock coordinate function is square-summable. -/
lemma magClockSeq_summable {k : ℕ} (x : H k) :
    Summable fun i : Idx k => ‖magClockSeq x i‖ ^ (2 : ℝ) := by
  have hx : Summable fun i : Idx k => ‖x i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa [magClockSeq, norm_mul, norm_pow, norm_omega] using hx

/-- The clock coordinate function belongs to `ℓ²(ℕ × Fin k)`. -/
lemma magClockSeq_memℓp {k : ℕ} (x : H k) : Memℓp (magClockSeq x) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  simpa using magClockSeq_summable x

/-- The clock coordinate function bundled as an element of `ℓ²(ℕ × Fin k)`. -/
noncomputable def magClockAux {k : ℕ} (x : H k) : H k :=
  ⟨magClockSeq x, magClockSeq_memℓp x⟩

/-- Coordinate formula for the magnetic clock operator before continuity. -/
@[simp] lemma magClockAux_apply {k : ℕ} (x : H k) (n : ℕ) (j : Fin k) :
    magClockAux x (n, j) = (omega k) ^ (j : ℕ) * x (n, j) := rfl

/-- The bundled magnetic clock sequence has the same norm as the original vector. -/
lemma magClockAux_norm {k : ℕ} (x : H k) : ‖magClockAux x‖ = ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hpow : ‖magClockAux x‖ ^ (2 : ℝ≥0∞).toReal =
      ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
    apply tsum_congr
    intro i
    rcases i with ⟨n, j⟩
    simp [magClockAux, magClockSeq, norm_pow, norm_omega]
  exact Real.rpow_left_injOn hp.ne' (norm_nonneg _) (norm_nonneg _) hpow

/-- The magnetic clock operator before adding continuity. -/
noncomputable def magClockLinear (k : ℕ) : H k →ₗ[ℂ] H k where
  toFun := magClockAux
  map_add' := by
    intro x y
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magClockAux (x + y) (n, j) =
      ((magClockAux x : Idx k → ℂ) + (magClockAux y : Idx k → ℂ)) (n, j)
    change omega k ^ (j : ℕ) * ((x + y : H k) : Idx k → ℂ) (n, j) =
      omega k ^ (j : ℕ) * x (n, j) + omega k ^ (j : ℕ) * y (n, j)
    rw [lp.coeFn_add, Pi.add_apply]
    ring_nf
  map_smul' := by
    intro c x
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magClockAux (c • x) (n, j) = (c • (magClockAux x : Idx k → ℂ)) (n, j)
    simp [magClockAux_apply, lp.coeFn_smul]
    ring

/-- The magnetic clock translation on the `ℂᵏ` guiding-center factor. -/
noncomputable def magClock (k : ℕ) : H k →L[ℂ] H k :=
  (magClockLinear k).mkContinuous 1 fun x => by
    change ‖magClockAux x‖ ≤ 1 * ‖x‖
    simpa [one_mul] using le_of_eq (magClockAux_norm x)

/-- Coordinate formula for the magnetic clock translation. -/
@[simp] theorem magClock_apply {k : ℕ} (x : H k) (n : ℕ) (j : Fin k) :
    magClock k x (n, j) = (omega k) ^ (j : ℕ) * x (n, j) := rfl

/-- The coordinate function underlying the magnetic cyclic shift. -/
def magShiftSeq {k : ℕ} [NeZero k] (x : H k) : Idx k → ℂ :=
  fun i => x (finShiftIdx i)

/-- The magnetic cyclic shift coordinate function is square-summable. -/
lemma magShiftSeq_summable {k : ℕ} [NeZero k] (x : H k) :
    Summable fun i : Idx k => ‖magShiftSeq x i‖ ^ (2 : ℝ) := by
  have hx : Summable fun i : Idx k => ‖x i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa [magShiftSeq, Function.comp_def] using hx.comp_injective finShiftIdx_injective

/-- The magnetic cyclic shift coordinate function belongs to `ℓ²(ℕ × Fin k)`. -/
lemma magShiftSeq_memℓp {k : ℕ} [NeZero k] (x : H k) : Memℓp (magShiftSeq x) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  simpa using magShiftSeq_summable x

/-- The magnetic cyclic shift coordinate function bundled as an element of `ℓ²(ℕ × Fin k)`. -/
def magShiftAux {k : ℕ} [NeZero k] (x : H k) : H k :=
  ⟨magShiftSeq x, magShiftSeq_memℓp x⟩

/-- Coordinate formula for the magnetic cyclic shift before continuity. -/
@[simp] lemma magShiftAux_apply {k : ℕ} [NeZero k] (x : H k) (n : ℕ) (j : Fin k) :
    magShiftAux x (n, j) = x (n, j - 1) := rfl

/-- The bundled magnetic cyclic shift sequence has norm at most the original vector. -/
lemma magShiftAux_norm_le {k : ℕ} [NeZero k] (x : H k) : ‖magShiftAux x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).1
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  have hx : Summable fun i : Idx k => ‖x i‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa [magShiftAux, magShiftSeq] using
    Summable.tsum_le_tsum_of_inj (e := finShiftIdx (k := k)) finShiftIdx_injective
      (fun _ _ => by positivity) (fun _ => le_rfl) (magShiftSeq_summable x) hx

/-- The magnetic cyclic shift before adding continuity. -/
noncomputable def magShiftLinear (k : ℕ) [NeZero k] : H k →ₗ[ℂ] H k where
  toFun := magShiftAux
  map_add' := by
    intro x y
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magShiftAux (x + y) (n, j) =
      ((magShiftAux x : Idx k → ℂ) + (magShiftAux y : Idx k → ℂ)) (n, j)
    change ((x + y : H k) : Idx k → ℂ) (n, j - 1) =
      x (n, j - 1) + y (n, j - 1)
    rw [lp.coeFn_add]
    rfl
  map_smul' := by
    intro c x
    refine lp.ext (funext fun i => ?_)
    rcases i with ⟨n, j⟩
    change magShiftAux (c • x) (n, j) = (c • (magShiftAux x : Idx k → ℂ)) (n, j)
    simp [magShiftAux_apply, lp.coeFn_smul]

/-- The magnetic cyclic shift translation on the `ℂᵏ` guiding-center factor. -/
noncomputable def magShift (k : ℕ) [NeZero k] : H k →L[ℂ] H k :=
  (magShiftLinear k).mkContinuous 1 fun x => by
    change ‖magShiftAux x‖ ≤ 1 * ‖x‖
    simpa [one_mul] using magShiftAux_norm_le x

/-- Coordinate formula for the magnetic cyclic shift translation. -/
@[simp] theorem magShift_apply {k : ℕ} [NeZero k] (x : H k) (n : ℕ) (j : Fin k) :
    magShift k x (n, j) = x (n, j - 1) := rfl

/-- The magnetic clock and shift translations satisfy the finite Weyl commutation relation. -/
theorem magneticTranslation_weyl (k : ℕ) [NeZero k] :
    magClock k * magShift k = (omega k) • (magShift k * magClock k) := by
  apply ContinuousLinearMap.ext
  intro x
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, j⟩
  simp only [ContinuousLinearMap.coe_mul', Function.comp_apply, magClock_apply, magShift_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, lp.coeFn_smul, smul_eq_mul]
  rw [← omega_mul_pow_pred k j]
  ring

/-- The magnetic clock translation commutes with the magnetic Dirac operator. -/
theorem magClock_comm_dirac (k : ℕ) :
    (magClock k).comp (magneticDirac k) = (magneticDirac k).comp (magClock k) := by
  apply ContinuousLinearMap.ext
  intro x
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, j⟩
  simp [ContinuousLinearMap.comp_apply]

/-- The magnetic cyclic shift translation commutes with the magnetic Dirac operator. -/
theorem magShift_comm_dirac (k : ℕ) [NeZero k] :
    (magShift k).comp (magneticDirac k) = (magneticDirac k).comp (magShift k) := by
  apply ContinuousLinearMap.ext
  intro x
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨n, j⟩
  simp [ContinuousLinearMap.comp_apply]

end SpectralTriples.MagneticDirac
