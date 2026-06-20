/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import SpectralTriples.Examples.ThetaSections

/-! # Fourier coefficients of holomorphic periodic functions: the contour shift

The analytic foundation for **M3a** (`docs/INDEX_PAIRING.md`): the upper bound
`dim H⁰(L_k) ≤ k` for theta sections rests on the **contour shift** — that the Fourier-type
period integral of an entire `1`-periodic function is independent of the horizontal line it is
taken on. Concretely, for `f : ℂ → ℂ` entire with `f(z+1) = f(z)`,

  `∫₀¹ f(x + i y) dx`  is independent of `y`.

This is Cauchy–Goursat on the rectangle `[0,1] × [y₁, y₂]`: the two vertical sides cancel by
periodicity (`f(1 + iy) = f(iy)`), leaving the two horizontal integrals equal. From it, the
intrinsic Fourier coefficient `a_m = ∫₀¹ f(x+iy) e^{-2πim(x+iy)} dx` is well-defined, and the
`τ`-quasi-periodicity of a theta section turns into the recursion `a_{m+k} = e^{πiτ(2m+k)} a_m`.

## Main results

* `SpectralTriples.periodIntegral_eq_of_periodic`: the contour shift.
-/

@[expose] public section

namespace SpectralTriples

open Complex intervalIntegral
open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- **Contour shift.** For an entire `1`-periodic function `f`, the period integral
`∫₀¹ f(x + i y) dx` does not depend on the height `y`. (Cauchy–Goursat on the rectangle
`[0,1] × [y₁, y₂]`; the vertical sides cancel by periodicity.) -/
theorem periodIntegral_eq_of_periodic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) (y₁ y₂ : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..1, f (↑x + ↑y₁ * I)) = ∫ x : ℝ in (0 : ℝ)..1, f (↑x + ↑y₂ * I) := by
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ((y₁ : ℂ) * I)
    (1 + (y₂ : ℂ) * I) hf.differentiableOn
  simp only [add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero, ofReal_one, ofReal_zero] at H
  have hvert : (∫ y : ℝ in y₁..y₂, f ((1 : ℂ) + ↑y * I))
      = ∫ y : ℝ in y₁..y₂, f (↑y * I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [add_comm]
    exact hper _
  rw [hvert, add_sub_cancel_right] at H
  exact sub_eq_zero.mp H

/-- Fourier coefficient of a `1`-periodic entire function, computed on the real period. -/
noncomputable def holCoeff (f : ℂ → ℂ) (m : ℤ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..1,
    f (x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ))

/-- Holomorphic sections of the degree-`k` line bundle on the square torus. -/
def holSection (k : ℕ) : Submodule ℂ (ℂ → ℂ) where
  carrier :=
    { f | Differentiable ℂ f ∧
        (∀ z : ℂ, f (z + 1) = f z) ∧
          (∀ z : ℂ, f (z + Complex.I) =
            Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z) }
  zero_mem' := by
    constructor
    · fun_prop
    constructor <;> intro z <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · exact hf.1.add hg.1
    constructor
    · intro z
      simp only [Pi.add_apply]
      rw [hf.2.1 z, hg.2.1 z]
    · intro z
      simp only [Pi.add_apply]
      rw [hf.2.2 z, hg.2.2 z]
      ring
  smul_mem' := by
    intro c f hf
    constructor
    · exact hf.1.const_smul c
    constructor
    · intro z
      simp only [Pi.smul_apply]
      rw [hf.2.1 z]
    · intro z
      simp only [Pi.smul_apply]
      rw [hf.2.2 z]
      ring

lemma holCoeff_intervalIntegrable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (m : ℤ) :
    IntervalIntegrable
      (fun x : ℝ => f (x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)))
      volume (0 : ℝ) 1 := by
  apply Continuous.intervalIntegrable
  exact (hf.continuous.comp continuous_ofReal).mul (by fun_prop)

lemma holCoeff_add {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (m : ℤ) :
    holCoeff (f + g) m = holCoeff f m + holCoeff g m := by
  unfold holCoeff
  rw [← intervalIntegral.integral_add (holCoeff_intervalIntegrable hf m)
    (holCoeff_intervalIntegrable hg m)]
  apply intervalIntegral.integral_congr
  intro x _
  simp [add_mul]

lemma holCoeff_smul (c : ℂ) (f : ℂ → ℂ) (m : ℤ) :
    holCoeff (c • f) m = c * holCoeff f m := by
  unfold holCoeff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp [mul_assoc]

noncomputable def realPeriodLift (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) : C(AddCircle (1 : ℝ), ℂ) := by
  let g : ℝ → ℂ := fun x => f (x : ℂ)
  have hgper : Function.Periodic g (1 : ℝ) := by
    intro x
    simpa [g] using hper (x : ℂ)
  refine ⟨hgper.lift, ?_⟩
  have hgcont : Continuous g := hf.continuous.comp continuous_ofReal
  have hs :
      ∀ a b : ℝ,
        (QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ))) a b →
          g a = g b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    obtain ⟨n, hn⟩ := hab
    exact (hgper.zsmul n _).symm.trans (congr_arg g (add_eq_of_eq_neg_add hn))
  simpa [Function.Periodic.lift] using
    hgcont.quotient_liftOn'
      (s := QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ))) hs

lemma realPeriodLift_coe (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) (x : ℝ) :
    realPeriodLift f hf hper (x : AddCircle (1 : ℝ)) = f (x : ℂ) := by
  simp [realPeriodLift]

private lemma star_exp_fourier_arg (m : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ))) =
      Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

lemma fourierCoeff_realPeriodLift_eq_holCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) (m : ℤ) :
    fourierCoeff (realPeriodLift f hf hper) m = holCoeff f m := by
  rw [fourierCoeff_eq_intervalIntegral (realPeriodLift f hf hper) m (0 : ℝ)]
  norm_num
  unfold holCoeff
  apply intervalIntegral.integral_congr
  intro x _
  simp only [realPeriodLift_coe]
  rw [star_exp_fourier_arg m x]
  ring

lemma holCoeff_shift {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) (m : ℤ) :
    holCoeff (fun z => f (z + Complex.I)) m =
      Complex.exp (-2 * Real.pi * (m : ℂ)) * holCoeff f m := by
  let g : ℂ → ℂ :=
    fun z => f z * Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * z)
  have hg : Differentiable ℂ g := by
    dsimp [g]
    fun_prop
  have hexp_period : Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Complex.exp_int_mul_two_pi_mul_I (-m))
  have hgper : ∀ z : ℂ, g (z + 1) = g z := by
    intro z
    dsimp [g]
    rw [hper z]
    have hsplit :
        -2 * Real.pi * Complex.I * (m : ℂ) * (z + 1) =
          (-2 * Real.pi * Complex.I * (m : ℂ) * z) +
            (-2 * Real.pi * Complex.I * (m : ℂ)) := by
      ring
    rw [hsplit, Complex.exp_add, hexp_period]
    ring
  have H := periodIntegral_eq_of_periodic hg hgper (0 : ℝ) (1 : ℝ)
  have hleft :
      (∫ x : ℝ in (0 : ℝ)..1, g ((x : ℂ) + (0 : ℝ) * Complex.I)) =
        holCoeff f m := by
    unfold holCoeff
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [g]
    ring_nf
  have hright :
      (∫ x : ℝ in (0 : ℝ)..1, g ((x : ℂ) + (1 : ℝ) * Complex.I)) =
        Complex.exp (2 * Real.pi * (m : ℂ)) * holCoeff (fun z => f (z + Complex.I)) m := by
    unfold holCoeff
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [g]
    have hsplit :
        -2 * Real.pi * Complex.I * (m : ℂ) * ((x : ℂ) + 1 * Complex.I) =
          2 * Real.pi * (m : ℂ) +
            (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) := by
      ring_nf
      rw [Complex.I_sq]
      norm_num
    rw [hsplit, Complex.exp_add]
    ring_nf
  have Hcoeff : holCoeff f m =
      Complex.exp (2 * Real.pi * (m : ℂ)) * holCoeff (fun z => f (z + Complex.I)) m := by
    rw [← hleft, ← hright]
    exact H
  calc
    holCoeff (fun z => f (z + Complex.I)) m =
        (Complex.exp (2 * Real.pi * (m : ℂ)))⁻¹ * holCoeff f m := by
      rw [Hcoeff]
      field_simp [Complex.exp_ne_zero]
    _ = Complex.exp (-2 * Real.pi * (m : ℂ)) * holCoeff f m := by
      rw [← Complex.exp_neg]
      congr 1
      ring_nf

lemma holCoeff_mul_automorphy (f : ℂ → ℂ) (m : ℤ) (k : ℕ) :
    holCoeff
        (fun z => Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z)
        m =
      Complex.exp (Real.pi * (k : ℂ)) * holCoeff f (m + k) := by
  unfold holCoeff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp
  have hsplit :
      -Real.pi * Complex.I * (k : ℂ) * (2 * (x : ℂ) + Complex.I) =
        Real.pi * (k : ℂ) + (-2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
    ring_nf
    rw [Complex.I_sq]
    norm_num
  have hcombine :
      Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) =
        Complex.exp (-2 * Real.pi * Complex.I * ((m + k : ℤ) : ℂ) * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  rw [hsplit, Complex.exp_add]
  calc
    (Complex.exp (Real.pi * (k : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) * f (x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) =
        Complex.exp (Real.pi * (k : ℂ)) * f (x : ℂ) *
          (Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) *
            Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ))) := by
      ring
    _ = Complex.exp (Real.pi * (k : ℂ)) * f (x : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I * ((m + k : ℤ) : ℂ) * (x : ℂ)) := by
      rw [hcombine]
    _ = Complex.exp (Real.pi * (k : ℂ)) *
          (f (x : ℂ) *
            Complex.exp (-2 * Real.pi * Complex.I * ((m + k : ℤ) : ℂ) * (x : ℂ))) := by
      ring

lemma holCoeff_recursion {f : ℂ → ℂ} {k : ℕ} (hf : f ∈ holSection k) (m : ℤ) :
    holCoeff f (m + k) =
      Complex.exp (-Real.pi * (2 * (m : ℂ) + (k : ℂ))) * holCoeff f m := by
  have hfun :
      (fun z : ℂ => f (z + Complex.I)) =
        fun z : ℂ =>
          Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z := by
    funext z
    exact hf.2.2 z
  have hcoeff :
      holCoeff (fun z : ℂ => f (z + Complex.I)) m =
        holCoeff
          (fun z : ℂ =>
            Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z)
          m := by
    rw [hfun]
  rw [holCoeff_shift hf.1 hf.2.1 m, holCoeff_mul_automorphy f m k] at hcoeff
  calc
    holCoeff f (m + k) =
        (Complex.exp (Real.pi * (k : ℂ)))⁻¹ *
          (Complex.exp (-2 * Real.pi * (m : ℂ)) * holCoeff f m) := by
      rw [hcoeff]
      field_simp [Complex.exp_ne_zero]
    _ = Complex.exp (-Real.pi * (2 * (m : ℂ) + (k : ℂ))) * holCoeff f m := by
      rw [← Complex.exp_neg]
      rw [show Complex.exp (-(Real.pi * (k : ℂ))) *
            (Complex.exp (-2 * Real.pi * (m : ℂ)) * holCoeff f m) =
            (Complex.exp (-(Real.pi * (k : ℂ))) *
              Complex.exp (-2 * Real.pi * (m : ℂ))) * holCoeff f m by ring]
      rw [← Complex.exp_add]
      congr 1
      ring_nf

lemma holCoeff_step_zero_iff {f : ℂ → ℂ} {k : ℕ} (hf : f ∈ holSection k) (m : ℤ) :
    holCoeff f (m + k) = 0 ↔ holCoeff f m = 0 := by
  rw [holCoeff_recursion hf m]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  · intro h
    simp [h]

lemma holCoeff_eq_zero_of_forall_lt {f : ℂ → ℂ} {k : ℕ} [NeZero k]
    (hf : f ∈ holSection k) (h : ∀ j : ℕ, j < k → holCoeff f j = 0) :
    ∀ m : ℤ, holCoeff f m = 0 := by
  have hkpos_nat : 0 < k := Nat.pos_iff_ne_zero.mpr (NeZero.ne k)
  have hkpos_int : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos_nat
  have hpropagate :
      ∀ (j q : ℤ), holCoeff f j = 0 → holCoeff f (j + q * (k : ℤ)) = 0 := by
    intro j q hj
    induction q using Int.induction_on with
    | zero =>
        simpa using hj
    | succ n ih =>
        have hnext : holCoeff f ((j + (n : ℤ) * (k : ℤ)) + (k : ℤ)) = 0 :=
          (holCoeff_step_zero_iff hf (j + (n : ℤ) * (k : ℤ))).2 ih
        convert hnext using 1
        ring_nf
    | pred n ih =>
        have hnext :
            holCoeff f ((j + ((-(n : ℤ) - 1) * (k : ℤ))) + (k : ℤ)) = 0 := by
          convert ih using 1
          ring_nf
        exact (holCoeff_step_zero_iff hf (j + ((-(n : ℤ) - 1) * (k : ℤ)))).1 hnext
  intro m
  let j : ℕ := (m % (k : ℤ)).toNat
  have hnonneg : 0 ≤ m % (k : ℤ) := Int.emod_nonneg m (by exact_mod_cast (NeZero.ne k))
  have hj_cast : (j : ℤ) = m % (k : ℤ) := Int.toNat_of_nonneg hnonneg
  have hj_lt_int : (j : ℤ) < (k : ℤ) := by
    simpa [hj_cast] using Int.emod_lt_of_pos m hkpos_int
  have hj_lt : j < k := by exact_mod_cast hj_lt_int
  have hrepr : (j : ℤ) + (m / (k : ℤ)) * (k : ℤ) = m := by
    rw [hj_cast]
    rw [mul_comm]
    exact Int.emod_add_mul_ediv m (k : ℤ)
  have hz := hpropagate (j : ℤ) (m / (k : ℤ)) (h j hj_lt)
  rwa [hrepr] at hz

lemma eq_zero_of_holCoeff_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) (h : ∀ m : ℤ, holCoeff f m = 0) :
    f = 0 := by
  let F := realPeriodLift f hf hper
  have hFcoeff : ∀ m : ℤ, fourierCoeff F m = 0 := by
    intro m
    rw [show F = realPeriodLift f hf hper by rfl,
      fourierCoeff_realPeriodLift_eq_holCoeff hf hper m, h m]
  have hFfun : fourierCoeff F = fun _ : ℤ => (0 : ℂ) := by
    funext m
    exact hFcoeff m
  have hsumm : Summable (fourierCoeff F) := by
    rw [hFfun]
    exact summable_zero
  have hFzero : ∀ x : AddCircle (1 : ℝ), F x = 0 := by
    intro x
    have hs := has_pointwise_sum_fourier_series_of_summable hsumm x
    have hs0 : HasSum (fun _ : ℤ => (0 : ℂ)) (F x) := by
      simpa [hFcoeff] using hs
    exact hs0.unique hasSum_zero
  have hreal : ∀ x : ℝ, f (x : ℂ) = 0 := by
    intro x
    simpa [F] using hFzero (x : AddCircle (1 : ℝ))
  let u : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have huR : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu0 : Tendsto u atTop (𝓝 (0 : ℂ)) := by
    change Tendsto
      (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ))
    exact (continuous_ofReal.tendsto 0).comp huR
  have hune : ∀ᶠ n : ℕ in atTop, u n ∈ ({0}ᶜ : Set ℂ) := by
    exact Filter.Eventually.of_forall fun n => by
      simp [u, Nat.cast_add_one_ne_zero]
  have hu : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hu0, hune⟩
  have hzseq : ∀ᶠ n : ℕ in atTop, f (u n) = 0 := by
    exact Filter.Eventually.of_forall fun n => by
      simpa [u] using hreal (1 / ((n : ℝ) + 1))
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), f z = (0 : ℂ) :=
    Filter.Tendsto.frequently hu (Filter.Eventually.frequently hzseq)
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hf
  have hzero_an : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    simpa using
      (Complex.analyticOnNhd_univ_iff_differentiable).2 (differentiable_const (c := (0 : ℂ)))
  exact AnalyticOnNhd.eq_of_frequently_eq hf_an hzero_an hfreq

noncomputable def coeffMap (k : ℕ) : holSection k →ₗ[ℂ] (Fin k → ℂ) where
  toFun f j := holCoeff (f : ℂ → ℂ) (j : ℤ)
  map_add' := by
    intro f g
    ext j
    simpa using holCoeff_add f.2.1 g.2.1 (j : ℤ)
  map_smul' := by
    intro c f
    ext j
    simpa using holCoeff_smul c (f : ℂ → ℂ) (j : ℤ)

lemma coeffMap_eq_zero (k : ℕ) [NeZero k] {f : holSection k} (hfcoeff : coeffMap k f = 0) :
    f = 0 := by
  apply Subtype.ext
  apply eq_zero_of_holCoeff_eq_zero f.2.1 f.2.2.1
  apply holCoeff_eq_zero_of_forall_lt f.2
  intro j hj
  have hfj := congrFun hfcoeff ⟨j, hj⟩
  simpa [coeffMap] using hfj

lemma coeffMap_injective (k : ℕ) [NeZero k] : Function.Injective (coeffMap k) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply coeffMap_eq_zero k
  rw [map_sub, hfg, sub_self]

theorem holSection_finrank_le (k : ℕ) [NeZero k] :
    Module.finrank ℂ (holSection k) ≤ k := by
  calc
    Module.finrank ℂ (holSection k) ≤ Module.finrank ℂ (Fin k → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective (coeffMap_injective k)
    _ = k := Module.finrank_fin_fun ℂ

noncomputable def thetaHolSection (k : ℕ) [NeZero k] (a : Fin k) : holSection k :=
  ⟨ThetaSections.thetaSection k a, by
    constructor
    · exact ThetaSections.differentiable_thetaSection k a
    constructor
    · intro z
      exact ThetaSections.thetaSection_periodic k a z
    · intro z
      exact ThetaSections.thetaSection_quasiPeriodic k a z⟩

lemma thetaHolSection_linearIndependent (k : ℕ) [NeZero k] :
    LinearIndependent ℂ (thetaHolSection k) := by
  have hcomp : (holSection k).subtype ∘ thetaHolSection k = ThetaSections.thetaSection k := by
    funext a
    rfl
  have h := ThetaSections.thetaSection_linearIndependent k
  rw [← hcomp] at h
  exact h.of_comp (holSection k).subtype

theorem holSection_finrank_eq (k : ℕ) [NeZero k] :
    Module.finrank ℂ (holSection k) = k := by
  haveI : FiniteDimensional ℂ (holSection k) :=
    FiniteDimensional.of_injective (coeffMap k) (coeffMap_injective k)
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range (thetaHolSection k))) = k := by
    simpa [Fintype.card_fin] using finrank_span_eq_card (thetaHolSection_linearIndependent k)
  apply le_antisymm (holSection_finrank_le k)
  calc
    k = Module.finrank ℂ (Submodule.span ℂ (Set.range (thetaHolSection k))) := hspan.symm
    _ ≤ Module.finrank ℂ (holSection k) := Submodule.finrank_le _

/-- Holomorphic sections of the degree-`-k` line bundle on the square torus. The sign of the
`i`-period automorphy is the conjugate/negative-degree sign relative to `holSection`. -/
def holSectionNeg (k : ℕ) : Submodule ℂ (ℂ → ℂ) where
  carrier :=
    { f | Differentiable ℂ f ∧
        (∀ z : ℂ, f (z + 1) = f z) ∧
          (∀ z : ℂ, f (z + Complex.I) =
            Complex.exp (Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z) }
  zero_mem' := by
    constructor
    · fun_prop
    constructor <;> intro z <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · exact hf.1.add hg.1
    constructor
    · intro z
      simp only [Pi.add_apply]
      rw [hf.2.1 z, hg.2.1 z]
    · intro z
      simp only [Pi.add_apply]
      rw [hf.2.2 z, hg.2.2 z]
      ring
  smul_mem' := by
    intro c f hf
    constructor
    · exact hf.1.const_smul c
    constructor
    · intro z
      simp only [Pi.smul_apply]
      rw [hf.2.1 z]
    · intro z
      simp only [Pi.smul_apply]
      rw [hf.2.2 z]
      ring

lemma holCoeff_mul_automorphyNeg (f : ℂ → ℂ) (m : ℤ) (k : ℕ) :
    holCoeff
        (fun z => Complex.exp (Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z)
        m =
      Complex.exp (-Real.pi * (k : ℂ)) * holCoeff f (m - (k : ℤ)) := by
  unfold holCoeff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp
  have hsplit :
      Real.pi * Complex.I * (k : ℂ) * (2 * (x : ℂ) + Complex.I) =
        -Real.pi * (k : ℂ) + (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
    ring_nf
    rw [Complex.I_sq]
    norm_num
    ring
  have hcombine :
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) =
        Complex.exp (-2 * Real.pi * Complex.I * (((m - (k : ℤ)) : ℤ) : ℂ) *
          (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  rw [hsplit, Complex.exp_add]
  calc
    (Complex.exp (-Real.pi * (k : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) * f (x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) =
        Complex.exp (-Real.pi * (k : ℂ)) * f (x : ℂ) *
          (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) *
            Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ))) := by
      ring
    _ = Complex.exp (-Real.pi * (k : ℂ)) * f (x : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I * (((m - (k : ℤ)) : ℤ) : ℂ) *
            (x : ℂ)) := by
      rw [hcombine]
    _ = Complex.exp (-Real.pi * (k : ℂ)) *
          (f (x : ℂ) *
            Complex.exp (-2 * Real.pi * Complex.I * (((m - (k : ℤ)) : ℤ) : ℂ) *
              (x : ℂ))) := by
      ring

lemma holCoeffNeg_recursion {f : ℂ → ℂ} {k : ℕ} (hf : f ∈ holSectionNeg k) (m : ℤ) :
    holCoeff f (m + k) =
      Complex.exp (Real.pi * (2 * (m : ℂ) + (k : ℂ))) * holCoeff f m := by
  have hfun :
      (fun z : ℂ => f (z + Complex.I)) =
        fun z : ℂ =>
          Complex.exp (Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z := by
    funext z
    exact hf.2.2 z
  have hcoeff :
      holCoeff (fun z : ℂ => f (z + Complex.I)) (m + k) =
        holCoeff
          (fun z : ℂ =>
            Complex.exp (Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) * f z)
          (m + k) := by
    rw [hfun]
  rw [holCoeff_shift hf.1 hf.2.1 (m + k), holCoeff_mul_automorphyNeg f (m + k) k] at hcoeff
  have hsub : (m + (k : ℤ) - (k : ℤ) : ℤ) = m := by ring
  rw [hsub] at hcoeff
  calc
    holCoeff f (m + k) =
        (Complex.exp (-2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℂ)))⁻¹ *
          (Complex.exp (-2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℂ)) *
            holCoeff f (m + k)) := by
      field_simp [Complex.exp_ne_zero]
    _ = (Complex.exp (-2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℂ)))⁻¹ *
          (Complex.exp (-Real.pi * (k : ℂ)) * holCoeff f m) := by
      rw [hcoeff]
    _ = Complex.exp (Real.pi * (2 * (m : ℂ) + (k : ℂ))) * holCoeff f m := by
      rw [← Complex.exp_neg]
      rw [show Complex.exp (-(-2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℂ))) *
            (Complex.exp (-Real.pi * (k : ℂ)) * holCoeff f m) =
            (Complex.exp (-(-2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℂ))) *
              Complex.exp (-Real.pi * (k : ℂ))) * holCoeff f m by ring]
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring_nf

lemma holCoeffNeg_step_zero_iff {f : ℂ → ℂ} {k : ℕ} (hf : f ∈ holSectionNeg k)
    (m : ℤ) :
    holCoeff f (m + k) = 0 ↔ holCoeff f m = 0 := by
  rw [holCoeffNeg_recursion hf m]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  · intro h
    simp [h]

lemma holCoeff_tendsto_atTop_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + 1) = f z) :
    Tendsto (fun m : ℤ => holCoeff f m) atTop (𝓝 0) := by
  let F := realPeriodLift f hf hper
  let FL2 : Lp ℂ 2 AddCircle.haarAddCircle :=
    (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ) F
  have hsumm_sq_L2 :
      Summable (fun m : ℤ => ‖fourierCoeff (FL2 : AddCircle (1 : ℝ) → ℂ) m‖ ^ 2) :=
    (hasSum_sq_fourierCoeff FL2).summable
  have hrewrite :
      (fun m : ℤ => ‖fourierCoeff (FL2 : AddCircle (1 : ℝ) → ℂ) m‖ ^ 2) =
        fun m : ℤ => ‖fourierCoeff F m‖ ^ 2 := by
    funext m
    rw [show fourierCoeff (FL2 : AddCircle (1 : ℝ) → ℂ) m = fourierCoeff F m from by
      simpa [FL2] using fourierCoeff_toLp F m]
  have hsumm_sq : Summable (fun m : ℤ => ‖fourierCoeff F m‖ ^ 2) := by
    simpa [hrewrite] using hsumm_sq_L2
  have hsq_atTop : Tendsto (fun m : ℤ => ‖fourierCoeff F m‖ ^ 2) atTop (𝓝 0) :=
    hsumm_sq.tendsto_cofinite_zero.mono_left Filter.atTop_le_cofinite
  have hsqrt :
      Tendsto (fun m : ℤ => Real.sqrt (‖fourierCoeff F m‖ ^ 2)) atTop
        (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq_atTop
  have hnorm : Tendsto (fun m : ℤ => ‖fourierCoeff F m‖) atTop (𝓝 0) := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg, Real.sqrt_zero] using hsqrt
  have hcoeff : Tendsto (fun m : ℤ => fourierCoeff F m) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  simpa [F, fourierCoeff_realPeriodLift_eq_holCoeff hf hper] using hcoeff

private lemma int_progression_tendsto_atTop (j : ℤ) (k : ℕ) [NeZero k] :
    Tendsto (fun n : ℕ => j + (n : ℤ) * (k : ℤ)) atTop atTop := by
  have hkpos_nat : 0 < k := Nat.pos_iff_ne_zero.mpr (NeZero.ne k)
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge (b - j)
  refine ⟨N, ?_⟩
  intro n hn
  have hn_int : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hle_n : b - j ≤ (n : ℤ) := hN.trans hn_int
  have hk_one : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hn_nonneg : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hn_le_mul : (n : ℤ) ≤ (n : ℤ) * (k : ℤ) := by
    nlinarith [mul_le_mul_of_nonneg_left hk_one hn_nonneg]
  have : b - j ≤ (n : ℤ) * (k : ℤ) := hle_n.trans hn_le_mul
  omega

lemma holCoeffNeg_eq_zero {f : ℂ → ℂ} {k : ℕ} [NeZero k] (hf : f ∈ holSectionNeg k) :
    ∀ m : ℤ, holCoeff f m = 0 := by
  intro j
  let b : ℕ → ℂ := fun n => holCoeff f (j + (n : ℤ) * (k : ℤ))
  have hprog := int_progression_tendsto_atTop j k
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    simpa [b] using (holCoeff_tendsto_atTop_zero hf.1 hf.2.1).comp hprog
  have hb_norm_tendsto : Tendsto (fun n : ℕ => ‖b n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hb_tendsto
  have hmono_event : ∀ᶠ n : ℕ in atTop, ‖b n‖ ≤ ‖b (n + 1)‖ := by
    filter_upwards [hprog.eventually_ge_atTop 0] with n hn_nonneg
    have hrec := holCoeffNeg_recursion hf (j + (n : ℤ) * (k : ℤ))
    have hidx : j + ((n + 1 : ℕ) : ℤ) * (k : ℤ) =
        (j + (n : ℤ) * (k : ℤ)) + (k : ℤ) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    have hbrec : b (n + 1) =
        Complex.exp
          (Real.pi * (2 * ((j + (n : ℤ) * (k : ℤ) : ℤ) : ℂ) + (k : ℂ))) * b n := by
      change holCoeff f (j + ((n + 1 : ℕ) : ℤ) * (k : ℤ)) = _
      rw [hidx]
      exact hrec
    have hfactor_ge_one :
        1 ≤ ‖Complex.exp
          (Real.pi * (2 * ((j + (n : ℤ) * (k : ℤ) : ℤ) : ℂ) + (k : ℂ)))‖ := by
      rw [Complex.norm_exp]
      apply Real.one_le_exp_iff.mpr
      have hm_nonneg : 0 ≤ (((j + (n : ℤ) * (k : ℤ) : ℤ) : ℝ)) := by
        exact_mod_cast hn_nonneg
      have hinside : 0 ≤ 2 * (((j + (n : ℤ) * (k : ℤ) : ℤ) : ℝ)) + (k : ℝ) := by
        positivity
      exact by simpa using mul_nonneg Real.pi_pos.le hinside
    rw [hbrec, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hfactor_ge_one
  obtain ⟨N, hNmono⟩ := Filter.eventually_atTop.mp hmono_event
  have hbN_zero : b N = 0 := by
    by_contra hNne
    have hNpos : 0 < ‖b N‖ := norm_pos_iff.mpr hNne
    obtain ⟨M, hMsmall⟩ :=
      (Metric.tendsto_atTop.mp hb_norm_tendsto) (‖b N‖ / 2) (half_pos hNpos)
    let n := max N M
    have hNle : N ≤ n := le_max_left N M
    have hMle : M ≤ n := le_max_right N M
    have htail : ‖b N‖ ≤ ‖b n‖ := by
      exact Nat.le_induction (by exact le_rfl)
        (fun r hr ih => ih.trans (hNmono r hr)) n hNle
    have hsmall : ‖b n‖ < ‖b N‖ / 2 := by
      have := hMsmall n hMle
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (b n))] using this
    exact (not_lt_of_ge (half_lt_self hNpos).le) (lt_of_le_of_lt htail hsmall)
  have hback : ∀ n : ℕ, b n = 0 → b 0 = 0 := by
    intro n hn
    induction n with
    | zero =>
        simpa using hn
    | succ n ih =>
        apply ih
        have hidx : j + (((n + 1 : ℕ) : ℤ) * (k : ℤ)) =
            (j + (n : ℤ) * (k : ℤ)) + (k : ℤ) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring
        have hstep : holCoeff f ((j + (n : ℤ) * (k : ℤ)) + (k : ℤ)) = 0 := by
          change holCoeff f (j + (((n + 1 : ℕ) : ℤ) * (k : ℤ))) = 0 at hn
          rwa [hidx] at hn
        have hprev := (holCoeffNeg_step_zero_iff hf (j + (n : ℤ) * (k : ℤ))).1 hstep
        simpa [b] using hprev
  have hb0 := hback N hbN_zero
  simpa [b] using hb0

/-- The negative-degree line bundle has no nonzero holomorphic sections:
`H^0(L_{-k}) = 0` for `k > 0`. By Serre duality this is the vanishing
`H^1(L_k) = 0`, equivalently the cokernel-vanishing half of `index = k`; the
duality identification itself is not formalized here. The proof is the clash
between Parseval/Riemann-Lebesgue coefficient decay and the negative-degree
automorphy growth recursion. -/
theorem holSectionNeg_eq_bot (k : ℕ) [NeZero k] : holSectionNeg k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  apply eq_zero_of_holCoeff_eq_zero hf.1 hf.2.1
  exact holCoeffNeg_eq_zero hf

/-- The space of holomorphic sections of the degree-`-k` line bundle has dimension zero for
`k > 0`; this is the cokernel-vanishing half of the index computation. -/
theorem holSectionNeg_finrank_eq_zero (k : ℕ) [NeZero k] :
    Module.finrank ℂ (holSectionNeg k) = 0 := by
  rw [holSectionNeg_eq_bot k]
  exact finrank_bot ℂ (ℂ → ℂ)

end

end SpectralTriples
