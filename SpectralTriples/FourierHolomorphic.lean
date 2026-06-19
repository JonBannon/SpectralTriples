/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral

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

end SpectralTriples
