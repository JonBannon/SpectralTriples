/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Jon Bannon
-/

module

public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The Hermite functions and the weighted `L²` inner product

Foundations for **Route B** of the `T²` operator-index bridge
(`docs/INDEX_PAIRING.md`): the Landau/Hermite decomposition needs the Hermite
functions `hₙ(x) = cₙ · Hₙ(x) · e^{-x²/2}` to form an orthonormal basis of
`L²(ℝ)`. Mathlib has the probabilists' Hermite *polynomials* `Polynomial.hermite`
and the Rodrigues identity `deriv_gaussian_eq_hermite_mul_gaussian`, but neither
the Gaussian-weighted **orthogonality** nor the `L²` basis. This file builds the
orthogonality layer.

The load-bearing fact is the Gaussian-weighted orthogonality
`∫ Hₘ(x) Hₙ(x) e^{-x²/2} dx = n! √(2π) · δₘₙ`. The proof avoids `n`-fold
integration by parts: from `(Hₙ·w)' = -Hₙ₊₁·w` (Rodrigues, with `w = e^{-x²/2}`)
and a single integration by parts on `ℝ` one gets the recursion
`⟨P, Hₙ₊₁⟩ = ⟨P', Hₙ⟩` for the weighted pairing of a polynomial `P` against `Hₙ`,
whence `deg P ≤ n ⟹ ⟨P, Hₙ₊₁⟩ = 0`, i.e. off-diagonal orthogonality; the
diagonal value comes from the derivative identity `Hₙ' = n · Hₙ₋₁`.

## Main results

* `Polynomial.derivative_hermite`: `Hₙ₊₁' = (n+1) · Hₙ` (probabilists' identity).
-/

@[expose] public section

namespace Polynomial

open Polynomial

/-- The probabilists' Hermite differentiation identity `Hₙ₊₁' = (n+1) · Hₙ`.

(Mathlib has the three-term recursion `hermite_succ` but not this derivative form.) -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite (n + 1)) = ((n : ℤ) + 1) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : derivative ((((n : ℤ) + 1)) • hermite n) = ((n : ℤ) + 1) • derivative (hermite n) :=
      map_smul derivative _ _
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, h2,
      hermite_succ n]
    push_cast
    ring
end Polynomial
