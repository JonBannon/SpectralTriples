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
* `Polynomial.integrable_aeval_mul_gaussian`: any polynomial times `e^{-x²/2}` is
  integrable on `ℝ`.
* `Polynomial.hermite_integral_eq_zero_of_ne` / `hermite_integral_self`: the
  off-diagonal vanishing and the diagonal value `n!·√(2π)`.
* `Polynomial.hermite_orthogonality`: `∫ Hₘ Hₙ e^{-x²/2} = n!·√(2π)·δₘₙ`.
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

noncomputable section

open MeasureTheory Real
open scoped Real

namespace Polynomial

private lemma hasDerivAt_gaussian_weight (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      (-x * Real.exp (-(x ^ 2 / 2))) x := by
  have hd : DifferentiableAt ℝ (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x := by
    fun_prop
  have hderiv : deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
      -x * Real.exp (-(x ^ 2 / 2)) := by
    rw [deriv_exp (by fun_prop)]
    simp [mul_comm]
  simpa [hderiv] using hd.hasDerivAt

private lemma hasDerivAt_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => aeval y (hermite n) * Real.exp (-(y ^ 2 / 2)))
      (-(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))) x := by
  have hp := (hermite n).hasDerivAt_aeval (R := ℤ) x
  have hw := hasDerivAt_gaussian_weight x
  convert hp.mul hw using 1
  · rw [hermite_succ]
    simp [sub_eq_add_neg, mul_assoc, mul_comm]
    ring

private lemma integrable_monomial_gaussian (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * Real.exp (-(x ^ 2 / 2)) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hn : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    linarith
  have h :
      Integrable fun x : ℝ =>
        x ^ (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    exact integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num) (s := (n : ℝ)) hs
  convert h using 1
  ext x
  rw [Real.rpow_natCast]
  ring_nf

/-- Any polynomial times the Gaussian weight `e^{-x²/2}` is integrable on `ℝ`. -/
theorem integrable_aeval_mul_gaussian (p : ℤ[X]) :
    Integrable fun x : ℝ => aeval x p * Real.exp (-(x ^ 2 / 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      ext x
      simp [add_mul]
  | monomial n c =>
      have h := (integrable_monomial_gaussian n).const_mul (c : ℝ)
      convert h using 1
      ext x
      simp [mul_assoc]

private lemma integrable_aeval_mul_aeval_mul_gaussian (p q : ℤ[X]) :
    Integrable fun x : ℝ =>
      aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2)) := by
  convert integrable_aeval_mul_gaussian (p * q) using 1
  ext x
  simp [mul_assoc]

private lemma hermite_integral_succ (p : ℤ[X]) (n : ℕ) :
    ∫ x : ℝ, aeval x p * aeval x (hermite (n + 1)) *
        Real.exp (-(x ^ 2 / 2)) =
      ∫ x : ℝ, aeval x (derivative p) * aeval x (hermite n) *
        Real.exp (-(x ^ 2 / 2)) := by
  let u : ℝ → ℝ := fun x => aeval x p
  let u' : ℝ → ℝ := fun x => aeval x (derivative p)
  let v : ℝ → ℝ := fun x => aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
  let v' : ℝ → ℝ :=
    fun x => -(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (u' := u') (v := v) (v' := v')
    (fun x _hx => by simpa [u, u'] using (p.hasDerivAt_aeval (R := ℤ) x))
    (fun x _hx => by simpa [v, v'] using hasDerivAt_hermite_mul_gaussian n x)
    (by
      dsimp [u, v']
      convert (integrable_aeval_mul_aeval_mul_gaussian p (hermite (n + 1))).neg using 1
      ext x
      simp [Pi.mul_apply, Pi.neg_apply, mul_assoc])
    (by
      dsimp [u', v]
      convert integrable_aeval_mul_aeval_mul_gaussian (derivative p) (hermite n) using 1
      ext x
      simp [Pi.mul_apply, mul_assoc])
    (by
      dsimp [u, v]
      convert integrable_aeval_mul_aeval_mul_gaussian p (hermite n) using 1
      ext x
      simp [Pi.mul_apply, mul_assoc])
  have h' :
      - (∫ x : ℝ, aeval x p * aeval x (hermite (n + 1)) *
          Real.exp (-(x ^ 2 / 2))) =
        - (∫ x : ℝ, aeval x (derivative p) * aeval x (hermite n) *
          Real.exp (-(x ^ 2 / 2))) := by
    simpa [u, u', v, v', mul_assoc, integral_neg, Pi.mul_apply, Pi.neg_apply] using h
  exact neg_injective h'

private lemma hermite_integral_eq_zero_of_natDegree_lt (p : ℤ[X]) :
    ∀ {n : ℕ}, p.natDegree < n →
      ∫ x : ℝ, aeval x p * aeval x (hermite n) *
        Real.exp (-(x ^ 2 / 2)) = 0 := by
  intro n
  induction n generalizing p with
  | zero =>
      intro hp
      exact (Nat.not_lt_zero _ hp).elim
  | succ n ih =>
      intro hp
      rw [hermite_integral_succ p n]
      by_cases hn : n = 0
      · subst n
        have hp0 : p.natDegree = 0 := by omega
        rw [derivative_of_natDegree_zero hp0]
        simp
      · exact ih (derivative p) (by
          have hle := natDegree_derivative_le p
          omega)

/-- **Off-diagonal orthogonality.** For `m ≠ n`, `∫ Hₘ Hₙ e^{-x²/2} = 0`. -/
theorem hermite_integral_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) *
      Real.exp (-(x ^ 2 / 2)) = 0 := by
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · exact hermite_integral_eq_zero_of_natDegree_lt (hermite m) (by simpa using hlt)
  · have hsym :
        (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) *
          Real.exp (-(x ^ 2 / 2))) =
          ∫ x : ℝ, aeval x (hermite n) * aeval x (hermite m) *
            Real.exp (-(x ^ 2 / 2)) := by
        congr with x
        ring
    rw [hsym]
    exact hermite_integral_eq_zero_of_natDegree_lt (hermite n) (by simpa using hgt)

private lemma hermite_integral_self_succ (n : ℕ) :
    (∫ x : ℝ, aeval x (hermite (n + 1)) * aeval x (hermite (n + 1)) *
        Real.exp (-(x ^ 2 / 2))) =
      ((n : ℝ) + 1) *
        ∫ x : ℝ, aeval x (hermite n) * aeval x (hermite n) *
          Real.exp (-(x ^ 2 / 2)) := by
  calc
    (∫ x : ℝ, aeval x (hermite (n + 1)) * aeval x (hermite (n + 1)) *
        Real.exp (-(x ^ 2 / 2)))
        = ∫ x : ℝ, aeval x (derivative (hermite (n + 1))) *
            aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
          exact hermite_integral_succ (hermite (n + 1)) n
    _ = ∫ x : ℝ, ((n : ℝ) + 1) *
          (aeval x (hermite n) * aeval x (hermite n) *
            Real.exp (-(x ^ 2 / 2))) := by
          congr with x
          rw [derivative_hermite]
          simp
          ring
    _ = ((n : ℝ) + 1) *
        ∫ x : ℝ, aeval x (hermite n) * aeval x (hermite n) *
          Real.exp (-(x ^ 2 / 2)) := by
          rw [integral_const_mul]

private lemma hermite_integral_self_zero :
    (∫ x : ℝ, aeval x (hermite 0) * aeval x (hermite 0) *
        Real.exp (-(x ^ 2 / 2))) =
      Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, aeval x (hermite 0) * aeval x (hermite 0) *
        Real.exp (-(x ^ 2 / 2)))
        = ∫ x : ℝ, Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
          congr with x
          simp
          ring_nf
    _ = Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
          exact integral_gaussian (1 / 2 : ℝ)
    _ = Real.sqrt (2 * Real.pi) := by
          congr 1
          ring

/-- **Diagonal value.** `∫ Hₙ Hₙ e^{-x²/2} = n!·√(2π)`. -/
theorem hermite_integral_self (n : ℕ) :
    (∫ x : ℝ, aeval x (hermite n) * aeval x (hermite n) *
        Real.exp (-(x ^ 2 / 2))) =
      (n.factorial : ℝ) * Real.sqrt (2 * Real.pi) := by
  induction n with
  | zero =>
      simpa using hermite_integral_self_zero
  | succ n ih =>
      rw [hermite_integral_self_succ n, ih]
      simp [Nat.factorial_succ]
      ring

/-- Gaussian-weighted orthogonality of the probabilists' Hermite polynomials. -/
theorem hermite_orthogonality (m n : Nat) :
    ∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) *
        Real.exp (-(x ^ 2 / 2)) =
      if m = n then (n.factorial : ℝ) * Real.sqrt (2 * Real.pi) else 0 := by
  by_cases hmn : m = n
  · subst m
    simp [hermite_integral_self]
  · simp [hmn, hermite_integral_eq_zero_of_ne hmn]

end Polynomial
