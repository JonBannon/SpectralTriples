/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Theta sections on the square torus

This file proves the lower-bound half of the square-torus flux-`k` Landau-level computation:
the `k` explicit degree-`k` theta sections are linearly independent.  Equivalently, these
sections give `dim ker D+ >= k` for the degree-`k` line bundle on
`ℂ / (ℤ + iℤ)`.

The standard theta sections are built from Mathlib's two-variable `jacobiTheta₂` at
`τ = k * i`.  They satisfy the same degree-`k` automorphy factors and diagonalize translation
by `1 / k`; the distinct `k`th roots of unity then give linear independence.

The matching upper bound `dim ker D+ <= k` and the coker-vanishing/completeness part are
deferred; see `docs/INDEX_PAIRING.md`.
-/

@[expose] public section

open Complex Real

namespace SpectralTriples.ThetaSections

noncomputable section

/-- The primitive `k`th root of unity used by translation through `1 / k`. -/
def omega (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (k : ℂ))

/-- The `a`th explicit degree-`k` theta section on the square torus. -/
def thetaSection (k : ℕ) (a : Fin k) : ℂ → ℂ :=
  fun z =>
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * z) *
      jacobiTheta₂ ((k : ℂ) * z + (a : ℂ) * Complex.I) ((k : ℂ) * Complex.I)

/-- The modulus `τ = k * i` lies in the upper half-plane when `k ≠ 0`. -/
private theorem tau_im_pos (k : ℕ) [NeZero k] :
    (0 : ℝ) < (((k : ℂ) * Complex.I).im) := by
  simpa using
    (Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr (NeZero.ne k)) :
      (0 : ℝ) < (k : ℝ))

/-- `jacobiTheta₂` is periodic under natural integer shifts in its first variable. -/
private theorem jacobiTheta₂_add_nat_left (z τ : ℂ) (n : ℕ) :
    jacobiTheta₂ (z + (n : ℂ)) τ = jacobiTheta₂ z τ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have harg : z + (Nat.succ n : ℂ) = (z + (n : ℂ)) + 1 := by
        norm_num
        ring
      calc
        jacobiTheta₂ (z + (Nat.succ n : ℂ)) τ
            = jacobiTheta₂ ((z + (n : ℂ)) + 1) τ := by rw [harg]
        _ = jacobiTheta₂ (z + (n : ℂ)) τ := jacobiTheta₂_add_left _ _
        _ = jacobiTheta₂ z τ := ih

/-- The theta summands at `z = a * i`, `τ = k * i` have nonnegative real part. -/
private theorem thetaTerm_re_nonneg (k : ℕ) [NeZero k] (a : Fin k) (n : ℤ) :
    0 ≤ (jacobiTheta₂_term n ((a : ℂ) * Complex.I) ((k : ℂ) * Complex.I)).re := by
  rw [jacobiTheta₂_term, Complex.exp_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
    Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im,
    zero_mul, add_zero, Complex.I_im, mul_one, sub_self, Complex.intCast_re,
    Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, zero_add, zero_sub,
    Complex.add_im, neg_mul]
  have hsqre : ((n : ℂ) ^ 2).re = (n : ℝ) ^ 2 := by
    norm_num [sq]
  have hsqim : ((n : ℂ) ^ 2).im = 0 := by
    norm_num [sq]
  rw [hsqre, hsqim]
  simp only [mul_zero]
  simp only [zero_mul]
  norm_num
  positivity

/-- The zero-index theta summand at `z = a * i`, `τ = k * i` has real part `1`. -/
private theorem thetaTerm_zero_re (k : ℕ) [NeZero k] (a : Fin k) :
    (jacobiTheta₂_term 0 ((a : ℂ) * Complex.I) ((k : ℂ) * Complex.I)).re = 1 := by
  simp [jacobiTheta₂_term]

/-- At `z = a * i`, `τ = k * i`, the theta value has real part at least `1`. -/
private theorem jacobiTheta₂_eval_re_ge_one (k : ℕ) [NeZero k] (a : Fin k) :
    1 ≤ (jacobiTheta₂ ((a : ℂ) * Complex.I) ((k : ℂ) * Complex.I)).re := by
  have hsumC := hasSum_jacobiTheta₂_term ((a : ℂ) * Complex.I) (tau_im_pos k)
  have hsumR := Complex.hasSum_re hsumC
  have hle := le_hasSum hsumR (0 : ℤ) (fun n _hn => thetaTerm_re_nonneg k a n)
  rwa [thetaTerm_zero_re k a] at hle

/-- Each theta section is holomorphic as a function of `z`. -/
theorem differentiable_thetaSection (k : ℕ) [NeZero k] (a : Fin k) :
    Differentiable ℂ (thetaSection k a) := by
  intro z
  unfold thetaSection
  have h_exp :
      DifferentiableAt ℂ
        (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * z)) z := by
    fun_prop
  have h_aff :
      DifferentiableAt ℂ (fun z : ℂ => (k : ℂ) * z + (a : ℂ) * Complex.I) z := by
    fun_prop
  have h_theta :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          jacobiTheta₂ ((k : ℂ) * z + (a : ℂ) * Complex.I) ((k : ℂ) * Complex.I)) z := by
    simpa [Function.comp_def] using
      (differentiableAt_jacobiTheta₂_fst
        ((k : ℂ) * z + (a : ℂ) * Complex.I) (tau_im_pos k)).comp z h_aff
  exact h_exp.mul h_theta

/-- The theta sections are periodic under the square-torus lattice generator `1`. -/
theorem thetaSection_periodic (k : ℕ) [NeZero k] (a : Fin k) (z : ℂ) :
    thetaSection k a (z + 1) = thetaSection k a z := by
  unfold thetaSection
  have hthetaArg :
      (k : ℂ) * (z + 1) + (a : ℂ) * Complex.I =
        ((k : ℂ) * z + (a : ℂ) * Complex.I) + (k : ℂ) := by
    ring
  have hprefArg :
      2 * Real.pi * Complex.I * (a : ℂ) * (z + 1) =
        2 * Real.pi * Complex.I * (a : ℂ) * z +
          (a : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [hthetaArg, jacobiTheta₂_add_nat_left]
  rw [hprefArg, Complex.exp_add]
  have hexp : Complex.exp ((a : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_nat_mul_two_pi_mul_I (a : ℕ)
  rw [hexp]
  ring

/-- The theta sections have the degree-`k` automorphy factor under the lattice generator `i`. -/
theorem thetaSection_quasiPeriodic (k : ℕ) [NeZero k] (a : Fin k) (z : ℂ) :
    thetaSection k a (z + Complex.I) =
      Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) *
        thetaSection k a z := by
  unfold thetaSection
  have hthetaArg :
      (k : ℂ) * (z + Complex.I) + (a : ℂ) * Complex.I =
        ((k : ℂ) * z + (a : ℂ) * Complex.I) + (k : ℂ) * Complex.I := by
    ring
  rw [hthetaArg, jacobiTheta₂_add_left']
  have hfactor :
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (z + Complex.I)) *
          Complex.exp
            (-Real.pi * Complex.I *
              ((k : ℂ) * Complex.I + 2 * ((k : ℂ) * z + (a : ℂ) * Complex.I))) =
        Complex.exp (-Real.pi * Complex.I * (k : ℂ) * (2 * z + Complex.I)) *
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * z) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring_nf
  rw [← mul_assoc, hfactor]
  ring

/-- Translation by `1 / k` diagonalizes the theta sections with eigenvalue `omega k ^ a`. -/
theorem thetaSection_translate (k : ℕ) [NeZero k] (a : Fin k) (z : ℂ) :
    thetaSection k a (z + (1 : ℂ) / (k : ℂ)) =
      omega k ^ (a : ℕ) * thetaSection k a z := by
  unfold thetaSection omega
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hthetaArg :
      (k : ℂ) * (z + (1 : ℂ) / (k : ℂ)) + (a : ℂ) * Complex.I =
        ((k : ℂ) * z + (a : ℂ) * Complex.I) + 1 := by
    field_simp [hk0]
    ring
  have hprefArg :
      2 * Real.pi * Complex.I * (a : ℂ) * (z + (1 : ℂ) / (k : ℂ)) =
        2 * Real.pi * Complex.I * (a : ℂ) * z +
          (a : ℂ) * (2 * Real.pi * Complex.I / (k : ℂ)) := by
    field_simp [hk0]
  rw [hthetaArg, jacobiTheta₂_add_left]
  rw [hprefArg, Complex.exp_add]
  have hpow :
      Complex.exp ((a : ℂ) * (2 * Real.pi * Complex.I / (k : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I / (k : ℂ)) ^ (a : ℕ) := by
    simpa using
      (Complex.exp_nat_mul (2 * Real.pi * Complex.I / (k : ℂ)) (a : ℕ))
  rw [hpow]
  ring

/-- No explicit theta section is the zero function. -/
theorem thetaSection_ne_zero (k : ℕ) [NeZero k] (a : Fin k) :
    thetaSection k a ≠ 0 := by
  intro hzero
  have hval : thetaSection k a 0 = 0 := by
    simpa using congrFun hzero 0
  have hre : 1 ≤ (thetaSection k a 0).re := by
    simpa [thetaSection] using jacobiTheta₂_eval_re_ge_one k a
  have hre_zero : (thetaSection k a 0).re = 0 := by
    rw [hval]
    rfl
  linarith

/-- Translation through `1 / k` as a linear endomorphism of complex-valued functions. -/
def translationEnd (k : ℕ) : Module.End ℂ (ℂ → ℂ) where
  toFun := fun f z => f (z + (1 : ℂ) / (k : ℂ))
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- The eigenvalues `omega k ^ a`, `a : Fin k`, are pairwise distinct. -/
theorem omega_powers_injective (k : ℕ) [NeZero k] :
    Function.Injective fun a : Fin k => omega k ^ (a : ℕ) := by
  intro a b h
  apply Fin.ext
  have hprim : IsPrimitiveRoot (omega k) k := by
    simpa [omega] using Complex.isPrimitiveRoot_exp k (NeZero.ne k)
  exact hprim.pow_inj a.isLt b.isLt h

/-- The `k` explicit theta sections are linearly independent over `ℂ`. -/
theorem thetaSection_linearIndependent (k : ℕ) [NeZero k] :
    LinearIndependent ℂ (thetaSection k) := by
  refine Module.End.eigenvectors_linearIndependent' (translationEnd k)
    (fun a : Fin k => omega k ^ (a : ℕ)) (omega_powers_injective k)
    (thetaSection k) ?_
  intro a
  refine ⟨?_, thetaSection_ne_zero k a⟩
  rw [Module.End.mem_eigenspace_iff]
  funext z
  exact thetaSection_translate k a z

end

end SpectralTriples.ThetaSections
