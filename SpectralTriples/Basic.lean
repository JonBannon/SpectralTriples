/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Order.CompletePartialOrder

/-! # Spectral triples

In this file we formalize spectral triples.

## Main definitions

* OddSpectralTriple
* EvenSpectralTriple

-/

@[expose] public section

open LinearPMap StarAlgebra ENNReal


/-
Now that the following are `Prop`-valued, it may be possible to make them classes, since the data
are provided in each instance and we have proof-irrelevance.
-/

open ContinuousLinearMap LinearMap in
structure IsOddSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) where
  self_adjoint : IsSelfAdjoint D
  dom_comp (a : A) (x : D.domain) : π a x ∈ D.domain
  comm (a : A) : (iSup fun (x : Metric.closedBall (0 : D.domain) 1) ↦
    ‖(π a) (D x) - (D ⟨(π a x), dom_comp a x⟩)‖ₑ) < ∞

open ContinuousLinearMap LinearMap in
structure IsEvenSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) (γ : H →L[𝕜] H)
    extends IsOddSpectralTriple A D π where
  self_adjoint_grading : IsSelfAdjoint γ
  unitary_grading : γ ∈ unitary (H →L[𝕜] H)
  grading_comm (a : A) : γ.comp (π a) = (π a).comp γ
  grading_dom (x : D.domain) : γ x ∈ D.domain
  grading_anticomm (x : D.domain) : D ⟨γ x, grading_dom x⟩ = - γ (D x)

namespace IsOddSpectralTriple

variable {A H 𝕜 : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)}

/-- The domain of the Dirac operator of a spectral triple is dense. -/
theorem dense_domain_dirac (hT : IsOddSpectralTriple A D π) : Dense (D.domain : Set H) :=
  hT.self_adjoint.dense_domain

/-- The Dirac operator of a spectral triple is a closed operator. -/
theorem isClosed_dirac (hT : IsOddSpectralTriple A D π) : D.IsClosed :=
  hT.self_adjoint.isClosed

open ContinuousLinearMap LinearMap in
/-- The commutator `[D, π a]`, while only assumed to extend to a bounded operator via an
`ℝ≥0∞`-valued supremum, is in fact bounded on the closed unit ball of `D.domain` by a finite
real constant. -/
theorem exists_comm_bound (hT : IsOddSpectralTriple A D π) (a : A) :
    ∃ C : ℝ, ∀ x : D.domain, ‖(x : H)‖ ≤ 1 →
      ‖π a (D x) - D ⟨π a x, hT.dom_comp a x⟩‖ ≤ C := by
  refine ⟨(⨆ x : Metric.closedBall (0 : D.domain) 1,
      ‖π a (D (x : D.domain)) - D ⟨π a (x : D.domain), hT.dom_comp a x⟩‖ₑ).toReal,
    fun x hx => ?_⟩
  have hmem : x ∈ Metric.closedBall (0 : D.domain) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have h1 := le_iSup (fun y : Metric.closedBall (0 : D.domain) 1 =>
    ‖π a (D (y : D.domain)) - D ⟨π a (y : D.domain), hT.dom_comp a y⟩‖ₑ) ⟨x, hmem⟩
  have hne := (hT.comm a).ne
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hne,
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h1
  exact h1

end IsOddSpectralTriple

namespace IsEvenSpectralTriple

variable {A H 𝕜 : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)} {γ : H →L[𝕜] H}

/-- The grading operator of an even spectral triple squares to the identity. -/
theorem grading_sq (hT : IsEvenSpectralTriple A D π γ) : γ * γ = 1 := by
  have h := Unitary.mul_star_self_of_mem hT.unitary_grading
  rwa [hT.self_adjoint_grading.star_eq] at h

/-- The grading operator commutes with the image of `A` under `π`. -/
theorem grading_commute (hT : IsEvenSpectralTriple A D π γ) (a : A) :
    Commute γ (π a) :=
  hT.grading_comm a

/-- Conjugating the Dirac operator by the grading operator negates it on `D.domain`:
`γ D γ = -D`. -/
theorem grading_conj_dirac (hT : IsEvenSpectralTriple A D π γ) (x : D.domain) :
    γ (D ⟨γ x, hT.grading_dom x⟩) = - D x := by
  rw [hT.grading_anticomm x, _root_.map_neg, ← ContinuousLinearMap.mul_apply, hT.grading_sq,
    ContinuousLinearMap.one_apply]

/-- For a self-adjoint operator, being a unitary involution is equivalent to squaring to the
identity. Thus `unitary_grading` could equivalently be replaced by `γ * γ = 1`, given
`self_adjoint_grading`. -/
theorem mem_unitary_iff_sq_eq_one (hγ : IsSelfAdjoint γ) :
    γ ∈ unitary (H →L[𝕜] H) ↔ γ * γ = 1 := by
  rw [Unitary.mem_iff, hγ.star_eq, and_self]

/-- Every vector decomposes as a sum of a `+1`-eigenvector and a `-1`-eigenvector of the
grading operator `γ`. -/
theorem exists_grading_eigen_decomp (hT : IsEvenSpectralTriple A D π γ) (x : H) :
    ∃ y z : H, x = y + z ∧ γ y = y ∧ γ z = -z := by
  have hγγ : γ (γ x) = x := by
    rw [← ContinuousLinearMap.mul_apply, hT.grading_sq, ContinuousLinearMap.one_apply]
  refine ⟨(2⁻¹ : 𝕜) • (x + γ x), (2⁻¹ : 𝕜) • (x - γ x), ?_, ?_, ?_⟩
  · have h2 : (x + γ x) + (x - γ x) = (2 : 𝕜) • x := by
      rw [two_smul]; abel
    rw [← smul_add, h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  · rw [_root_.map_smul, _root_.map_add, hγγ, add_comm]
  · rw [_root_.map_smul, _root_.map_sub, hγγ, ← smul_neg, neg_sub]

end IsEvenSpectralTriple
