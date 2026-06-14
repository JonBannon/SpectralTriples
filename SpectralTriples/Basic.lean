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

open ContinuousLinearMap LinearMap in
structure IsOddSpectralTriple (A : Type*) {H : Type*} {𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (hD : IsSelfAdjoint D) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) where
  dom_comp (a : A) (x : D.domain) : π a x ∈ D.domain
  comm (a : A) : iSup fun (x : Metric.closedBall (0 : D.domain) 1) ↦
    ‖(π a) (D x) - (D ⟨(π a x), dom_comp a x⟩)‖ₑ < ∞

open ContinuousLinearMap LinearMap in
structure IsEvenSpectralTriple (A : Type*) {H : Type*} {𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (hD : IsSelfAdjoint D) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) (γ : H →L[𝕜] H)
    (hγS : IsSelfAdjoint γ) (hγU : γ ∈ unitary (H →L[𝕜] H))
    extends IsOddSpectralTriple A D hD π where
  grading_comm (a : A) : γ.comp (π a) = (π a).comp γ
  grading_dom (x : D.domain) : γ x ∈ D.domain
  grading (x : D.domain) : D ⟨γ x, grading_dom x⟩ = - γ (D x)
