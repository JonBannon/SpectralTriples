/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Order.CompletePartialOrder

/-! # Core axioms for odd and even spectral triples

This file packages the self-adjointness, domain-invariance, bounded-commutator, and grading
axioms. The predicates deliberately do **not** include compact resolvent; the standard
spectral-triple definition is completed by `IsCompactResolventSpectralTriple` in
`CompactResolvent.lean`. Thus `IsOddSpectralTriple` and `IsEvenSpectralTriple` should be read
as reusable spectral-triple cores, not as a claim that compactness or `p`-summability holds.

## Main definitions

* `IsOddSpectralTriple`
* `IsEvenSpectralTriple`
* `IsOddSpectralTriple.boundedCommutator`: the canonical bounded extension of the domain
  commutator.

-/

@[expose] public section

open LinearPMap StarAlgebra ENNReal

open ContinuousLinearMap LinearMap in
/-- The core odd spectral-triple axioms: self-adjoint `D`, invariance of `dom D` under the
representation, and a finite unit-ball bound for each commutator. Compact resolvent is supplied
separately by `IsCompactResolventSpectralTriple`. -/
structure IsOddSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) where
  self_adjoint : IsSelfAdjoint D
  dom_comp (a : A) (x : D.domain) : π a x ∈ D.domain
  comm (a : A) : (iSup fun (x : Metric.closedBall (0 : D.domain) 1) ↦
    ‖(π a) (D x) - (D ⟨(π a x), dom_comp a x⟩)‖ₑ) < ∞

open ContinuousLinearMap LinearMap in
/-- The core even spectral-triple axioms: an odd core together with a self-adjoint involutive
grading commuting with the representation and anticommuting with `D`. -/
structure IsEvenSpectralTriple (A : Type*) {H 𝕜 : Type*} [RCLike 𝕜] [Semiring A]
    [StarRing A] [Algebra 𝕜 A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →ₗ.[𝕜] H) (π : StarAlgHom 𝕜 A (H →L[𝕜] H)) (γ : H →L[𝕜] H)
    extends IsOddSpectralTriple A D π where
  self_adjoint_grading : IsSelfAdjoint γ
  grading_sq : γ * γ = 1
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

/-- The representation restricted to the invariant Dirac domain. -/
noncomputable def domainRepresentation (hT : IsOddSpectralTriple A D π) (a : A) :
    D.domain →ₗ[𝕜] D.domain where
  toFun x := ⟨π a x, hT.dom_comp a x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (π a) (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (π a) c (x : H)

/-- The conventional algebraic commutator `[D, π(a)]` on `dom D`. It becomes an everywhere-defined
continuous linear map through `boundedCommutator`. -/
noncomputable def commutatorOnDomain (hT : IsOddSpectralTriple A D π) (a : A) :
    D.domain →ₗ[𝕜] H :=
  D.toFun.comp (hT.domainRepresentation a) - (π a).toLinearMap.comp D.toFun

@[simp] theorem commutatorOnDomain_apply (hT : IsOddSpectralTriple A D π) (a : A)
    (x : D.domain) :
    hT.commutatorOnDomain a x = D ⟨π a x, hT.dom_comp a x⟩ - π a (D x) :=
  rfl

open ContinuousLinearMap LinearMap in
/-- The structure field writes the negative commutator `[π(a), D]`; its finite `ℝ≥0∞`
supremum gives the same unit-ball bound for the conventional `[D, π(a)]`. -/
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

/-- The unit-ball axiom gives the homogeneous bound needed to extend the commutator from the
dense Dirac domain. -/
theorem exists_commutator_bound (hT : IsOddSpectralTriple A D π) (a : A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : D.domain,
      ‖hT.commutatorOnDomain a x‖ ≤ C * ‖(x : H)‖ := by
  obtain ⟨C, hC⟩ := hT.exists_comm_bound a
  let C' := max C 0
  refine ⟨C', le_max_right C 0, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    simp [commutatorOnDomain]
  have hxcoe : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxnorm : ‖(x : H)‖ ≠ 0 := norm_ne_zero_iff.mpr hxcoe
  let y : D.domain := (‖(x : H)‖⁻¹ : 𝕜) • x
  have hy : ‖(y : H)‖ ≤ 1 := by
    change ‖(‖(x : H)‖⁻¹ : 𝕜) • (x : H)‖ ≤ 1
    calc
      ‖(‖(x : H)‖⁻¹ : 𝕜) • (x : H)‖ = ‖(x : H)‖⁻¹ * ‖(x : H)‖ := by
        rw [norm_smul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ = 1 := inv_mul_cancel₀ hxnorm
      _ ≤ 1 := le_rfl
  have hscaled : ‖(x : H)‖⁻¹ * ‖hT.commutatorOnDomain a x‖ ≤ C' := by
    have hunit := hC y hy
    have hunit' : ‖hT.commutatorOnDomain a y‖ ≤ C := by
      simpa only [commutatorOnDomain_apply, norm_sub_rev] using hunit
    calc
      ‖(x : H)‖⁻¹ * ‖hT.commutatorOnDomain a x‖ =
          ‖hT.commutatorOnDomain a y‖ := by
        rw [show y = (‖(x : H)‖⁻¹ : 𝕜) • x from rfl,
          LinearMap.map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ C := hunit'
      _ ≤ C' := le_max_left C 0
  calc
    ‖hT.commutatorOnDomain a x‖ =
        ‖(x : H)‖ * (‖(x : H)‖⁻¹ * ‖hT.commutatorOnDomain a x‖) := by
      symm
      rw [← mul_assoc, mul_inv_cancel₀ hxnorm, one_mul]
    _ ≤ ‖(x : H)‖ * C' :=
      mul_le_mul_of_nonneg_left hscaled (norm_nonneg _)
    _ = C' * ‖(x : H)‖ := mul_comm _ _

/-- The bounded extension of `[D, π(a)]` from the dense Dirac domain to all of `H`. -/
noncomputable def boundedCommutator (hT : IsOddSpectralTriple A D π) (a : A) : H →L[𝕜] H :=
  (hT.commutatorOnDomain a).extendOfNorm D.domain.subtype

/-- On `dom D`, the bounded extension agrees with the algebraic commutator. -/
theorem boundedCommutator_apply (hT : IsOddSpectralTriple A D π) (a : A) (x : D.domain) :
    hT.boundedCommutator a (x : H) =
      D ⟨π a x, hT.dom_comp a x⟩ - π a (D x) := by
  obtain ⟨C, _hCnonneg, hC⟩ := hT.exists_commutator_bound a
  change (hT.commutatorOnDomain a).extendOfNorm D.domain.subtype
      (D.domain.subtype x) = hT.commutatorOnDomain a x
  exact LinearMap.extendOfNorm_eq hT.dense_domain_dirac.denseRange_val ⟨C, hC⟩ x

/-- The bounded commutator is the unique continuous linear extension of the domain
commutator. -/
theorem boundedCommutator_unique (hT : IsOddSpectralTriple A D π) (a : A)
    (T : H →L[𝕜] H)
    (hT_apply : ∀ x : D.domain,
      T (x : H) = D ⟨π a x, hT.dom_comp a x⟩ - π a (D x)) :
    hT.boundedCommutator a = T := by
  obtain ⟨C, _hCnonneg, hC⟩ := hT.exists_commutator_bound a
  apply LinearMap.extendOfNorm_unique hT.dense_domain_dirac.denseRange_val C hC
  ext x
  exact hT_apply x

end IsOddSpectralTriple

namespace IsEvenSpectralTriple

variable {A H 𝕜 : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {D : H →ₗ.[𝕜] H} {π : StarAlgHom 𝕜 A (H →L[𝕜] H)} {γ : H →L[𝕜] H}

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

/-- For a self-adjoint operator, membership in `unitary` is equivalent to squaring to the
identity. This provides the bridge between `grading_involutive` and the `unitary` API when
needed. -/
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
