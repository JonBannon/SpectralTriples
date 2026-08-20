/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

module

public import Mathlib.LinearAlgebra.LinearPMap

/-! # Resolvents of partially defined linear maps

This file adapts a portion of mathlib4 PR #29624
(`https://github.com/leanprover-community/mathlib4/pull/29624`), specialized to
endomorphisms `f : E →ₗ.[R] E`, to define the resolvent set and resolvent of a
`LinearPMap`. This is the algebraic groundwork for the compact-resolvent axiom of a
spectral triple. Quantitative finite (`p`-)summability requires additional decay data.

## Main definitions

* `LinearPMap.inverseAsLinearMap`: the inverse of a bijective `LinearPMap`, packaged as an
  (everywhere-defined) `LinearMap`.
* `LinearPMap.resolventSet`: the set of `z` for which `z • 1 - f` is bijective.
* `LinearPMap.resolvent`: the resolvent `(z • 1 - f)⁻¹` of `f` at `z ∈ f.resolventSet`.

-/

@[expose] public section

namespace LinearPMap

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

section bijective

variable {f : E →ₗ.[R] E}

theorem inverse_domain_eq_top_of_bijective (hf : Function.Bijective f) :
    f.inverse.domain = ⊤ := by
  rw [inverse_domain, LinearMap.range_eq_top]
  exact hf.2

/-- If `f` is bijective, its inverse is defined on all of `E`; package it as a
(globally defined) `LinearMap`. -/
noncomputable def inverseAsLinearMap (hf : Function.Bijective f) : E →ₗ[R] E :=
  f.inverse.toFun.comp (LinearEquiv.ofTop f.inverse.domain
    (inverse_domain_eq_top_of_bijective hf)).symm.toLinearMap

theorem inverseAsLinearMap_eq (hf : Function.Bijective f) :
    f.inverseAsLinearMap hf = f.inverse.toFun.comp (LinearEquiv.ofTop f.inverse.domain
      (inverse_domain_eq_top_of_bijective hf)).symm.toLinearMap :=
  rfl

theorem mem_inverse_domain_of_bijective (hf : Function.Bijective f) (y : E) :
    y ∈ f.inverse.domain := by
  rw [inverse_domain_eq_top_of_bijective hf]
  exact Submodule.mem_top

theorem inverseAsLinearMap_apply_eq_inverse_apply (hf : Function.Bijective f) {y : E} :
    f.inverseAsLinearMap hf y = f.inverse ⟨y, mem_inverse_domain_of_bijective hf y⟩ := by
  simp only [inverseAsLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    toFun_eq_coe]
  congr

theorem inverseAsLinearMap_range (hf : Function.Bijective f) :
    (f.inverseAsLinearMap hf).range = f.domain := by
  simp [inverseAsLinearMap_eq hf, inverse_range (LinearMap.ker_eq_bot.mpr hf.1)]

theorem inverseAsLinearMap_apply_mem_domain (hf : Function.Bijective f) (x : E) :
    f.inverseAsLinearMap hf x ∈ f.domain := by
  rw [← inverseAsLinearMap_range hf]
  exact (f.inverseAsLinearMap hf).mem_range_self x

theorem graph_eq_inverse_graph_prodComm (hf : f.toFun.ker = ⊥) :
    f.graph = f.inverse.graph.map (LinearEquiv.prodComm R E E : (E × E) →ₗ[R] (E × E)) := by
  rw [inverse_graph hf]
  ext x
  simp

theorem mem_graph_of_inverse (hf : f.toFun.ker = ⊥) (y : f.inverse.domain) :
    (f.inverse y, (y : E)) ∈ f.graph := by
  simp [graph_eq_inverse_graph_prodComm hf]

theorem mem_graph_of_inverseAsLinearMap (hf : Function.Bijective f) (y : E) :
    (f.inverseAsLinearMap hf y, y) ∈ f.graph := by
  rw [inverseAsLinearMap_apply_eq_inverse_apply hf]
  exact mem_graph_of_inverse (LinearMap.ker_eq_bot.mpr hf.1) _

/-- Applying `f` to the inverse of `x` (computed via `inverseAsLinearMap`) returns `x`. -/
theorem inverse_apply_apply_cancel (hf : Function.Bijective f) (x : E) :
    f ⟨f.inverseAsLinearMap hf x, inverseAsLinearMap_apply_mem_domain hf x⟩ = x := by
  apply ((image_iff (inverseAsLinearMap_apply_mem_domain hf x)).mpr ?_).symm
  exact mem_graph_of_inverseAsLinearMap hf _

/-- The inverse of `f x` (computed via `inverseAsLinearMap`) returns `x`. -/
theorem apply_inverseAsLinearMap_apply_cancel (hf : Function.Bijective f) (x' : f.domain) :
    f.inverseAsLinearMap hf (f x') = x' := by
  have hmem : (f x', (x' : E)) ∈ f.inverse.graph := by
    rw [inverse_graph (LinearMap.ker_eq_bot.mpr hf.1)]
    simp
  rw [← image_iff (mem_inverse_domain_of_bijective hf _)] at hmem
  rw [hmem]
  exact inverseAsLinearMap_apply_eq_inverse_apply hf

end bijective

section resolvent

variable [SMulCommClass R R E] (f : E →ₗ.[R] E)

/-- The resolvent set of a `LinearPMap` `f`: the set of `z` for which `z • 1 - f` is
bijective (as a `LinearPMap` with domain `f.domain`).

This definition only agrees with the conventional one when `f` is closed; if it is not,
the conventional definition would give `resolventSet f = ∅`, but this definition can still
be nonempty. We use this definition for convenience and since it makes fewer assumptions. -/
def resolventSet : Set R :=
  { z | Function.Bijective ((z • (LinearMap.id (R := R) (M := E))) +ᵥ (-f) : E →ₗ.[R] E) }

open Classical in
/-- The resolvent of `f` at `z ∈ f.resolventSet`, as a (globally defined) `LinearMap`. -/
noncomputable def resolvent (z : R) : E →ₗ[R] E :=
  if hz : z ∈ f.resolventSet then
    ((z • LinearMap.id) +ᵥ (-f) : E →ₗ.[R] E).inverseAsLinearMap hz
  else 0

theorem resolvent_apply_eq {z : R} (hz : z ∈ f.resolventSet) :
    f.resolvent z = ((z • LinearMap.id) +ᵥ (-f) : E →ₗ.[R] E).inverseAsLinearMap hz := by
  simp [resolvent, hz]

/-- The range of the resolvent of `f` at `z ∈ f.resolventSet` is the domain of `f`. -/
theorem range_resolvent {z : R} (hz : z ∈ f.resolventSet) :
    (f.resolvent z).range = f.domain := by
  simp [resolvent, hz, inverseAsLinearMap_range hz]

end resolvent

end LinearPMap
