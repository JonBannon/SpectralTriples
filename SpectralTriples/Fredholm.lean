/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-! # Fredholm operators

A minimal, self-contained notion of Fredholm linear map, scoped to exactly what the index
pairing of Chapter~2 of the blueprint needs.

There is ongoing work towards a general theory of Fredholm operators on topological vector
spaces in Mathlib (`leanprover-community/mathlib4#39274`), but as of this writing that branch
is unmerged, depends on other unmerged PRs, and contains unfinished (`sorry`) proofs, so it is
not yet usable here. The definitions below are deliberately minimal — stated for plain linear
maps `E →ₗ[𝕜] F` rather than continuous linear maps, so that they apply uniformly to bounded
operators (via `ContinuousLinearMap.toLinearMap`) and to the restriction of an unbounded
operator to its domain (via `LinearPMap.toFun`), as needed for chiral Dirac operators. The
naming (`IsFredholm`, `index`) is chosen to match the anticipated Mathlib API, so that this
file can be replaced by an `import` once the upstream theory lands.

## Main definitions

* `SpectralTriples.Fredholm.IsFredholm`: `f` has finite-dimensional kernel, closed range, and
  finite-dimensional cokernel.
* `SpectralTriples.Fredholm.index`: the integer `dim (ker f) - dim (F ⧸ range f)`.

## Main results

* `SpectralTriples.Fredholm.index_of_bijective`: a bijective linear map has index `0`.
-/

@[expose] public section

namespace SpectralTriples.Fredholm

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A linear map `f : E →ₗ[𝕜] F` is *Fredholm* if its kernel is finite-dimensional, its range
is closed, and its range has finite codimension (the cokernel `F ⧸ range f` is
finite-dimensional). -/
structure IsFredholm (f : E →ₗ[𝕜] F) : Prop where
  finiteDimensional_ker : FiniteDimensional 𝕜 (LinearMap.ker f)
  isClosed_range : IsClosed (LinearMap.range f : Set F)
  finiteDimensional_coker : FiniteDimensional 𝕜 (F ⧸ LinearMap.range f)

/-- The **Fredholm index** of a linear map `f : E →ₗ[𝕜] F`: the integer
`dim (ker f) - dim (F ⧸ range f)`. When `f` is not Fredholm and the relevant spaces are
infinite-dimensional, `Module.finrank` returns the junk value `0`, so `index f` silently
defaults accordingly — the same convention used by `SpectralTriples.index`. -/
noncomputable def index (f : E →ₗ[𝕜] F) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker f) : ℤ) - (Module.finrank 𝕜 (F ⧸ LinearMap.range f) : ℤ)

omit [TopologicalSpace E] in
/-- A bijective linear map with closed range is Fredholm. -/
theorem isFredholm_of_bijective {f : E →ₗ[𝕜] F} (hf : Function.Bijective f)
    (hrange : IsClosed (LinearMap.range f : Set F)) : IsFredholm f where
  finiteDimensional_ker := by
    rw [LinearMap.ker_eq_bot.mpr hf.1]; infer_instance
  isClosed_range := hrange
  finiteDimensional_coker := by
    haveI : Subsingleton (F ⧸ (⊤ : Submodule 𝕜 F)) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [LinearMap.range_eq_top.mpr hf.2]; infer_instance

omit [TopologicalSpace E] [TopologicalSpace F] in
/-- A bijective linear map has Fredholm index `0`. -/
theorem index_of_bijective {f : E →ₗ[𝕜] F} (hf : Function.Bijective f) : index f = 0 := by
  unfold index
  rw [LinearMap.ker_eq_bot.mpr hf.1, LinearMap.range_eq_top.mpr hf.2, finrank_bot]
  haveI : Subsingleton (F ⧸ (⊤ : Submodule 𝕜 F)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  rw [Module.finrank_zero_of_subsingleton]
  simp

end SpectralTriples.Fredholm
