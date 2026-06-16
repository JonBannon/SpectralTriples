/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable

/-! # The basic criterion of self-adjointness

For a self-adjoint operator `D` and `z : 𝕜` with `Im z ≠ 0`, the operator `z • 1 - D` is
bijective on `D.domain`, i.e. `z ∈ D.resolventSet`. This upgrades the injectivity of
`IsSelfAdjoint.injective_resolvent_apply` to bijectivity, and in particular gives `i ∈ ρ(D)`.

## Main results

* `IsSelfAdjoint.range_subDirac_orthogonal_eq_bot`: the range of `z • 1 - D` is dense
  (its orthogonal complement is trivial), via the adjoint.
* `IsSelfAdjoint.isClosed_range_subDirac`: the range of `z • 1 - D` is closed, via the
  bounded-below estimate and closedness of `D`.
* `IsSelfAdjoint.mem_resolventSet`: consequently `z ∈ D.resolventSet` when `Im z ≠ 0`.
-/

@[expose] public section

open LinearPMap

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]

namespace IsSelfAdjoint

variable {D : H →ₗ.[𝕜] H}

/-- The operator `z • 1 - D`, restricted to `D.domain`, packaged as a linear map into `H`. -/
noncomputable def subDirac (D : H →ₗ.[𝕜] H) (z : 𝕜) : D.domain →ₗ[𝕜] H :=
  z • D.domain.subtype - D.toFun

omit [CompleteSpace H] in
@[simp] theorem subDirac_apply (z : 𝕜) (x : D.domain) :
    subDirac D z x = z • (x : H) - D x := rfl

/-- The restriction `z • 1 - D` is injective on `D.domain` when `Im z ≠ 0`. -/
theorem injective_subDirac (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Function.Injective (subDirac D z) := by
  simpa only [subDirac_apply] using hD.injective_resolvent_apply hz

/-- The range of `z • 1 - D` is dense (orthogonal complement trivial) when `Im z ≠ 0`:
if `y ⊥ range(z • 1 - D)` then `D y = conj z • y`, forcing `Im z · ‖y‖² = 0`, hence `y = 0`. -/
theorem range_subDirac_orthogonal_eq_bot (hD : IsSelfAdjoint D) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    (LinearMap.range (subDirac D z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hadj : D† = D := isSelfAdjoint_def.mp hD
  -- `y ⊥ range` gives `⟪z • x - D x, y⟫ = 0`, i.e. `⟪conj z • y, x⟫ = ⟪y, D x⟫` on `D.domain`.
  have hortho : ∀ x : D.domain, inner 𝕜 ((starRingEnd 𝕜) z • y) (x : H) = inner 𝕜 y (D x) := by
    intro x
    have h0 : (starRingEnd 𝕜) z * inner 𝕜 (x : H) y = inner 𝕜 (D x) y := by
      have := hy _ (LinearMap.mem_range_self (subDirac D z) x)
      rwa [subDirac_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at this
    have h1 := congrArg (starRingEnd 𝕜) h0
    rw [map_mul, RCLike.conj_conj, inner_conj_symm, inner_conj_symm] at h1
    rw [inner_smul_left, RCLike.conj_conj]
    exact h1
  -- Hence `y ∈ D†.domain = D.domain`.
  have hmem : y ∈ D†.domain := mem_adjoint_domain_of_exists y ⟨(starRingEnd 𝕜) z • y, hortho⟩
  have hydom : y ∈ D.domain := by rwa [hadj] at hmem
  -- `⟪y, D y⟫` is real (self-adjointness), and equals `z · ‖y‖²` via `hortho` at `x = y`.
  have hsa : D.IsFormalAdjoint D := by
    have h := adjoint_isFormalAdjoint (𝕜 := 𝕜) hD.dense_domain
    rwa [hadj] at h
  have hreal : (starRingEnd 𝕜) (inner 𝕜 y (D ⟨y, hydom⟩)) = inner 𝕜 y (D ⟨y, hydom⟩) := by
    have h1 : inner 𝕜 (D ⟨y, hydom⟩) y = inner 𝕜 y (D ⟨y, hydom⟩) := hsa ⟨y, hydom⟩ ⟨y, hydom⟩
    calc (starRingEnd 𝕜) (inner 𝕜 y (D ⟨y, hydom⟩))
        = (starRingEnd 𝕜) (inner 𝕜 (D ⟨y, hydom⟩) y) := by rw [h1]
      _ = inner 𝕜 y (D ⟨y, hydom⟩) := inner_conj_symm _ _
  have him : RCLike.im (inner 𝕜 y (D ⟨y, hydom⟩)) = 0 := RCLike.conj_eq_iff_im.mp hreal
  have hval : inner 𝕜 y (D ⟨y, hydom⟩) = z * ((‖y‖ ^ 2 : ℝ) : 𝕜) := by
    have hh := hortho ⟨y, hydom⟩
    rw [show ((⟨y, hydom⟩ : D.domain) : H) = y from rfl, inner_smul_left, RCLike.conj_conj,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hh
    exact hh.symm
  rw [hval, RCLike.im_mul_ofReal] at him
  -- him : RCLike.im z * ‖y‖ ^ 2 = 0
  have hy2 : (‖y‖ ^ 2 : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h hz
    · exact h
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hy2)

/-- The range of `z • 1 - D` is closed when `Im z ≠ 0`.

Strategy: the bounded-below estimate `|Im z| · ‖x‖ ≤ ‖(z • 1 - D) x‖` makes any preimage
sequence Cauchy; its limit `x` together with `D x = z • x - y` follows from closedness of the
graph of `D` (`hD.isClosed`), so the limit `y` of `(z • 1 - D) xₙ` is again in the range. -/
theorem isClosed_range_subDirac (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    IsClosed (LinearMap.range (subDirac D z) : Set H) := by
  have hpos : (0 : ℝ) < |RCLike.im z| := abs_pos.mpr hz
  apply IsSeqClosed.isClosed
  intro Y y hY hYy
  simp only [SetLike.mem_coe, LinearMap.mem_range] at hY
  choose X hX using hY
  -- The bounded-below estimate makes the preimage sequence Cauchy.
  have hbound : ∀ n m, ‖(X n : H) - (X m : H)‖ ≤ ‖Y n - Y m‖ / |RCLike.im z| := by
    intro n m
    have hsub : subDirac D z (X n - X m) = Y n - Y m := by rw [_root_.map_sub, hX, hX]
    have hb := hD.norm_resolvent_apply_ge z (X n - X m)
    rw [← subDirac_apply, hsub, Submodule.coe_sub] at hb
    rw [le_div_iff₀ hpos, mul_comm]
    exact hb
  have hCauchyX : CauchySeq (fun n => (X n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hYy.cauchySeq) (ε * |RCLike.im z|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hY' : ‖Y m - Y n‖ < ε * |RCLike.im z| := by
      have := hN m hm n hn; rwa [dist_eq_norm] at this
    rw [dist_eq_norm]
    calc ‖(X m : H) - (X n : H)‖ ≤ ‖Y m - Y n‖ / |RCLike.im z| := hbound m n
      _ < (ε * |RCLike.im z|) / |RCLike.im z| := by gcongr
      _ = ε := by rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchyX
  -- `D (X n) = z • X n - Y n` tends to `z • x - y`; the graph of `D` is closed.
  have heq : ∀ n, D (X n) = z • (X n : H) - Y n := by
    intro n
    have h := hX n; rw [subDirac_apply] at h; rw [← h]; abel
  have hDX : Filter.Tendsto (fun n => D (X n)) Filter.atTop (nhds (z • x - y)) := by
    simp only [heq]
    exact (hx.const_smul z).sub hYy
  have hmem : ((x, z • x - y) : H × H) ∈ D.graph :=
    hD.isClosed.mem_of_tendsto (hx.prodMk_nhds hDX)
      (Filter.Eventually.of_forall (fun n => D.mem_graph (X n)))
  rw [LinearPMap.mem_graph_iff] at hmem
  obtain ⟨x₀, hx1, hx2⟩ := hmem
  dsimp only at hx1 hx2
  rw [SetLike.mem_coe, LinearMap.mem_range]
  exact ⟨x₀, by rw [subDirac_apply, hx1, hx2]; abel⟩

/-- **Basic criterion of self-adjointness.** If `D` is self-adjoint and `Im z ≠ 0`, then
`z • 1 - D` is bijective on `D.domain`, i.e. `z` lies in the resolvent set of `D`. -/
theorem mem_resolventSet (hD : IsSelfAdjoint D) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    z ∈ D.resolventSet := by
  -- Surjectivity: the range is closed and dense, hence everything.
  have hrange : LinearMap.range (subDirac D z) = ⊤ := by
    have hcl := (hD.isClosed_range_subDirac hz).submodule_topologicalClosure_eq
    have hdense := (Submodule.topologicalClosure_eq_top_iff
      (K := LinearMap.range (subDirac D z))).mpr (hD.range_subDirac_orthogonal_eq_bot hz)
    rw [← hcl, hdense]
  have hsurj : Function.Surjective (subDirac D z) := LinearMap.range_eq_top.mp hrange
  have hbij : Function.Bijective (subDirac D z) := ⟨hD.injective_subDirac hz, hsurj⟩
  -- Repackage as bijectivity of `z • 1 +ᵥ (-D)`, the operator used in `resolventSet`.
  let op : H →ₗ.[𝕜] H := (z • LinearMap.id (R := 𝕜) (M := H)) +ᵥ (-D)
  change Function.Bijective ⇑op
  have hdom : op.domain = D.domain := rfl
  let e : op.domain ≃ₗ[𝕜] D.domain := LinearEquiv.ofEq op.domain D.domain hdom
  have hfun : ⇑op = ⇑(subDirac D z) ∘ ⇑e := by
    funext x
    simp only [op, e, Function.comp_apply, vadd_apply, LinearMap.smul_apply, LinearMap.id_apply,
      neg_apply, subDirac_apply, sub_eq_add_neg]
    congr 2
  rw [hfun]
  exact hbij.comp e.bijective

end IsSelfAdjoint
