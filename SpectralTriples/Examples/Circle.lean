/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable
public import SpectralTriples.DiagonalOperator
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The Dirac spectral triple of the circle `S¹`

The simplest concrete (odd, finitely summable) spectral triple, built on the Fourier side so
that the Dirac operator is **diagonal**, bypassing spin bundles and Sobolev theory.

* `H = ℓ²(ℤ)` (`lp (fun _ : ℤ => ℂ) 2`), the Fourier model of `L²(S¹)` with orthonormal
  basis `(eₙ)_{n∈ℤ}`.
* `D = -i d/dθ`, acting diagonally as `eₙ ↦ n · eₙ`, with maximal domain
  `dom D = { a ∈ ℓ²(ℤ) : Σ n² |aₙ|² < ∞ }` (the `H¹` Sobolev space).
* `π : C^∞(S¹) → 𝓑(ℓ²(ℤ))` by Fourier convolution; `[D, π(f)] = π(-i f')` is bounded.

`D` is self-adjoint with **compact resolvent** (`(i·1 − D)⁻¹` is diagonal with eigenvalues
`1/(i − n) → 0`), so the remaining step toward a finitely summable spectral triple is the
algebra representation; the `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple`
constructor will then assemble the structure without a separate `resolvent_mem` proof.

## Construction status and plan

The space, the `H¹` domain, the **diagonal Dirac operator** (`diracDirac`), its
**self-adjointness**, **`i ∈ ρ(D)`**, and **compact resolvent** are built and `sorry`-free.
The remaining algebra representation is absent from Mathlib and is the work ahead.

1. **Diagonal operator** — done (`diracDirac`, with `diracDirac_apply : (D a)ₙ = n · aₙ`).
2. **Self-adjointness** — done (`diracDirac_isSelfAdjoint`): symmetry from `inner_eq_tsum` +
   reality of the eigenvalues, then the adjoint-domain inclusion by testing against
   `lp.single 2 n 1` to read off `(D† b)ₙ = n · bₙ`. Gives `i ∈ ρ(D)` (`mem_resolventSet_I`).
3. **Compact resolvent** — done (`isCompactOperator_resolvent_I`): the resolvent is the
   bounded diagonal operator `bₙ ↦ bₙ/(i − n)`, a norm limit of finite-rank truncations since
   `1/(i − n) → 0`, via `lpDiag.isCompactOperator_diagL`.
4. **Representation** (ahead) `π : C^∞(S¹) → (ℓ²(ℤ) →L[ℂ] ℓ²(ℤ))` by convolution with Fourier
   coefficients; `dom_comp` and the commutator bound `[D, π f] = π(f')` from rapid decay.
5. **Assemble** via `IsOddSpectralTriple` and
   `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple`.

See `IsSelfAdjoint.mem_resolventSet` (off-real-axis bijectivity) and
`IsSelfAdjoint.isClosed_range_subDirac` for the criterion this construction feeds.
-/

@[expose] public section

open LinearPMap
open Filter
open scoped Topology

namespace SpectralTriples.Circle

/-- The Fourier model `ℓ²(ℤ)` of `L²(S¹)`: square-summable bi-infinite sequences of complex
numbers, a separable complex Hilbert space with orthonormal basis `(eₙ)_{n ∈ ℤ}`. -/
abbrev L2 : Type := lp (fun _ : ℤ => ℂ) 2

noncomputable instance : NormedAddCommGroup L2 := inferInstance
noncomputable instance : InnerProductSpace ℂ L2 := inferInstance
instance : CompleteSpace L2 := inferInstance

/-- The eigenvalues of the circle Dirac operator `D = -i d/dθ`: `D eₙ = n · eₙ`, so the `n`-th
eigenvalue is the real number `n`. These are real (hence `D` is symmetric) and satisfy
`|n| → ∞` (hence `D` has compact resolvent). -/
def diracEigen : ℤ → ℝ := fun n => (n : ℝ)

/-- The maximal domain of the circle Dirac operator: the `H¹` Sobolev space
`{ a ∈ ℓ²(ℤ) : Σ n² |aₙ|² < ∞ }`, i.e. those `a` for which `n ↦ n · aₙ` is again in `ℓ²(ℤ)`.
This is the domain on which the diagonal Dirac operator `(D a)ₙ = n · aₙ` will be defined. -/
def diracDomain : Submodule ℂ L2 where
  carrier := {a | Memℓp (fun n => (diracEigen n : ℂ) * a n) 2}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply, mul_add] at *
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at *
    have hrw : (fun n => (diracEigen n : ℂ) * (c * a n))
        = c • fun n => (diracEigen n : ℂ) * a n := by
      funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]; exact ha.const_smul c

theorem mem_diracDomain_iff (a : L2) :
    a ∈ diracDomain ↔ Memℓp (fun n => (diracEigen n : ℂ) * a n) 2 := Iff.rfl

/-- Coordinatewise multiplication by the eigenvalue sequence `(n)`, as an element of `ℓ²(ℤ)`,
given a proof that the result is square-summable. -/
def applyDirac (a : L2) (h : Memℓp (fun n => (diracEigen n : ℂ) * a n) 2) : L2 :=
  ⟨fun n => (diracEigen n : ℂ) * a n, h⟩

@[simp] theorem coe_applyDirac (a : L2) (h) (n : ℤ) :
    (applyDirac a h) n = (diracEigen n : ℂ) * a n := rfl

/-- The circle Dirac operator `D = -i d/dθ` as an unbounded `LinearPMap`: diagonal on the
Fourier basis, `(D a)ₙ = n · aₙ`, with domain the `H¹` Sobolev space `diracDomain`. -/
noncomputable def diracDirac : L2 →ₗ.[ℂ] L2 where
  domain := diracDomain
  toFun :=
    { toFun := fun a => applyDirac (a : L2) ((mem_diracDomain_iff _).mp a.2)
      map_add' := fun a b => by
        ext n
        simp only [coe_applyDirac, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        ext n
        simp only [coe_applyDirac, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, mul_left_comm] }

@[simp] theorem diracDirac_apply (a : diracDomain) (n : ℤ) :
    (diracDirac a) n = (diracEigen n : ℂ) * (a : L2) n := rfl

/-- The circle Dirac operator is symmetric (formally self-adjoint): `⟪D x, y⟫ = ⟪x, D y⟫`
on its domain, because its eigenvalues are real. -/
theorem diracDirac_isFormalAdjoint : diracDirac.IsFormalAdjoint diracDirac := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [diracDirac_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Each Fourier basis vector `eₙ = lp.single 2 n 1` lies in the `H¹` domain (it has finite
support, so `m ↦ m · (eₙ)ₘ = n · eₙ` is square-summable). -/
theorem single_mem_diracDomain (n : ℤ) : (lp.single 2 n (1 : ℂ) : L2) ∈ diracDomain := by
  rw [mem_diracDomain_iff]
  have hfun : (fun m => (diracEigen m : ℂ) * (lp.single 2 n (1 : ℂ) : L2) m)
      = (diracEigen n : ℂ) • (⇑(lp.single 2 n (1 : ℂ) : L2) : ℤ → ℂ) := by
    funext m
    rcases eq_or_ne m n with h | h
    · subst h; simp [lp.single_apply]
    · simp [lp.single_apply, h]
  rw [hfun]
  exact (lp.memℓp _).const_smul _

/-- The `H¹` domain is dense in `ℓ²(ℤ)`: it contains every Fourier basis vector, so its
orthogonal complement is trivial. -/
theorem dense_diracDomain : Dense (diracDirac.domain : Set L2) := by
  change Dense (diracDomain : Set L2)
  have horth : (diracDomain : Submodule ℂ L2)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine lp.ext (funext fun n => ?_)
    have h0 : inner ℂ (lp.single 2 n (1 : ℂ) : L2) y = 0 := hy _ (single_mem_diracDomain n)
    rw [lp.inner_single_left] at h0
    simpa [RCLike.inner_apply, lp.coeFn_zero] using h0
  have htop : diracDomain.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff (K := diracDomain)).mpr horth
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop, Submodule.top_coe]

/-- The circle Dirac operator is contained in its adjoint (symmetry ⇒ `D ≤ D†`). -/
theorem diracDirac_le_adjoint : diracDirac ≤ diracDirac† :=
  diracDirac_isFormalAdjoint.le_adjoint dense_diracDomain

/-- **The circle Dirac operator is self-adjoint.** Since it is symmetric (so `D ≤ D†`), it
suffices that `D†.domain ⊆ D.domain`: for `y ∈ D†.domain`, testing the adjoint relation against
each Fourier basis vector `eₙ` gives `(D† y)ₙ = n · yₙ`, so `n ↦ n · yₙ` is square-summable and
`y` lies in the `H¹` domain. -/
theorem diracDirac_isSelfAdjoint : IsSelfAdjoint diracDirac := by
  rw [isSelfAdjoint_def]
  have hfa : diracDirac†.IsFormalAdjoint diracDirac := adjoint_isFormalAdjoint dense_diracDomain
  have hdomle : diracDirac†.domain ≤ diracDomain := by
    intro y hy
    rw [mem_diracDomain_iff]
    have hcoe : (fun n => (diracEigen n : ℂ) * y n) = ⇑(diracDirac† ⟨y, hy⟩) := by
      funext n
      have key := hfa ⟨y, hy⟩ ⟨lp.single 2 n (1 : ℂ), single_mem_diracDomain n⟩
      have hDe : diracDirac ⟨lp.single 2 n (1 : ℂ), single_mem_diracDomain n⟩
          = (diracEigen n : ℂ) • (lp.single 2 n (1 : ℂ) : L2) := by
        refine lp.ext (funext fun m => ?_)
        simp only [diracDirac_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rcases eq_or_ne m n with h | h
        · subst h; rfl
        · simp [lp.single_apply, h]
      rw [lp.inner_single_right, hDe, inner_smul_right, lp.inner_single_right] at key
      have key2 := congrArg (starRingEnd ℂ) key
      simp [RCLike.inner_apply, map_mul, Complex.conj_ofReal] at key2
      exact key2.symm
    rw [hcoe]; exact lp.memℓp _
  have heq : diracDirac.domain = diracDirac†.domain :=
    le_antisymm diracDirac_le_adjoint.1 hdomle
  exact (LinearPMap.eq_of_le_of_domain_eq diracDirac_le_adjoint heq).symm

/-- `i` lies in the resolvent set of the circle Dirac operator: it is self-adjoint and
`Im i = 1 ≠ 0`, so the basic criterion applies. -/
theorem mem_resolventSet_I : Complex.I ∈ diracDirac.resolventSet :=
  diracDirac_isSelfAdjoint.mem_resolventSet (by simp)

/-! ### Compact resolvent -/

/-- The resolvent block at Fourier mode `n`: scalar multiplication by `(i - n)⁻¹` on the
fibre `ℂ`. -/
private noncomputable def resolventBlock (n : ℤ) : ℂ →L[ℂ] ℂ :=
  (Complex.I - (diracEigen n : ℂ))⁻¹ • ContinuousLinearMap.id ℂ ℂ

private lemma norm_sub_eigen_ge_one (n : ℤ) : (1 : ℝ) ≤ ‖Complex.I - (diracEigen n : ℂ)‖ := by
  have him : RCLike.im (Complex.I - (diracEigen n : ℂ)) = 1 := by simp [diracEigen]
  have h := RCLike.abs_im_le_norm (Complex.I - (diracEigen n : ℂ))
  rwa [him, abs_one] at h

private lemma norm_resolventBlock_eq (n : ℤ) :
    ‖resolventBlock n‖ = (‖Complex.I - (diracEigen n : ℂ)‖)⁻¹ := by
  unfold resolventBlock
  rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, norm_inv]

private lemma norm_resolventBlock_le_one (n : ℤ) : ‖resolventBlock n‖ ≤ 1 := by
  rw [norm_resolventBlock_eq]
  exact inv_le_one_of_one_le₀ (norm_sub_eigen_ge_one n)

private lemma norm_sub_eigen_tendsto_atTop :
    Tendsto (fun n : ℤ => ‖Complex.I - (diracEigen n : ℂ)‖) cofinite atTop := by
  have habs : Tendsto (fun n : ℤ => |(n : ℝ)|) cofinite atTop := by
    rw [Int.cofinite_eq, tendsto_sup]
    exact ⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id),
      tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩
  refine tendsto_atTop_mono' _ ?_ habs
  filter_upwards with n
  have hre : RCLike.re (Complex.I - (diracEigen n : ℂ)) = -(diracEigen n : ℝ) := by
    simp [diracEigen]
  have h := RCLike.abs_re_le_norm (Complex.I - (diracEigen n : ℂ))
  rwa [hre, abs_neg] at h

private lemma norm_resolventBlock_tendsto_zero :
    Tendsto (fun n : ℤ => ‖resolventBlock n‖) cofinite (𝓝 0) := by
  simp_rw [norm_resolventBlock_eq]
  exact tendsto_inv_atTop_zero.comp norm_sub_eigen_tendsto_atTop

private noncomputable def resolventDiag : L2 →L[ℂ] L2 :=
  lpDiag.diagL (𝕜 := ℂ) (G := fun _ : ℤ => ℂ) resolventBlock zero_le_one
    norm_resolventBlock_le_one

private lemma isCompactOperator_resolventDiag : IsCompactOperator resolventDiag :=
  lpDiag.isCompactOperator_diagL (𝕜 := ℂ) (G := fun _ : ℤ => ℂ) resolventBlock zero_le_one
    norm_resolventBlock_le_one norm_resolventBlock_tendsto_zero

/-- The resolvent block inverts `i·1 − D` at Fourier mode `n`. -/
private lemma resolventBlock_left_inverse (n : ℤ) (v : ℂ) :
    Complex.I • resolventBlock n v - (diracEigen n : ℂ) * resolventBlock n v = v := by
  have hne : Complex.I - (diracEigen n : ℂ) ≠ 0 := by
    intro h
    have h1 := norm_sub_eigen_ge_one n
    rw [h, norm_zero] at h1
    linarith
  unfold resolventBlock
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  field_simp

private lemma resolventBlock_dirac_apply (n : ℤ) (v : ℂ) :
    (diracEigen n : ℂ) * resolventBlock n v = Complex.I • resolventBlock n v - v := by
  have h := sub_eq_iff_eq_add'.mp (resolventBlock_left_inverse n v)
  rw [eq_sub_iff_add_eq]
  exact h.symm

private lemma resolventDiag_mem_diracDomain (a : L2) : resolventDiag a ∈ diracDomain := by
  rw [mem_diracDomain_iff]
  have hfun : (fun n => (diracEigen n : ℂ) * (resolventDiag a) n) =
      fun n => (Complex.I • resolventDiag a - a) n := by
    funext n
    rw [resolventDiag, lpDiag.diagL_apply, resolventBlock_dirac_apply]
    rfl
  rw [hfun]
  exact lp.memℓp _

private lemma resolvent_op_resolventDiag (a : L2) :
    (((Complex.I • LinearMap.id (R := ℂ) (M := L2)) +ᵥ (-diracDirac) : L2 →ₗ.[ℂ] L2)
      ⟨resolventDiag a, resolventDiag_mem_diracDomain a⟩) = a := by
  refine lp.ext (funext fun n => ?_)
  rw [vadd_apply, LinearMap.smul_apply, LinearMap.id_apply, neg_apply]
  change (Complex.I • resolventDiag a -
      diracDirac ⟨resolventDiag a, resolventDiag_mem_diracDomain a⟩) n = a n
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, diracDirac_apply]
  simpa only [resolventDiag, lpDiag.diagL_apply] using resolventBlock_left_inverse n (a n)

private lemma resolvent_eq_resolventDiag :
    diracDirac.resolvent Complex.I = (resolventDiag : L2 →ₗ[ℂ] L2) := by
  rw [LinearPMap.resolvent_apply_eq (f := diracDirac) mem_resolventSet_I]
  apply LinearMap.ext
  intro a
  have h := LinearPMap.apply_inverseAsLinearMap_apply_cancel
      (f := ((Complex.I • LinearMap.id (R := ℂ) (M := L2)) +ᵥ (-diracDirac) : L2 →ₗ.[ℂ] L2))
      mem_resolventSet_I
      (⟨resolventDiag a, resolventDiag_mem_diracDomain a⟩ :
        (((Complex.I • LinearMap.id (R := ℂ) (M := L2)) +ᵥ (-diracDirac) : L2 →ₗ.[ℂ] L2).domain))
  rw [resolvent_op_resolventDiag] at h
  exact h

/-- The resolvent of the circle Dirac operator at `i` is compact. -/
theorem isCompactOperator_resolvent_I :
    IsCompactOperator (diracDirac.resolvent Complex.I) := by
  rw [resolvent_eq_resolventDiag]
  exact isCompactOperator_resolventDiag

end SpectralTriples.Circle
