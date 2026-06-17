/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable
public import SpectralTriples.DiagonalOperator
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.Order.Northcott

/-! # The Dirac spectral triple of the 2-torus `T²`

The simplest **even** (`Z₂`-graded) concrete spectral triple, built on the Fourier side. The
flat torus `T² = ℝ²/ℤ²` has trivial spin structure; the spinor bundle is rank 2, and on the
Fourier mode `(m, n) ∈ ℤ²` the Dirac operator acts on the spinor fibre `ℂ²` by the
self-adjoint block
`D₍ₘ,ₙ₎ = 2π (σ₁ m + σ₂ n) = 2π · !![0, m - i·n; m + i·n, 0]`,
with eigenvalues `± 2π √(m² + n²)`. The chirality is `γ = σ₃ = diag(1, -1)`.

* `H = ℓ²(ℤ²; ℂ²)` (`lp (fun _ : ℤ × ℤ => EuclideanSpace ℂ (Fin 2)) 2`), the Hilbert space.
* `D` is block-diagonal, self-adjoint, with `(D + i)⁻¹` compact (`|2π√(m²+n²)| → ∞`).
* `γ` is a self-adjoint unitary involution, commuting with the (scalar) representation and
  anticommuting with `D` (since each block is off-diagonal and `γ` is diagonal).

This reuses the `S¹` strategy (a diagonal operator on `lp 2`, self-adjointness by testing
against `lp.single`, compact resolvent by finite-rank truncation), upgraded from scalar
eigenvalues to **self-adjoint 2×2 blocks** on the spinor fibre.

## Construction status and plan

The Hilbert space, the block-diagonal Dirac operator, its **self-adjointness** (hence
`i ∈ ρ(D)`), **compact resolvent**, and the **grading** `γ = σ₃` are done. The representation
and the final assembly are the work ahead.

1. **Hilbert space** `H = ℓ²(ℤ²; ℂ²)` — done.
2. **Dirac block** `diracBlock (m,n) : ℂ² →L[ℂ] ℂ²`, the self-adjoint matrix above; then the
   block-diagonal `D : H →ₗ.[ℂ] H`, `(D a)₍ₘ,ₙ₎ = diracBlock (m,n) (a ₍ₘ,ₙ₎)`, on the `H¹`
   domain `diracDomain` below — done.
3. **Self-adjointness** `IsSelfAdjoint D` — done: the block version of the `S¹` argument —
   symmetry from `inner_eq_tsum` + self-adjointness of each block; the adjoint-domain inclusion
   by testing against `lp.single (m,n) v` for single-mode spinors. `i ∈ ρ(D)` follows.
4. **Compact resolvent** `IsCompactOperator (D.resolvent i)` — done: the resolvent is the
   block-diagonal operator with blocks `(i·1 − D₍ₚ₎)⁻¹ = (1+|D₍ₚ₎|²)⁻¹(−i·1 − D₍ₚ₎)`, whose
   norms `→ 0` (since `|D₍ₚ₎| = 2π√(m²+n²) → ∞`); compactness then comes from the finite-rank
   truncation criterion `lpDiag.isCompactOperator_diagL`.
5. **Grading** `γ : H →L[ℂ] H` (fibrewise `σ₃`) — done: self-adjoint (`isSelfAdjoint_grading`),
   `γ² = 1` (`grading_mul_self`), domain-preserving (`grading_mem_diracDomain`), and
   anticommuting `D γ = -γ D` (`grading_anticomm`), since each `σ₃` anticommutes with the
   off-diagonal Dirac block.
6. **Representation** `π : C^∞(T²) → 𝓑(H)` by Fourier convolution (scalar, so `[γ, π a] = 0`).
7. **Assemble** `IsEvenSpectralTriple`, and via
   `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` a finitely summable triple at `i`.
-/

@[expose] public section

open LinearPMap
open Filter
open scoped Topology Matrix.Norms.L2Operator

namespace SpectralTriples.Torus

/-- The spinor fibre `ℂ²` (with its Hilbert-space structure). -/
abbrev Spinor : Type := EuclideanSpace ℂ (Fin 2)

/-- The Hilbert space `ℓ²(ℤ²; ℂ²)` of the `T²` Dirac triple: square-summable spinor-valued
sequences over the Fourier lattice `ℤ²`. -/
abbrev H : Type := lp (fun _ : ℤ × ℤ => Spinor) 2

noncomputable instance : NormedAddCommGroup H := inferInstance
noncomputable instance : InnerProductSpace ℂ H := inferInstance
instance : CompleteSpace H := inferInstance

/-- The magnitude of the Dirac eigenvalues on the Fourier mode `(m, n)`: the block
`2π(σ₁ m + σ₂ n)` has eigenvalues `± 2π √(m² + n²)`, all of magnitude `diracMagnitude (m, n)`.
This tends to `∞` as `(m, n) → ∞`, which is what makes the resolvent compact. -/
noncomputable def diracMagnitude : ℤ × ℤ → ℝ :=
  fun p => 2 * Real.pi * Real.sqrt ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)

/-- The Dirac block on the Fourier mode `(m, n)`: the self-adjoint matrix
`2π · !![0, m - i·n; m + i·n, 0]`, as a linear endomorphism of the spinor fibre `ℂ²`. -/
noncomputable def diracBlock (p : ℤ × ℤ) : Spinor →ₗ[ℂ] Spinor :=
  Matrix.toEuclideanLin <| (2 * Real.pi : ℂ) •
    !![0, (p.1 : ℂ) - (p.2 : ℂ) * Complex.I;
       (p.1 : ℂ) + (p.2 : ℂ) * Complex.I, 0]

/-- The maximal domain of the torus Dirac operator: the `H¹` Sobolev space, those `a` for which
`p ↦ D₍ₚ₎ (aₚ)` is again square-summable (equivalently `Σ (m²+n²) ‖aₚ‖² < ∞`). -/
def diracDomain : Submodule ℂ H where
  carrier := {a | Memℓp (fun p => diracBlock p (a p)) 2}
  zero_mem' := by
    have : (fun p => diracBlock p ((0 : H) p)) = 0 := by
      funext p; simp only [lp.coeFn_zero, Pi.zero_apply, _root_.map_zero]
    simp only [Set.mem_setOf_eq, this]; exact zero_memℓp
  add_mem' := fun {a b} ha hb => by
    have heq : (fun p => diracBlock p ((a + b) p))
        = (fun p => diracBlock p (a p)) + fun p => diracBlock p (b p) := by
      funext p; simp only [lp.coeFn_add, Pi.add_apply, _root_.map_add]
    rw [Set.mem_setOf_eq, heq]; exact ha.add hb
  smul_mem' := fun c a ha => by
    have heq : (fun p => diracBlock p ((c • a) p)) = c • fun p => diracBlock p (a p) := by
      funext p; simp only [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul]
    rw [Set.mem_setOf_eq, heq]; exact ha.const_smul c

theorem mem_diracDomain_iff (a : H) :
    a ∈ diracDomain ↔ Memℓp (fun p => diracBlock p (a p)) 2 := Iff.rfl

/-- Coordinatewise application of the Dirac blocks, as an element of `ℓ²(ℤ²; ℂ²)`, given a
proof that the result is square-summable. -/
noncomputable def applyDirac (a : H) (h : Memℓp (fun p => diracBlock p (a p)) 2) : H :=
  ⟨fun p => diracBlock p (a p), h⟩

@[simp] theorem coe_applyDirac (a : H) (h) (p : ℤ × ℤ) :
    (applyDirac a h) p = diracBlock p (a p) := rfl

/-- The torus Dirac operator as an unbounded `LinearPMap`: block-diagonal on the Fourier
lattice, `(D a)₍ₘ,ₙ₎ = D₍ₘ,ₙ₎ (a₍ₘ,ₙ₎)`, with domain the `H¹` Sobolev space `diracDomain`. -/
noncomputable def diracDirac : H →ₗ.[ℂ] H where
  domain := diracDomain
  toFun :=
    { toFun := fun a => applyDirac (a : H) ((mem_diracDomain_iff _).mp a.2)
      map_add' := fun a b => by
        refine lp.ext (funext fun p => ?_)
        simp only [coe_applyDirac, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, _root_.map_add]
      map_smul' := fun c a => by
        refine lp.ext (funext fun p => ?_)
        simp only [coe_applyDirac, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
          _root_.map_smul, RingHom.id_apply] }

@[simp] theorem diracDirac_apply (a : diracDomain) (p : ℤ × ℤ) :
    (diracDirac a) p = diracBlock p ((a : H) p) := rfl

/-- Each Dirac block is self-adjoint on the spinor fibre: the matrix
`2π·!![0, m-in; m+in, 0]` is Hermitian. -/
theorem diracBlock_isSymmetric (p : ℤ × ℤ) : (diracBlock p).IsSymmetric := by
  rw [diracBlock, Matrix.isSymmetric_toEuclideanLin_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.smul_apply, Complex.conj_ofReal, sub_eq_add_neg]

/-- The torus Dirac operator is symmetric (formally self-adjoint): `⟪D a, b⟫ = ⟪a, D b⟫` on its
domain, because each spinor block is self-adjoint. -/
theorem diracDirac_isFormalAdjoint : diracDirac.IsFormalAdjoint diracDirac := by
  intro a b
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [diracDirac_apply, diracDirac_apply]
  exact diracBlock_isSymmetric p _ _

/-- Each `lp.single (m, n) v` (a single spinor in one Fourier mode) lies in the `H¹` domain: it
has finite support, so `q ↦ D₍q₎ (single₍q₎)` is supported on `{(m, n)}` and square-summable. -/
theorem single_mem_diracDomain (p : ℤ × ℤ) (v : Spinor) :
    (lp.single 2 p v : H) ∈ diracDomain := by
  rw [mem_diracDomain_iff]
  have hfun : (fun q => diracBlock q ((lp.single 2 p v : H) q))
      = ⇑(lp.single 2 p (diracBlock p v) : H) := by
    funext q
    rcases eq_or_ne q p with h | h
    · subst h; simp [lp.single_apply]
    · simp [lp.single_apply, h, _root_.map_zero]
  rw [hfun]
  exact lp.memℓp _

/-- The image `D (single (m, n) v) = single (m, n) (D₍ₘ,ₙ₎ v)`: the block-diagonal operator acts
on a single-mode vector by its block in that mode. -/
theorem diracDirac_single (p : ℤ × ℤ) (v : Spinor) :
    diracDirac ⟨lp.single 2 p v, single_mem_diracDomain p v⟩
      = (lp.single 2 p (diracBlock p v) : H) := by
  refine lp.ext (funext fun q => ?_)
  rcases eq_or_ne q p with h | h
  · subst h; simp [diracDirac_apply, lp.single_apply]
  · simp [diracDirac_apply, lp.single_apply, h, _root_.map_zero]

/-- The `H¹` domain is dense in `ℓ²(ℤ²; ℂ²)`: it contains every single-mode spinor, so its
orthogonal complement is trivial. -/
theorem dense_diracDomain : Dense (diracDirac.domain : Set H) := by
  change Dense (diracDomain : Set H)
  have horth : (diracDomain : Submodule ℂ H)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine lp.ext (funext fun p => ?_)
    refine ext_inner_left ℂ fun v => ?_
    have h0 : inner ℂ (lp.single 2 p v : H) y = 0 := hy _ (single_mem_diracDomain p v)
    rw [lp.inner_single_left] at h0
    rw [h0, lp.coeFn_zero, Pi.zero_apply, inner_zero_right]
  have htop : diracDomain.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff (K := diracDomain)).mpr horth
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop, Submodule.top_coe]

/-- The torus Dirac operator is contained in its adjoint (symmetry ⇒ `D ≤ D†`). -/
theorem diracDirac_le_adjoint : diracDirac ≤ diracDirac† :=
  diracDirac_isFormalAdjoint.le_adjoint dense_diracDomain

/-- **The torus Dirac operator is self-adjoint.** It is symmetric (so `D ≤ D†`); it remains to
show `D†.domain ⊆ D.domain`. For `y ∈ D†.domain`, testing the adjoint relation against each
single-mode spinor `single (m, n) v` and using self-adjointness of the block gives
`(D† y)₍ₘ,ₙ₎ = D₍ₘ,ₙ₎ (y₍ₘ,ₙ₎)`, so `q ↦ D₍q₎ (y₍q₎)` is square-summable and `y ∈ H¹`. -/
theorem diracDirac_isSelfAdjoint : IsSelfAdjoint diracDirac := by
  rw [isSelfAdjoint_def]
  have hfa : diracDirac†.IsFormalAdjoint diracDirac := adjoint_isFormalAdjoint dense_diracDomain
  have hdomle : diracDirac†.domain ≤ diracDomain := by
    intro y hy
    rw [mem_diracDomain_iff]
    have hcoe : (fun p => diracBlock p (y p)) = ⇑(diracDirac† ⟨y, hy⟩) := by
      funext p
      refine (ext_inner_right ℂ fun v => ?_).symm
      have key := hfa ⟨y, hy⟩ ⟨lp.single 2 p v, single_mem_diracDomain p v⟩
      rw [lp.inner_single_right, diracDirac_single, lp.inner_single_right] at key
      rw [key]
      exact (diracBlock_isSymmetric p (y p) v).symm
    rw [hcoe]; exact lp.memℓp _
  have heq : diracDirac.domain = diracDirac†.domain :=
    le_antisymm diracDirac_le_adjoint.1 hdomle
  exact (LinearPMap.eq_of_le_of_domain_eq diracDirac_le_adjoint heq).symm

/-- `i` lies in the resolvent set of the torus Dirac operator: it is self-adjoint and
`Im i = 1 ≠ 0`, so the basic criterion applies. -/
theorem mem_resolventSet_I : Complex.I ∈ diracDirac.resolventSet :=
  diracDirac_isSelfAdjoint.mem_resolventSet (by simp)

private noncomputable def diracMatrix (p : ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 * Real.pi : ℂ) •
    !![0, (p.1 : ℂ) - (p.2 : ℂ) * Complex.I;
       (p.1 : ℂ) + (p.2 : ℂ) * Complex.I, 0]

private noncomputable def diracSq (p : ℤ × ℤ) : ℝ :=
  (2 * Real.pi) ^ 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)

private lemma diracMagnitude_nonneg (p : ℤ × ℤ) : 0 ≤ diracMagnitude p := by
  unfold diracMagnitude
  positivity

private lemma diracMagnitude_sq (p : ℤ × ℤ) :
    diracMagnitude p ^ 2 = diracSq p := by
  have hnonneg : 0 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
  unfold diracMagnitude diracSq
  rw [mul_pow, Real.sq_sqrt hnonneg]

private lemma diracSq_nonneg (p : ℤ × ℤ) : 0 ≤ diracSq p := by
  rw [← diracMagnitude_sq]
  positivity

private lemma diracMatrix_conjTranspose (p : ℤ × ℤ) :
    (diracMatrix p).conjTranspose = diracMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMatrix, Matrix.conjTranspose_apply, Matrix.smul_apply, Complex.conj_ofReal,
      sub_eq_add_neg]

private lemma diracMatrix_sq (p : ℤ × ℤ) :
    diracMatrix p * diracMatrix p =
      ((diracSq p : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMatrix, diracSq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      sub_eq_add_neg]
    <;> ring_nf
    <;> rw [Complex.I_sq]
    <;> ring_nf

private lemma norm_diracMatrix (p : ℤ × ℤ) : ‖diracMatrix p‖ = diracMagnitude p := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (diracMatrix p)
  rw [diracMatrix_conjTranspose, diracMatrix_sq] at h
  have hleft :
      ‖((diracSq p : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ =
        diracMagnitude p ^ 2 := by
    rw [show (((diracSq p : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        Matrix.diagonal (fun _ : Fin 2 => ((diracSq p : ℝ) : ℂ)) by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.smul_apply]]
    rw [Matrix.l2_opNorm_diagonal]
    simp [Pi.norm_def, Finset.sup_const Finset.univ_nonempty, Real.nnnorm_of_nonneg,
      diracSq_nonneg, diracMagnitude_sq]
  have hsq : ‖diracMatrix p‖ ^ 2 = diracMagnitude p ^ 2 := by
    rw [pow_two]
    rw [← h, hleft]
  exact sq_eq_sq₀ (norm_nonneg _) (diracMagnitude_nonneg p) |>.mp hsq

private lemma diracBlock_sq_apply (p : ℤ × ℤ) (v : Spinor) :
    diracBlock p (diracBlock p v) = ((diracMagnitude p ^ 2 : ℝ) : ℂ) • v := by
  apply WithLp.ofLp_injective (p := 2)
  change WithLp.ofLp ((Matrix.toLpLin 2 2 (diracMatrix p))
      ((Matrix.toLpLin 2 2 (diracMatrix p)) v)) =
    WithLp.ofLp (((diracMagnitude p ^ 2 : ℝ) : ℂ) • v)
  rw [Matrix.ofLp_toLpLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.mulVec_mulVec, diracMatrix_sq, ← diracMagnitude_sq]
  simp [Matrix.smul_mulVec]

private noncomputable def diracBlockL (p : ℤ × ℤ) : Spinor →L[ℂ] Spinor :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracMatrix p)

@[simp] private lemma coe_diracBlockL (p : ℤ × ℤ) :
    (diracBlockL p : Spinor →ₗ[ℂ] Spinor) = diracBlock p := rfl

@[simp] private lemma diracBlockL_apply (p : ℤ × ℤ) (v : Spinor) :
    diracBlockL p v = diracBlock p v := by
  change (diracBlockL p : Spinor →ₗ[ℂ] Spinor) v = diracBlock p v
  rw [coe_diracBlockL]

private lemma norm_diracBlockL (p : ℤ × ℤ) : ‖diracBlockL p‖ = diracMagnitude p := by
  change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracMatrix p)‖ = diracMagnitude p
  rw [Matrix.l2_opNorm_toEuclideanCLM, norm_diracMatrix]

private noncomputable def resolventBlock (p : ℤ × ℤ) : Spinor →L[ℂ] Spinor :=
  (((1 / (1 + diracMagnitude p ^ 2) : ℝ) : ℂ)) •
    (-(Complex.I) • ContinuousLinearMap.id ℂ Spinor - diracBlockL p)

private lemma norm_resolventBlock_le_bound (p : ℤ × ℤ) :
    ‖resolventBlock p‖ ≤ (1 + diracMagnitude p) / (1 + diracMagnitude p ^ 2) := by
  let s : ℂ := ((1 / (1 + diracMagnitude p ^ 2) : ℝ) : ℂ)
  let T : Spinor →L[ℂ] Spinor :=
    -(Complex.I) • ContinuousLinearMap.id ℂ Spinor - diracBlockL p
  have hs : ‖s‖ = 1 / (1 + diracMagnitude p ^ 2) := by
    dsimp [s]
    rw [show ‖((1 / (1 + diracMagnitude p ^ 2) : ℝ) : ℂ)‖ =
        |(1 / (1 + diracMagnitude p ^ 2) : ℝ)| from RCLike.norm_ofReal (K := ℂ) _]
    rw [abs_of_nonneg]
    positivity
  have hIid : ‖-(Complex.I) • ContinuousLinearMap.id ℂ Spinor‖ = 1 := by
    rw [norm_smul, ContinuousLinearMap.norm_id]
    simp
  have hT : ‖T‖ ≤ 1 + diracMagnitude p := by
    dsimp [T]
    calc
      ‖-(Complex.I) • ContinuousLinearMap.id ℂ Spinor - diracBlockL p‖
          ≤ ‖-(Complex.I) • ContinuousLinearMap.id ℂ Spinor‖ + ‖diracBlockL p‖ := norm_sub_le _ _
      _ = 1 + diracMagnitude p := by
        rw [hIid, norm_diracBlockL]
  calc
    ‖resolventBlock p‖ = ‖s • T‖ := rfl
    _ = ‖s‖ * ‖T‖ := norm_smul _ _
    _ ≤ (1 / (1 + diracMagnitude p ^ 2)) * (1 + diracMagnitude p) := by
      rw [hs]
      gcongr
    _ = (1 + diracMagnitude p) / (1 + diracMagnitude p ^ 2) := by ring

private lemma resolventBlock_left_inverse (p : ℤ × ℤ) (v : Spinor) :
    Complex.I • resolventBlock p v - diracBlock p (resolventBlock p v) = v := by
  let s : ℂ := ((1 / (1 + diracMagnitude p ^ 2) : ℝ) : ℂ)
  let d : ℂ := ((diracMagnitude p ^ 2 : ℝ) : ℂ)
  have hden : (1 + diracMagnitude p ^ 2 : ℝ) ≠ 0 := by positivity
  have hs : s * (1 + d) = 1 := by
    have hreal : (1 / (1 + diracMagnitude p ^ 2)) *
        (1 + diracMagnitude p ^ 2) = (1 : ℝ) := by
      field_simp [hden]
    dsimp [s, d]
    exact_mod_cast hreal
  have hscalar : -(Complex.I ^ 2 * s) + s * d = 1 := by
    rw [Complex.I_sq]
    simpa [mul_add] using hs
  unfold resolventBlock
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, diracBlockL_apply]
  rw [_root_.map_smul, _root_.map_sub, _root_.map_smul, diracBlock_sq_apply]
  change Complex.I • s • (-Complex.I • v - diracBlock p v) -
      s • (-Complex.I • diracBlock p v - d • v) = v
  calc
    Complex.I • s • (-Complex.I • v - diracBlock p v) -
        s • (-Complex.I • diracBlock p v - d • v)
        = (-(Complex.I ^ 2 * s) + s * d) • v := by module
    _ = v := by rw [hscalar, one_smul]

private lemma resolventBlock_dirac_apply (p : ℤ × ℤ) (v : Spinor) :
    diracBlock p (resolventBlock p v) = Complex.I • resolventBlock p v - v := by
  have h := sub_eq_iff_eq_add'.mp (resolventBlock_left_inverse p v)
  rw [eq_sub_iff_add_eq]
  exact h.symm

private def radius (p : ℤ × ℤ) : ℕ := max p.1.natAbs p.2.natAbs

private lemma radius_northcott : Northcott radius where
  finite_le n := by
    classical
    let s : Finset (ℤ × ℤ) := (Finset.range (n + 1)).biUnion fun k => Finset.box k
    refine s.finite_toSet.subset ?_
    intro p hp
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨radius p, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hp
    · exact Int.mem_box.mpr rfl

private lemma radius_tendsto_atTop : Tendsto radius cofinite atTop := by
  rw [← northcott_iff_tendsto]
  exact radius_northcott

private lemma radius_le_sqrt (p : ℤ × ℤ) :
    (radius p : ℝ) ≤ Real.sqrt ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) := by
  have hsum : 0 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
  have h1 : ((p.1.natAbs : ℕ) : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    have habs : ((p.1.natAbs : ℕ) : ℝ) = |(p.1 : ℝ)| := by
      simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) p.1)
    rw [habs, sq_abs]
    nlinarith [sq_nonneg (p.2 : ℝ)]
  have h2 : ((p.2.natAbs : ℕ) : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    have habs : ((p.2.natAbs : ℕ) : ℝ) = |(p.2 : ℝ)| := by
      simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) p.2)
    rw [habs, sq_abs]
    nlinarith [sq_nonneg (p.1 : ℝ)]
  have hsq : (radius p : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    unfold radius
    by_cases hle : p.1.natAbs ≤ p.2.natAbs
    · rw [max_eq_right hle]
      exact h2
    · rw [max_eq_left (le_of_not_ge hle)]
      exact h1
  rw [← sq_le_sq₀ (by positivity : 0 ≤ (radius p : ℝ)) (Real.sqrt_nonneg _),
    Real.sq_sqrt hsum]
  exact hsq

private lemma diracMagnitude_tendsto_atTop : Tendsto diracMagnitude cofinite atTop := by
  have hradR : Tendsto (fun p : ℤ × ℤ => (radius p : ℝ)) cofinite atTop :=
    tendsto_natCast_atTop_atTop.comp radius_tendsto_atTop
  have hscale : Tendsto (fun p : ℤ × ℤ => (2 * Real.pi) * (radius p : ℝ)) cofinite atTop :=
    hradR.const_mul_atTop' (by positivity : (0 : ℝ) < 2 * Real.pi)
  refine tendsto_atTop_mono' _ ?_ hscale
  filter_upwards with p
  unfold diracMagnitude
  exact mul_le_mul_of_nonneg_left (radius_le_sqrt p) (by positivity)

private lemma ratio_le_two_inv (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) / (1 + x ^ 2) ≤ 2 / (1 + x) := by
  have hpos1 : 0 < 1 + x := by linarith
  have hpos2 : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  rw [div_le_div_iff₀ hpos2 hpos1]
  nlinarith [sq_nonneg (x - 1)]

private lemma norm_resolventBlock_le_two (p : ℤ × ℤ) : ‖resolventBlock p‖ ≤ 2 := by
  calc
    ‖resolventBlock p‖ ≤ (1 + diracMagnitude p) / (1 + diracMagnitude p ^ 2) :=
      norm_resolventBlock_le_bound p
    _ ≤ 2 / (1 + diracMagnitude p) := ratio_le_two_inv _ (diracMagnitude_nonneg p)
    _ ≤ 2 := by
      have hpos : 0 < 1 + diracMagnitude p := by linarith [diracMagnitude_nonneg p]
      rw [div_le_iff₀ hpos]
      nlinarith [diracMagnitude_nonneg p]

private lemma norm_resolventBlock_tendsto_zero :
    Tendsto (fun p : ℤ × ℤ => ‖resolventBlock p‖) cofinite (𝓝 0) := by
  have hden : Tendsto (fun p : ℤ × ℤ => 1 + diracMagnitude p) cofinite atTop := by
    refine tendsto_atTop_mono' _ ?_ diracMagnitude_tendsto_atTop
    filter_upwards with p
    linarith
  have hmajor0 : Tendsto (fun p : ℤ × ℤ => 2 / (1 + diracMagnitude p)) cofinite (𝓝 0) :=
    hden.const_div_atTop 2
  refine squeeze_zero (fun p => norm_nonneg _) ?_ hmajor0
  intro p
  exact (norm_resolventBlock_le_bound p).trans
    (ratio_le_two_inv _ (diracMagnitude_nonneg p))

private noncomputable def resolventDiag : H →L[ℂ] H :=
  lpDiag.diagL (𝕜 := ℂ) (G := fun _ : ℤ × ℤ => Spinor) resolventBlock (C := 2)
    (by norm_num) (fun p => norm_resolventBlock_le_two p)

private lemma isCompactOperator_resolventDiag : IsCompactOperator resolventDiag := by
  exact lpDiag.isCompactOperator_diagL (𝕜 := ℂ) (G := fun _ : ℤ × ℤ => Spinor)
    resolventBlock (C := 2) (by norm_num) (fun p => norm_resolventBlock_le_two p)
    norm_resolventBlock_tendsto_zero

private lemma resolventDiag_mem_diracDomain (x : H) : resolventDiag x ∈ diracDomain := by
  rw [mem_diracDomain_iff]
  have hfun : (fun q => diracBlock q ((resolventDiag x) q)) =
      fun q => (Complex.I • resolventDiag x - x) q := by
    funext q
    rw [resolventDiag, lpDiag.diagL_apply, resolventBlock_dirac_apply]
    rfl
  rw [hfun]
  exact lp.memℓp (Complex.I • resolventDiag x - x)

private lemma resolvent_op_resolventDiag (x : H) :
    (((Complex.I • LinearMap.id (R := ℂ) (M := H)) +ᵥ (-diracDirac) : H →ₗ.[ℂ] H)
      ⟨resolventDiag x, resolventDiag_mem_diracDomain x⟩) = x := by
  refine lp.ext (funext fun q => ?_)
  rw [vadd_apply, LinearMap.smul_apply, LinearMap.id_apply, neg_apply]
  change (Complex.I • resolventDiag x -
      diracDirac ⟨resolventDiag x, resolventDiag_mem_diracDomain x⟩) q = x q
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, diracDirac_apply]
  simpa only [resolventDiag, lpDiag.diagL_apply] using resolventBlock_left_inverse q (x q)

set_option maxHeartbeats 800000 in
-- This proof asks Lean to compare the unfolded resolvent operator with a named diagonal map.
private lemma resolvent_eq_resolventDiag :
    diracDirac.resolvent Complex.I = (resolventDiag : H →ₗ[ℂ] H) := by
  rw [LinearPMap.resolvent_apply_eq (f := diracDirac) mem_resolventSet_I]
  apply LinearMap.ext
  intro x
  have h := LinearPMap.apply_inverseAsLinearMap_apply_cancel
      (f := ((Complex.I • LinearMap.id (R := ℂ) (M := H)) +ᵥ (-diracDirac) : H →ₗ.[ℂ] H))
      mem_resolventSet_I
      (⟨resolventDiag x, resolventDiag_mem_diracDomain x⟩ :
        (((Complex.I • LinearMap.id (R := ℂ) (M := H)) +ᵥ (-diracDirac) : H →ₗ.[ℂ] H).domain))
  rw [resolvent_op_resolventDiag] at h
  exact h

/-- The resolvent of the torus Dirac operator at `i` is compact. -/
theorem isCompactOperator_resolvent_I :
    IsCompactOperator (diracDirac.resolvent Complex.I) := by
  rw [resolvent_eq_resolventDiag]
  exact isCompactOperator_resolventDiag

/-! ### The grading `γ = σ₃`

The chirality operator is the block-diagonal operator acting fibrewise by `σ₃ = diag(1, -1)`.
It is a self-adjoint unitary involution (`γ = γ*`, `γ² = 1`) that anticommutes with the Dirac
operator (each Dirac block is off-diagonal, `σ₃` is diagonal, so `σ₃ D₍ₚ₎ = -D₍ₚ₎ σ₃`). -/

/-- The chirality matrix `σ₃ = diag(1, -1)` on the spinor fibre. -/
noncomputable def gradingMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σ₃` as an endomorphism of the spinor fibre. -/
noncomputable def gradingBlock : Spinor →ₗ[ℂ] Spinor :=
  Matrix.toEuclideanLin gradingMatrix

/-- `σ₃` as a continuous endomorphism of the spinor fibre. -/
noncomputable def gradingBlockL : Spinor →L[ℂ] Spinor :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix

@[simp] theorem coe_gradingBlockL :
    (gradingBlockL : Spinor →ₗ[ℂ] Spinor) = gradingBlock := rfl

@[simp] theorem gradingBlockL_apply (v : Spinor) : gradingBlockL v = gradingBlock v := rfl

private lemma gradingMatrix_mul_self : gradingMatrix * gradingMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradingMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private lemma diracMatrix_mul_gradingMatrix (p : ℤ × ℤ) :
    diracMatrix p * gradingMatrix = -(gradingMatrix * diracMatrix p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMatrix, gradingMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

private lemma gradingBlock_isSymmetric : (gradingBlock).IsSymmetric := by
  rw [gradingBlock, Matrix.isSymmetric_toEuclideanLin_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradingMatrix, Matrix.conjTranspose_apply]

/-- `σ₃ * σ₃ = 1` as continuous operators (`Matrix.toEuclideanCLM` is a `*`-algebra map). -/
private lemma gradingBlockL_mul_self : gradingBlockL * gradingBlockL = 1 := by
  change Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix *
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix = 1
  rw [← _root_.map_mul, gradingMatrix_mul_self, _root_.map_one]

private lemma gradingBlock_apply_self (v : Spinor) : gradingBlock (gradingBlock v) = v := by
  have h : gradingBlockL (gradingBlockL v) = (1 : Spinor →L[ℂ] Spinor) v := by
    rw [← ContinuousLinearMap.mul_apply, gradingBlockL_mul_self]
  simpa using h

/-- `D₍ₚ₎ σ₃ = -σ₃ D₍ₚ₎` as continuous operators. -/
private lemma diracBlockL_gradingBlockL_anticomm (p : ℤ × ℤ) :
    diracBlockL p * gradingBlockL = -(gradingBlockL * diracBlockL p) := by
  change Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracMatrix p) *
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix =
      -(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix *
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracMatrix p))
  rw [← _root_.map_mul, ← _root_.map_mul, diracMatrix_mul_gradingMatrix, _root_.map_neg]

private lemma diracBlock_gradingBlock_anticomm (p : ℤ × ℤ) (v : Spinor) :
    diracBlock p (gradingBlock v) = -gradingBlock (diracBlock p v) := by
  have h := congrArg (fun T : Spinor →L[ℂ] Spinor => T v) (diracBlockL_gradingBlockL_anticomm p)
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply, diracBlockL_apply,
    gradingBlockL_apply] using h

theorem norm_gradingBlockL_le_one : ‖gradingBlockL‖ ≤ 1 := by
  have hdiag : gradingMatrix = Matrix.diagonal ![1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gradingMatrix, Matrix.diagonal]
  have hnorm : ‖gradingBlockL‖ = ‖(![1, -1] : Fin 2 → ℂ)‖ := by
    change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) gradingMatrix‖ = _
    rw [Matrix.l2_opNorm_toEuclideanCLM, hdiag, Matrix.l2_opNorm_diagonal]
  rw [hnorm, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i <;> simp

/-- The chirality (grading) operator `γ = σ₃` on `ℓ²(ℤ²; ℂ²)`: block-diagonal, acting on each
Fourier mode by `σ₃ = diag(1, -1)`. -/
noncomputable def grading : H →L[ℂ] H :=
  lpDiag.diagL (𝕜 := ℂ) (G := fun _ : ℤ × ℤ => Spinor) (fun _ => gradingBlockL) zero_le_one
    (fun _ => norm_gradingBlockL_le_one)

@[simp] theorem grading_apply (a : H) (q : ℤ × ℤ) : (grading a) q = gradingBlock (a q) := by
  rw [grading, lpDiag.diagL_apply, gradingBlockL_apply]

/-- The grading is symmetric: `⟪γ a, b⟫ = ⟪a, γ b⟫`, fibrewise from `σ₃` being Hermitian. -/
theorem grading_isSymmetric : (grading : H →ₗ[ℂ] H).IsSymmetric := by
  intro a b
  rw [ContinuousLinearMap.coe_coe, lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [grading_apply, grading_apply]
  exact gradingBlock_isSymmetric (a q) (b q)

/-- The grading is self-adjoint. -/
theorem isSelfAdjoint_grading : IsSelfAdjoint grading :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr grading_isSymmetric

/-- The grading is an involution: `γ² = 1`. -/
theorem grading_mul_self : grading * grading = 1 := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [ContinuousLinearMap.one_apply]
  refine lp.ext (funext fun q => ?_)
  rw [ContinuousLinearMap.mul_apply, grading_apply, grading_apply]
  exact gradingBlock_apply_self (a q)

/-- The grading preserves the Dirac domain `H¹`. -/
theorem grading_mem_diracDomain (x : diracDomain) : grading (x : H) ∈ diracDomain := by
  rw [mem_diracDomain_iff]
  have hfun : (fun q => diracBlock q ((grading (x : H)) q))
      = ⇑(-grading (diracDirac x)) := by
    funext q
    rw [grading_apply, diracBlock_gradingBlock_anticomm, lp.coeFn_neg, Pi.neg_apply,
      grading_apply, diracDirac_apply]
  rw [hfun]
  exact lp.memℓp _

/-- The grading anticommutes with the Dirac operator: `D (γ x) = - γ (D x)`. -/
theorem grading_anticomm (x : diracDomain) :
    diracDirac ⟨grading (x : H), grading_mem_diracDomain x⟩ = -grading (diracDirac x) := by
  refine lp.ext (funext fun q => ?_)
  rw [diracDirac_apply, lp.coeFn_neg, Pi.neg_apply, grading_apply, grading_apply,
    diracDirac_apply, diracBlock_gradingBlock_anticomm]

end SpectralTriples.Torus
