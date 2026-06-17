/-
Copyright (c) 2026 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Michael R. Douglas
-/

module

public import SpectralTriples.FinitelySummable
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The Dirac spectral triple of the circle `S¹`

The simplest concrete (odd, finitely summable) spectral triple, built on the Fourier side so
that the Dirac operator is **diagonal**, bypassing spin bundles and Sobolev theory.

* `H = ℓ²(ℤ)` (`lp (fun _ : ℤ => ℂ) 2`), the Fourier model of `L²(S¹)` with orthonormal
  basis `(eₙ)_{n∈ℤ}`.
* `D = -i d/dθ`, acting diagonally as `eₙ ↦ n · eₙ`, with maximal domain
  `dom D = { a ∈ ℓ²(ℤ) : Σ n² |aₙ|² < ∞ }` (the `H¹` Sobolev space).
* `π : C^∞(S¹) → 𝓑(ℓ²(ℤ))` by Fourier convolution; `[D, π(f)] = π(-i f')` is bounded.

`D` is self-adjoint with **compact resolvent** (`(D + i)⁻¹` is diagonal with eigenvalues
`1/(n+i) → 0`), so the data is a finitely summable spectral triple at `z = i` — which the
`IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` constructor turns into the structure
without a separate `resolvent_mem` proof.

## Construction status and plan

The space, the `H¹` domain, the **diagonal Dirac operator** (`diracDirac`), its
**self-adjointness**, and **`i ∈ ρ(D)`** are built and `sorry`-free. The remaining analytic
core (compact resolvent, representation) is absent from Mathlib and is the work ahead — shared
with the `T²` example, which reuses the same diagonal-operator machinery over `ℤ²`.

1. **Diagonal operator** — done (`diracDirac`, with `diracDirac_apply : (D a)ₙ = n · aₙ`).
   To reuse for `T²`, generalize to eigenvalues `μ : ι → ℝ` over an arbitrary index `ι`.
2. **Self-adjointness** — done (`diracDirac_isSelfAdjoint`): symmetry from `inner_eq_tsum` +
   reality of the eigenvalues, then the adjoint-domain inclusion by testing against
   `lp.single 2 n 1` to read off `(D† b)ₙ = n · bₙ`. Gives `i ∈ ρ(D)` (`mem_resolventSet_I`).
3. **Compact resolvent** (ahead) `IsCompactOperator (diracDirac.resolvent Complex.I)`: the
   resolvent is the bounded diagonal operator `bₙ ↦ bₙ/(i − n)`, a norm limit of finite-rank
   truncations since `1/(i − n) → 0`.
4. **Representation** (ahead) `π : C^∞(S¹) → (ℓ²(ℤ) →L[ℂ] ℓ²(ℤ))` by convolution with Fourier
   coefficients; `dom_comp` and the commutator bound `[D, π f] = π(f')` from rapid decay.
5. **Assemble** via `IsOddSpectralTriple` and
   `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple … (z := Complex.I)`.

See `IsSelfAdjoint.mem_resolventSet` (off-real-axis bijectivity) and
`IsSelfAdjoint.isClosed_range_subDirac` for the criterion this construction feeds.
-/

@[expose] public section

open LinearPMap

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

/- TODO (final analytic step toward the spectral triple, reusable for `T²` over `ℤ²`):
`IsCompactOperator (diracDirac.resolvent Complex.I)`. Now de-risked — Mathlib has
`isCompactOperator_of_tendsto` (compact operators are operator-norm-closed) and
`isCompactOperator_of_locallyCompactSpace_rng` (finite-dim range ⇒ compact). Plan:
1. build the bounded diagonal resolvent `R : L2 →L[ℂ] L2`, `(R b)ₙ = bₙ / (i - n)` (‖·‖ ≤ 1);
2. truncations `R_N` (zero outside `|n| ≤ N`) are finite-rank, hence compact;
3. `R_N → R` in operator norm since `1/(i - n) → 0`, so `R` is compact by the limit lemma;
4. identify `diracDirac.resolvent Complex.I = R` (it is the inverse of `i • 1 - D`).
Then `IsOddSpectralTriple.toIsFinitelySummableSpectralTriple` assembles the triple at `z = i`,
using `diracDirac_isSelfAdjoint` and `mem_resolventSet_I`. -/

end SpectralTriples.Circle
