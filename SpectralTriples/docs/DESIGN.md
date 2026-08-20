---
title: "Spectral Triples and the Index Pairing"
subtitle: "Formalization design — see PLAN.md for current implementation status"
author: "Project notes"
date: "2026-08-20"
geometry: margin=1in
fontsize: 11pt
monofont: "Menlo"
header-includes:
  - \usepackage{amsmath,amssymb,amsthm}
  - \usepackage{mathtools}
  - \def\C{\mathbb{C}}
  - \def\R{\mathbb{R}}
  - \def\Z{\mathbb{Z}}
  - \def\N{\mathbb{N}}
  - \def\Q{\mathbb{Q}}
  - \def\H{\mathcal{H}}
  - \def\B{\mathcal{B}}
  - \def\K{\mathcal{K}}
  - \def\A{\mathcal{A}}
  - \def\D{D}
  - \DeclareMathOperator{\ind}{ind}
  - \DeclareMathOperator{\Tr}{Tr}
  - \DeclareMathOperator{\dom}{dom}
---

# 1. Goal

`DESIGN.md` is the source document for this roadmap; `DESIGN.tex` is a generated
presentation artifact and must be kept synchronized with it. Status claims name a Lean
declaration when they describe a formalized result. Unqualified index-theorem statements
are classical targets, not claims about the present codebase.

Formalize, in Lean 4 with Mathlib, the following triad of objects and the
relations between them:

(a) the abstract notion of a **$Z_2$-graded spectral triple**
    $(\A, \H, \D, \gamma)$,
(b) the **Fredholm index pairing**
    $\bigl\langle [\D],\,[p]\bigr\rangle = \ind\bigl(p \D^+ p\bigr) \in \Z$
    of an even spectral triple with a projection $p \in \A$,
(c) the **canonical spectral triple of a closed Riemannian spin manifold**
    $(M, g)$, i.e. the triple
    $\bigl(C^{\infty}(M),\, L^2(S),\, \D_M,\, \gamma_M\bigr)$
    built from the spinor bundle $S \to M$ and the Dirac operator $\D_M$.

The mathematical content is classical (Connes 1994; GBF 2001;
Higson--Roe 2000). The intended contribution is a Lean encoding and eventual
*machine-checked* verification that the manifold construction satisfies the abstract
axioms; the current implementation has reached the abstract core and Fourier models, not
the general manifold construction.

## 1.1 Motivation: why both an algebra $\A$ and a Hilbert space $\H$?

The bipartite data $(\A, \H, D)$ encodes a deliberate split: $\A$ carries
the *topology* (what the space looks like), and $\H$ together with $D$
carries the *calculus* (how to differentiate and measure on it). Each
half alone is too featureless to recover geometry; the spectral triple
is their collision.

**Algebra alone is too rubbery.** By Gelfand--Naimark a commutative
$C^*$-algebra fully determines a (locally compact Hausdorff) topological
space, but topology cannot see distances, angles, or volumes: $C(X)$
does not distinguish a unit sphere from a sphere of radius 100. And on
a generic noncommutative algebra there are no nontrivial outer
derivations at all, so the very notion of "differentiating an element
of $\A$" is absent from $\A$ alone.

**Hilbert space alone is amnesiac.** Every separable infinite-dimensional
Hilbert space is unitarily isomorphic to $\ell^2(\N)$: $L^2(S^2)$ and
$L^2(T^2)$ are indistinguishable as Hilbert spaces. Adding a self-adjoint
operator $D$ does not fix this — by Milnor (1964) and the negative
answer to Kac's "Can one hear the shape of a drum?"
(Gordon--Webb--Wolpert 1992), isospectral non-isometric manifolds exist.
The spectrum of $D$ alone misses the manifold.

**The representation $\pi$ localises.** A $*$-representation
$\pi\colon \A \to \B(\H)$ breaks the universality of $\H$ by anchoring
it to the topological shape recorded by $\A$. For the canonical Dirac
triple, $(\pi(f)\psi)(x) = f(x)\,\psi(x)$ is pointwise multiplication —
this is what lets a vector in $\H$ know *which point of $M$ it lives
over*. Connes' reconstruction theorem (1996; 2008 final form) makes this
precise: from $(\A, \H, D, \gamma)$ satisfying suitable additional
axioms, the smooth Riemannian spin manifold $M$ is recovered.

**The commutator is the derivative.** $D$ acts on $\H$, not on $\A$, so
$a \in \A$ cannot be differentiated by $D$ directly. But both $D$ and
$\pi(a)$ live in $\B(\H)$, so they can be multiplied; their commutator
$$
[D, \pi(a)]\,\psi \;=\; D(a\psi) - a\,(D\psi) \;=\; c(da)\,\psi
$$
*is* Clifford multiplication by $df$ in the canonical manifold case.
Boundedness of $[D, \pi(a)]$ (axiom (3) of §2.1) is the abstract
statement that "$a$ is Lipschitz." The derivative is born from the
failure of $\A$ to commute with $D$ — and that failure exists only
because both act on a common third object $\H$.

**The pairing: $\A$ asks, $\H + D$ answers.** A projection $p \in \A$
defines a K-theory class — a topological question ("does this bundle
have holes?"). The Fredholm index of $p D^+ p \colon p\H^+ \to p\H^-$ is
the analytic answer $\langle [D], [p]\rangle \in \Z$. Neither half
produces the integer alone: $\A$ supplies the topological lock,
$\H + D$ supplies the analytic key. This is the classical index pairing of §2.2.
The current Phase-2 code contains a generic bounded Fredholm index and a separate
`gradedKernelIndex`; the projection-compressed chiral pairing remains a roadmap item.

**Heisenberg's legacy.** Connes modelled the triple on the Heisenberg
picture of quantum mechanics: $\A =$ observables, $\H =$ states, $D =$
Hamiltonian. Just as QM needs all three together to mean anything,
"space" in noncommutative geometry is born from the interaction of $\A$
and $D$ on a common $\H$.

# 2. Mathematical content

## 2.1 Abstract $Z_2$-graded spectral triple

Let $\A$ be a unital $*$-algebra over $\C$ and $\H$ a separable complex
Hilbert space.

**Definition (Connes).** A *spectral triple* $(\A, \H, \D)$ consists of:

1. a $*$-representation $\pi \colon \A \to \B(\H)$ by bounded operators;
2. a self-adjoint operator $\D$ on $\H$ with dense domain $\dom \D$, such
   that $(\D + i)^{-1} \in \K(\H)$ (compact resolvent);
3. for every $a \in \A$, $\pi(a)\,\dom \D \subseteq \dom \D$ and the
   commutator
   $[\D, \pi(a)]\colon \dom \D \to \H$
   extends to a bounded operator on $\H$.

The triple is **$Z_2$-graded** (or *even*) if there exists a bounded
self-adjoint involution $\gamma\colon \H \to \H$ (i.e. $\gamma^* = \gamma$
and $\gamma^2 = 1$) with

$$
[\gamma,\pi(a)] = 0 \quad \forall\,a \in \A,
\qquad
\gamma\,\D + \D\,\gamma = 0.
$$

The grading splits $\H = \H^+ \oplus \H^-$ into the $\pm 1$ eigenspaces of
$\gamma$. The representation $\pi$ preserves each summand; $\D$ exchanges
them. Writing
$\D = \begin{pmatrix} 0 & \D^- \\ \D^+ & 0 \end{pmatrix}$
with respect to the splitting, self-adjointness of $\D$ gives
$\D^- = (\D^+)^*$.

## 2.2 Index pairing

Let $(\A, \H, \D, \gamma)$ be a $Z_2$-graded spectral triple and let
$p = p^* = p^2 \in \A$ be a projection.

**Classical theorem (Connes; formalization target).** The operator
$p \D^+ p \colon p\H^+ \to p\H^-$ is Fredholm, and its index depends only
on the class $[p] \in K_0(\A)$ (K-theory of the algebra) and on the
class $[\D] \in K^0(\A)$ (even analytic K-homology). The pairing
$$
\bigl\langle [\D],\,[p]\bigr\rangle
\;:=\; \ind\bigl(p \D^+ p\bigr)
\;=\; \dim\ker\bigl(p \D^+ p\bigr) \;-\; \dim\operatorname{coker}\bigl(p \D^+ p\bigr)
\;\in\; \Z
$$
is bilinear and additive. Self-adjointness of $\D$ identifies the
cokernel with $\operatorname{coker}(p \D^+ p) \cong \ker(p \D^- p)$ as a
subspace of $p\H^-$, since $(p\D^+ p)^* = p \D^- p$ under the splitting
$\H = \H^+ \oplus \H^-$ (see §2.1).

Fredholmness reduces to two facts:

* $p \D^+ p$ has a parametrix modulo compacts, built from
  $(\D + i)^{-1}$ (compact by the resolvent axiom) and the bounded
  commutator $[\D, \pi(p)]$ (bounded by the commutator axiom);
* compact resolvent + bounded commutator $\Rightarrow$ compactness of
  the remainder term, so Atkinson's theorem applies.

**Bounded form.** Replace $\D$ by $F := \D\,(1 + \D^2)^{-1/2}$ (the
*bounded transform* of $\D$). Then $F$ is bounded self-adjoint,
$F^2 - 1$ and $[F, \pi(a)]$ are compact for every $a \in \A$, and the
pairing reads
$$
\bigl\langle [F],\,[p]\bigr\rangle
\;=\; \ind\bigl(p F^+ p\colon p\H^+ \to p\H^-\bigr) \in \Z.
$$
Here $F^+\colon \H^+ \to \H^-$ is the off-diagonal block of $F$ under
the $\gamma$-grading. The two pictures give the same integer (GBF §9.4).

**Present Lean boundary.** `Fredholm.lean` defines the Fredholm predicate and index for
bounded linear maps, while `Index.lean` defines `gradedKernelIndex` for the full
self-adjoint unbounded operator and proves its kernel finite-dimensional under compact
resolvent. The repository does not yet define the chiral restriction $D^+$ or prove it
Fredholm, does not construct $pD^+p$, and does not prove that `gradedKernelIndex` equals
the classical chiral Fredholm index. Those are distinct Phase-2 deliverables.

## 2.3 Canonical spectral triple of a Riemannian spin manifold

Let $(M, g)$ be a closed Riemannian manifold of dimension $n$, equipped
with a spin structure. The construction proceeds in stages.

**(i) Clifford algebra and spinor bundle.** The cotangent bundle
$T^*M$ together with $g$ gives a Clifford bundle $\mathrm{Cl}(T^*M)$
whose fibre $\mathrm{Cl}_n$ is generated by $T^*_x M$ with relations
$v \cdot w + w \cdot v = -2 g(v, w)$. A **spin structure** on $M$ is a
principal $\mathrm{Spin}(n)$-bundle $P_{\mathrm{Spin}} \to M$ together
with a double cover $P_{\mathrm{Spin}} \to P_{\mathrm{SO}}$ of the
oriented orthonormal frame bundle, equivariant for the standard double
cover $\mathrm{Spin}(n) \to \mathrm{SO}(n)$. Such a lift exists iff
the second Stiefel--Whitney class $w_2(M) \in H^2(M; \Z/2)$ vanishes;
when it does, the set of spin structures is a torsor over
$H^1(M; \Z/2)$.

Associated to the standard complex spinor representation
$\sigma\colon \mathrm{Cl}_n \otimes_{\R} \C \to \mathrm{End}(\Sigma_n)$
(irreducible of dimension $2^{\lfloor n/2 \rfloor}$; unique for $n$
even, two inequivalent choices distinguished by $\sigma(\omega) = \pm 1$
for $n$ odd), one obtains the **spinor bundle**
$$
S \;:=\; P_{\mathrm{Spin}} \times_{\mathrm{Spin}(n)} \Sigma_n
\;\longrightarrow\; M.
$$
Pointwise Clifford multiplication $c\colon T^*M \otimes S \to S$ is
fibrewise the action $\sigma$.

**(ii) Hilbert space.** With the Riemannian volume form, define
$\H := L^2(M, S)$, the completion of smooth compactly supported sections
$C_c^{\infty}(M, S)$ under
$\langle \psi, \varphi\rangle := \int_M \langle \psi(x), \varphi(x)\rangle_{S_x}\,d\mathrm{vol}_g(x)$.

**(iii) Algebra and representation.** Let $\A := C^{\infty}(M)$ act on
$\H$ by pointwise multiplication: $(\pi(f)\psi)(x) := f(x)\,\psi(x)$.

**(iv) Dirac operator.** The Levi--Civita connection on $TM$ lifts to a
connection $\nabla^S$ on $S$. The Dirac operator is
$$
\D_M \;:=\; c \circ \nabla^S
\;\colon\; \Gamma(S) \to \Gamma(S),
$$
in local coordinates $\D_M = \sum_i c(e^i)\,\nabla^S_{e_i}$
for any local orthonormal frame $(e_i)$ with dual coframe $(e^i)$.

**(v) Grading (when $n$ is even).** In even dimension the spinor
representation splits as
$\Sigma_n = \Sigma_n^+ \oplus \Sigma_n^-$ under the **chirality element**
$$
\gamma_M \;:=\; i^{n/2}\, c(e^1) c(e^2) \cdots c(e^n),
$$
which is self-adjoint, squares to $1$, commutes with even Clifford
elements, anti-commutes with odd ones. Hence $\gamma_M$ commutes with
$\pi(f)$ (a function is a degree-$0$ object) and anti-commutes with $\D_M$
(which is degree-$1$).

**Theorem (canonical triple).** With the above data,
$(C^{\infty}(M), L^2(M,S), \D_M, \gamma_M)$ is a $Z_2$-graded spectral
triple. Specifically (writing $\D_M$ for both the symmetric operator on
$C_c^\infty(M, S)$ and its closure):

* $\D_M$ is essentially self-adjoint on $C_c^{\infty}(M,S)$ — closed
  $M$ is geodesically complete, so Chernoff's theorem applies. We
  identify $\D_M$ with its self-adjoint closure throughout.
* $(\D_M + i)^{-1}$ is compact, by Rellich--Kondrachov: the inclusion
  $H^1(M,S) \hookrightarrow L^2(M,S)$ is compact for compact $M$, and
  $(\D_M + i)^{-1}$ factors through this inclusion since
  $(\D_M + i)^{-1}\colon L^2 \to H^1$ is bounded by elliptic regularity.
* For $f \in C^{\infty}(M)$, the commutator
  $[\D_M, \pi(f)]\colon C_c^\infty(M, S) \to C_c^\infty(M, S)$ equals
  $c(df)$, pointwise Clifford multiplication by the (bounded smooth)
  one-form $df$. It extends by boundedness to all of $L^2(M, S)$ with
  operator norm $\|df\|_{\infty}$ (the sup norm of $df$ in the metric
  induced by $g$).
* $\gamma_M$ commutes with $\pi(C^{\infty}(M))$ (functions are degree-0
  Clifford elements) and anti-commutes with $\D_M$ (which is degree-1).

Atiyah--Singer specializes the index pairing: for a Hermitian vector
bundle $E \to M$ with projection $p_E$ encoding $E$, the index
$\langle [\D_M], [p_E] \rangle = \ind(\D_E^+)$ where $\D_E$ is the
twisted Dirac operator, equal to the topological index of $E$
(Â-genus times Chern character).

## 2.4 Generalizations: equivariance and families

The framework admits two important extensions, both well established in
the literature and both fitting naturally on top of the abstract
$Z_2$-graded spectral triple of §2.1.

**Equivariance.** Let $G$ be a locally compact group acting on $\A$ by
$*$-automorphisms $\sigma\colon G \to \mathrm{Aut}(\A)$. A
*$G$-equivariant* (graded) spectral triple adds a strongly-continuous
unitary representation $U\colon G \to \mathcal{U}(\H)$ satisfying the
covariance condition
$$
U(g)\,\pi(a)\,U(g)^* = \pi\!\bigl(\sigma_g(a)\bigr)
\qquad \forall\, g \in G,\ a \in \A,
$$
together with $U(g)\D = \D U(g)$ and (in the graded case)
$U(g)\gamma = \gamma U(g)$ for every $g$. For **compact** $G$ the index
pairing refines to a homomorphism $K^G_0(\A) \to R(G)$ into the
representation ring of $G$; specializing at the trivial representation
recovers the integer index. For non-compact $G$ one works with the
$K$-theory of the reduced group $C^*$-algebra $K_0(C^*_r(G))$ in place
of $R(G)$, via the Baum--Connes assembly map; this generality is out of
scope for the initial formalization.

Prototype examples: Atiyah--Singer for $G$-equivariant elliptic operators
on a $G$-manifold (with isometric $G$-action and $G$-invariant spin
structure); Connes--Moscovici's transverse fundamental class on a
foliation; spectral triples for quantum groups.

**Families.** Replace the Hilbert space $\H$ with a **Hilbert
$C^*$-module** $\mathcal{E}$ over a $C^*$-algebra $B$ (think $B = C(X)$
for a compact Hausdorff base $X$, so that $\mathcal{E}$ is the section
space of a continuous field of Hilbert spaces over $X$). The
representation $\pi$ now takes values in the adjointable $B$-linear
operators $\mathcal{L}_B(\mathcal{E})$, and "compact resolvent" means
$(\D + i)^{-1} \in \mathcal{K}_B(\mathcal{E})$, the $B$-compact operators
(the closed two-sided ideal generated by the rank-one $B$-linear maps
$\theta_{\xi,\eta}(\zeta) := \xi\,\langle \eta, \zeta\rangle_B$).

This is precisely an **unbounded Kasparov $(\A, B)$-bimodule**; the
bounded form (replace $\D$ by $F$) is Kasparov's original definition.
The index lifts to a class in $K_0(B)$; for $B = C(X)$ this recovers the
Atiyah--Singer family index theorem. The whole programme sits inside
**Kasparov's bivariant K-theory** $KK(\A, B)$, and our current setting is
the special case $B = \C$ (where $K_0(\C) = \Z$).

The two extensions combine: $G$-equivariant families give classes in
$KK^G(\A, B)$, encompassing equivariant family index theorems.

## 2.5 Super-Bakry--Émery curvature

A spectral triple comes with enough structure to support a synthetic
**Ricci-curvature lower bound** in the sense of Bakry--Émery, adapted to
the Z₂-graded setting. The generator is $L := D^2$ (positive, self-adjoint
on $\H$); the "gradient" is the noncommutative derivative
$\delta(a) := [D, a]$, an odd derivation $\A \to \B(\H)$.

**Carré du champ.** Define
$$
\Gamma(a, b) \;:=\; \tfrac{1}{2}\bigl(\delta(a)^*\,\delta(b) + \delta(b^*)\,\delta(a^*)^*\bigr)
\qquad (a, b \in \A),
$$
a sesquilinear form valued in $\B(\H)$ (Cipriani--Sauvageot; agrees with
$\Gamma(a, b) = \tfrac{1}{2}(L(a^*b) - a^*\,Lb - (La^*)\,b)$ when $\A$ acts as
multiplication operators and $L$ is a Markov generator). The
**iterated carré du champ** is
$$
\Gamma_2(a, b) \;:=\; \tfrac{1}{2}\bigl(L\,\Gamma(a, b) - \Gamma(a, Lb) - \Gamma(La, b)\bigr).
$$
For real $\A$ and self-adjoint $a$, $\Gamma(a, a) \geq 0$ in the operator
order.

**Super-$CD(\rho, \infty)$ condition.** The spectral triple satisfies
super-Bakry--Émery curvature $\geq \rho \in \R$ if
$$
\Gamma_2(a, a) \;\geq\; \rho\,\Gamma(a, a) \qquad \forall\,a \in \A
$$
in the operator-ordering sense (positive operator inequality on $\H$).
The "super" qualifier marks two non-classical features: the generator
is $L = D^2$ with $D$ odd (Dirac-type), and the underlying space is
Z₂-graded by $\gamma$.

**Equivalent gradient-decay form** (used in `graphops-qft`). Let
$P_t := e^{-tL}$ be the heat semigroup. The $CD(\rho, \infty)$ inequality
is equivalent to
$$
\Gamma(P_t a,\,P_t a) \;\leq\; e^{-2\rho t}\,P_t\bigl(\Gamma(a, a)\bigr)
\qquad \forall\, t \geq 0,\ a \in \A.
$$
Equivalently in expectation: $\|\nabla P_t a\|^2 \leq e^{-2\rho t}\,P_t \|\nabla a\|^2$
where $\|\nabla a\|^2 := \Gamma(a, a)$ understood as an $\H$-bilinear form.

**Specialization to the canonical Dirac triple.** Via the
**Lichnerowicz formula**
$$
D^2 \;=\; \nabla^{S\,*}\nabla^S \,+\, \tfrac{1}{4} R_{\mathrm{scal}}(g),
$$
combined with the Bochner formula for the rough Laplacian, the
Bakry--Émery $CD$ inequality for the canonical Dirac spectral triple of
a closed Riemannian spin manifold $(M, g)$ reduces to a pointwise lower
bound on $\mathrm{Ric}_g$. Concretely: $\mathrm{Ric}_g \geq K$ pointwise
implies super-$CD(K/4, \infty)$ for the spectral triple. The factor
$1/4$ is the Lichnerowicz coefficient.

**Bridge to `graphops-qft`.** The `SusyGraphop` `(H₊, H₋, Q)` of
`graphops-qft` is exactly a finite-dimensional Fredholm module with
$Q$ playing the role of $F$ (legal since $F = Q$ in finite dimension —
the bounded transform is the identity up to scaling). The gradient
$\nabla = Q$ (acting $C^0 \to C^1$ on a graph) is the supercharge; the
super-BE curvature defined there agrees with the carré-du-champ form
above with $L = Q^2$ on the even side. So the spectral-triples project
contains `graphops-qft`'s finite case as an instance of a graded
Fredholm module; integrating super-BE here gives both frameworks a
common abstraction.

## 2.6 Other instances of the framework

*Extra, not core.* The abstract data of an even graded Fredholm module
$(\A, \H = \H^+ \oplus \H^-, F, \gamma)$ — equivalently a pair of
Hilbert spaces with an odd operator $Q$ between them — has several
classical instantiations beyond the Dirac case of §2.3. Each comes with
its own deformation parameter or extra structure; in each, the index
pairing reduces to a familiar topological invariant.

**Hodge--de Rham (the signature/Euler operator).** Take
$\H = L^2(\Lambda^* M)$ (square-integrable forms of all degrees) on a
closed oriented Riemannian manifold, $\gamma = (-1)^{\deg}$ for the
Euler operator (or the Hodge-$*$ chirality for the signature operator),
and $D = d + d^*$. The Witten index $\dim\ker D|_{\mathrm{even}} -
\dim\ker D|_{\mathrm{odd}}$ recovers the Euler characteristic
$\chi(M) = \sum (-1)^k \beta_k$ (resp. the signature $\sigma(M)$ in the
oriented even-dim chirality case).

**Witten--Morse deformation.** A Morse function $f \colon M \to \R$
defines a one-parameter family
$d_t \;:=\; e^{-tf}\,d\,e^{tf} \;=\; d \,+\, t\,df \wedge$
of deformations of $d$, hence a family of even graded Fredholm modules
$\bigl(C^\infty(M),\, L^2(\Lambda^*M),\, d_t + d_t^*,\, (-1)^{\deg}\bigr)$
for $t \in [0, \infty)$. The Witten Laplacian $\Delta_t := (d_t + d_t^*)^2$
agrees with the standard Hodge Laplacian at $t = 0$ and develops a
semiclassical large-$t$ asymptotic of the form
$\Delta_t \;\sim\; \Delta \,+\, t^2 |\nabla f|^2 \,+\, t\,(\mathcal{L}_{\nabla f} + \mathcal{L}_{\nabla f}^*)$
in which the potential $t^2 |\nabla f|^2$ confines low-energy
eigenfunctions to a shrinking neighbourhood of the critical points of
$f$ (Witten 1982; rigorous via Helffer--Sjöstrand 1985). The Witten
index is $t$-independent and equals $\chi(M)$; the count of low-energy
modes by Morse index gives the **Morse inequalities**; the
exponentially-small eigenvalues at large $t$ encode the **Morse complex
differential** (counted gradient flow lines, à la Floer/Bismut).

**Morse-complex limit as a finite `SusyGraphop`.** In the $t \to \infty$
limit the smooth Witten triple "collapses" onto a finite-dimensional
chain complex: one generator per critical point of $f$, graded by Morse
index, with differential given by flow-line counts. This finite complex
**is** a `SusyGraphop` in the sense of `graphops-qft`. So Witten--Morse
provides a *smooth* discrete-continuum bridge — complementing the
graph-approximation bridge — in which the same K-homology class is
represented by the smooth spectral triple ($t = 0$) and by the finite
Morse complex ($t = \infty$).

**Manifolds with boundary — deliberately out of scope.** On a
Riemannian manifold $M$ with $\partial M \neq \emptyset$, the Dirac
operator is not essentially self-adjoint, requiring a choice of
self-adjoint extension (APS, MIT-bag, Riemannian/Dirichlet, …) — each
giving a different operator with a different index. The
Atiyah--Patodi--Singer (1975) formula
$\mathrm{ind}(D_{\mathrm{APS}}^+) = \int_M \widehat{A}(M)\,\mathrm{ch}(E) - \tfrac{1}{2}(\eta(D_{\partial M}) + h(\partial M))$
introduces the non-local **eta-invariant**
$\eta(s) := \sum_{\lambda \neq 0} \mathrm{sgn}(\lambda)\,|\lambda|^{-s}$
of the boundary Dirac operator — a real (non-integer) spectral
asymmetry, requiring meromorphic continuation in $s$ and well outside
our K-theoretic / Fredholm setup. *In the bounded picture, the
operator-algebraic signature of the boundary obstruction is precisely
the failure of $F^2 - 1$ to be compact:* the boundary algebra
$C(\partial M)$ emerges as the cokernel modulo compacts (this is the
relative-K-homology setting of Forsyth--Mesland--Rennie 2019,
Goffeng--Mesland 2015, and the relative-K-homology / "spectral
triples with boundary" literature). We therefore *deliberately exclude*
manifolds with boundary from this project — the classical bounded Fredholm-module
condition $F^2-1\in\K(\H)$ enforces it. The closed-manifold
case is enough to formalize the index pairing and the canonical
construction; the APS framework is a separate project of comparable
scope.

**Hodge--Dolbeault.** For a complex manifold $(X, J)$,
$D = \overline{\partial} + \overline{\partial}^*$ on
$\H = L^2(\Lambda^{0,*})$ with $\gamma = (-1)^{q}$ on $\Lambda^{0,q}$
gives the Dolbeault spectral triple. Its index is the holomorphic
Euler characteristic $\chi(\mathcal{O}_X) = \sum (-1)^q h^{0,q}$; twisting by a
holomorphic vector bundle $E$ gives $\chi(E)$ via Hirzebruch--Riemann--Roch.
This is the framework specialization that underwrites our Phase 3.5
$T^2$ line-bundle test (where it reduces to Riemann--Roch on a genus-1
curve).

## 2.7 Connes' spectral distance

The data of a spectral triple supplies not only an *integer-valued* invariant
(the index pairing of §2.2) but also a *metric*. The mechanism: the
bounded commutator $[D, \pi(a)]$ is the noncommutative gradient of $a$,
and a noncommutative analogue of the classical formula
$d(x, y) = \sup\{|f(x) - f(y)| : \|\nabla f\|_\infty \leq 1\}$
yields a distance on the state space of $\A$.

**Definition (Connes).** Let $(\A, \H, D)$ be a spectral triple and let
$\mathcal{S}(\A)$ denote its state space (positive linear functionals
$\phi\colon \A \to \C$ of norm 1). The **spectral distance** is
$$
d_D(\phi, \psi) \;:=\; \sup\Bigl\{\,\bigl|\phi(a) - \psi(a)\bigr| \;:\; a \in \A,\ a = a^*,\ \bigl\|[D, \pi(a)]\bigr\|_{\B(\H)} \leq 1\,\Bigr\}
\qquad (\phi, \psi \in \mathcal{S}(\A)).
$$
It takes values in $[0, +\infty]$, defines an extended metric on
$\mathcal{S}(\A)$, and depends only on the gauge-equivalence class of $D$.

Three specializations:

* **Manifold (commutative case).** For the canonical Dirac triple of a
  closed Riemannian spin manifold $(M, g)$, the algebra is $\A = C^\infty(M)$
  and *pure states* are evaluation functionals $\delta_x(f) := f(x)$ for
  $x \in M$. Connes' theorem:
  $$d_D(\delta_x, \delta_y) \;=\; d_g(x, y) \qquad \forall\, x, y \in M,$$
  the Riemannian geodesic distance. This is the foundational result
  showing that spectral data $\bigl(C^\infty(M), L^2(S), D_M\bigr)$
  recovers the metric of $(M, g)$ — a key step toward Connes'
  reconstruction theorem.
* **Graph (commutative finite case).** For a finite graph viewed as a
  finite spectral triple (`graphops-qft` `SpectralTriple`, with
  $\A$ the algebra of functions on vertices and $D = d + d^*$), the spectral distance
  between vertex evaluation states equals the graph (shortest-path)
  distance. The condition $\|[D, f]\| \leq 1$ becomes
  $|f(x) - f(y)| \leq 1$ along edges — exactly the 1-Lipschitz
  condition for the combinatorial metric.
* **Noncommutative case (generalized Wasserstein).** For a genuinely
  noncommutative $\A$ — e.g., matrix algebras, group $C^*$-algebras of
  discrete groups, fuzzy spheres — the formula yields the **Connes--Rieffel
  metric** on $\mathcal{S}(\A)$, an analogue of the Wasserstein-1
  (earth-mover) distance. The Lipschitz seminorm
  $L(a) := \|[D, \pi(a)]\|$ plays the role of a Lipschitz constant,
  and $d_D$ is the dual transport distance for $L$. Rieffel (1999)
  identified the conditions on $L$ under which $d_D$ metrizes the
  weak-$*$ topology on $\mathcal{S}(\A)$ — a "compact quantum metric
  space" structure.

**Relation to the index pairing.** The two invariants extracted from
spectral data are complementary:

| Invariant | Type | Recovers in manifold case |
|-----------|------|---------------------------|
| Index pairing $\langle [D], [p]\rangle$ | Integer-valued, $\Z$ | Topological invariants (Â-genus, Chern numbers) |
| Spectral distance $d_D(\phi, \psi)$ | Metric on $\mathcal{S}(\A)$ | Riemannian geodesic distance |

Together they realize Connes' programme: every Riemannian (spin) manifold
is reconstructible from its spectral triple, with both the topology
(via $K$-homology) and the metric (via $d_D$) encoded in the spectral data.

**Formalization note.** Unlike the index pairing — which lives naturally
in the bounded $F$-picture — the spectral distance is intrinsically
tied to the *unbounded* $D$. In the bounded picture the commutator
$[F, \pi(a)]$ is *compact* (not bounded with controlled norm), so
$\|[F, \pi(a)]\|$ does **not** define the same Lipschitz seminorm; the
metric built from it generally differs from $d_D$. The needed unbounded commutator API is
now implemented on `IsOddSpectralTriple`: `domainRepresentation` and
`commutatorOnDomain` define the domain map, `exists_commutator_bound` proves a global
linear norm bound, and `boundedCommutator` is the canonical continuous extension, with
`boundedCommutator_apply` proving agreement on $\dom D$. Thus the distance can use
`hT.boundedCommutator a` directly; no parallel structure or extra extension axiom is
needed.

The definition itself is one line once the data is available:
$d_D(\phi, \psi) \;=\; \sup\{|\phi(a) - \psi(a)| : a^* = a,\quad
\|\texttt{hT.boundedCommutator a}\| \leq 1\}$.

## 2.8 Cyclic cohomology and the Chern--Connes character

A spectral triple represents a *K-homology class* of $\A$; the natural
algebraic dual to K-homology is **cyclic cohomology** $HC^*(\A)$
(Connes 1985). The image of the triple under this duality is the
**Chern--Connes character**
$$
\mathrm{ch}(D) \;\in\; HP^*(\A)
$$
in periodic cyclic cohomology. The Phase 2 index pairing factors
through it:
$$
\bigl\langle [D],\,[p]\bigr\rangle
\;=\; \bigl\langle \mathrm{ch}(D),\,\mathrm{ch}(p)\bigr\rangle,
$$
where $\mathrm{ch}(p) \in HC_*(\A)$ is the Chern character of the
projection on the K-theory side. Cyclic cohomology is precisely the
cohomological substrate that makes the integer pairing of §2.2 into a
Chern--Weil-style integration.

**Cyclic cohomology in short.** For a unital algebra $\A$ over $\C$,
the **Hochschild complex** $C^n(\A, \A^*) = \mathrm{Hom}(\A^{\otimes(n+1)}, \C)$
with coboundary $b$ computes Hochschild cohomology $HH^*(\A)$.
Restricting to cyclically-symmetric cochains and adjoining Connes' second
differential $B$ yields the $(b, B)$-bicomplex; its total cohomology is
**cyclic cohomology** $HC^*(\A)$. The periodicity operator $S$ stabilizes
the degree mod 2 and produces $\Z/2$-graded **periodic cyclic cohomology**
$HP^*(\A)$.

**Two presentations of $\mathrm{ch}(D)$.**

* **Connes' algebraic $(b, B)$-cocycle** (1985; finitely summable, purely
  algebraic). For a $(p+1)$-summable graded Fredholm module
  $(\A, \H, F, \gamma)$ with $p$ even,
  $$
  \tau_p(a_0, \dots, a_p)
  \;:=\; \lambda_p\,\mathrm{Tr}\bigl(\gamma\,F\,[F, \pi(a_0)]\,[F, \pi(a_1)]\,\cdots\,[F, \pi(a_p)]\bigr)
  $$
  (with $\lambda_p$ a normalization) is a cyclic $p$-cocycle on $\A$,
  and its class $[\tau_p] \in HC^p(\A)$ represents $\mathrm{ch}(D)$.
  Summability — $[F, \pi(a)]$ lies in the Schatten ideal
  $\mathcal{L}^{p+1}(\H)$ for every $a$ — replaces the dimension axiom of
  a smooth manifold. *Lives entirely on the classical bounded Fredholm-module layer;
  the corresponding Lean structure is planned, and no unbounded $D$ or heat semigroup
  is needed once that layer exists.*
* **JLO cocycle** (Jaffe--Lesniewski--Osterwalder 1988; entire,
  unbounded). For an unbounded $D$,
  $$
  \varphi_{2n}(a_0, \dots, a_{2n}) \;=\;
  \int_{\Delta_{2n}} \mathrm{Tr}\!\Bigl(\gamma\,\pi(a_0)\,e^{-s_0 D^2}\,[D, \pi(a_1)]\,e^{-s_1 D^2}\,\cdots\,[D, \pi(a_{2n})]\,e^{-s_{2n} D^2}\Bigr)\,ds
  $$
  on the standard $2n$-simplex $\Delta_{2n}$. The family
  $(\varphi_{2n})_n$ assembles to an **entire cyclic cocycle**
  representing $\mathrm{ch}(D)$. *Needs the heat semigroup $e^{-tD^2}$
  and hence the unbounded $D$; trades finite summability for entire-cyclic
  regularity.*

Both presentations represent the same class in $HP^*(\A)$ when both are
defined, and both deliver the same integer pairing with $K_0(\A)$.

**Manifold specialization --- HKR / Connes' theorem.** For
$\A = C^\infty(M)$ on a closed smooth manifold, the
**Hochschild--Kostant--Rosenberg theorem** (continuous version) gives
$HH^n(C^\infty(M)) \cong \Omega^n(M)$, and Connes' refinement promotes
this to the periodic cyclic statement
$$
HP^*\bigl(C^\infty(M)\bigr) \;\cong\; H^*_{\mathrm{dR}}(M;\, \C),
\qquad \text{$\Z/2$-graded by parity of degree.}
$$
Under this iso, $\mathrm{ch}(D_M)$ becomes the index density
$\widehat{A}(M) \in H^*_{\mathrm{dR}}(M;\C)$, and pairing with
$\mathrm{ch}(p_E)$ for a vector bundle $E$ recovers the Atiyah--Singer
integrand $\widehat{A}(M) \cup \mathrm{ch}(E)$. The square
$$
\begin{array}{ccc}
K_0(\A) \otimes K^0(\A) & \xrightarrow{\langle\cdot,\cdot\rangle} & \Z \\
\mathrm{ch}\otimes\mathrm{ch}\;\downarrow & & \downarrow \\
HP_*(\A) \otimes HP^*(\A) & \xrightarrow{\langle\cdot,\cdot\rangle} & \C
\end{array}
$$
commutes: the integer index lifts to a complex pairing that happens to
land in $\Z$ for spectral-triple data.

**Direct alternative on manifolds.** Cohomology of $M$ can also be
read off the *specific* Hodge--de Rham triple of §2.6: with
$\H = L^2(\Lambda^* M)$, $D = d + d^*$, $\gamma = (-1)^{\deg}$, Hodge
theory gives $\ker(D)|_{\Lambda^k} \cong H^k_{\mathrm{dR}}(M;\,\R)$.
This is concrete but tied to one specific triple, and is *not* the
NCG-native answer: it computes cohomology as a kernel of an operator
on forms rather than as a structure intrinsic to $\A$. The
cyclic-cohomology picture is the framework-level answer, computing
manifold cohomology as a derived invariant of $\A$ alone.

**Formalization route.** The algebraic $(b, B)$-cocycle is the natural
target: it lives entirely on the planned bounded Fredholm-module layer and requires no
unbounded-operator API, only Schatten-class membership of the
commutators. Cyclic cohomology of $\A$ itself is a purely algebraic
Hochschild-style construction. The JLO presentation and the HKR /
Connes iso to de Rham cohomology are heavier and defer to the
unbounded-API phase / Phase 4a respectively. See Phase 2.75 in §3.6
for the encoding plan.

## 2.9 Genuinely noncommutative instances

The framework's axioms (§2.1) are stated for an arbitrary unital
$*$-algebra $\A$; they do not require commutativity. Several classes of
genuinely noncommutative examples fit the implemented unbounded core and should fit the
planned bounded Fredholm-module layer without changing the algebra typeclasses of §3.2.

**Matrix algebras and finite triples.** $\A = M_n(\C)$ acting on
$\H = \C^n \otimes \C^n$ (or its $\Z/2$-graded version) gives the
simplest finite-dimensional even spectral triple. Two-point spaces and
finite-dimensional models for gauge theories (Connes--Lott; Chamseddine--Connes
spectral standard model) live in this class. These are also the cleanest
examples for testing the cyclic-cohomology Chern character of §2.8 in a
setting where all sums are finite.

**The noncommutative torus $A_\theta$.** For
$\theta \in [0, 1) \setminus \Q$, the **irrational rotation algebra**
$A_\theta$ is the universal $C^*$-algebra generated by unitaries $U, V$
with $UV = e^{2\pi i \theta}\,VU$; its smooth subalgebra
$A_\theta^\infty$ (rapid-decay Fourier coefficients) is the pre-$C^*$
algebra for the spectral triple. Connes (1980) constructs a canonical
even spectral triple
$(A_\theta^\infty,\, \H = \ell^2(\Z^2) \otimes \C^2,\, D, \gamma)$
modelled on the flat-torus Dirac operator: with $\tau(a) := a_{0,0}$
the unique trace, $\H$ is the GNS Hilbert space tensored with the
spinor representation, and $D = \delta_1 \otimes \sigma_1 + \delta_2 \otimes \sigma_2$
where $\delta_1, \delta_2$ are the canonical derivations dual to $U, V$.
Strikingly $D$ has the *same spectrum* as the flat $T^2$ Dirac
(Connes' isospectral deformation) — the geometry sees the deformation
only through the algebra, not through the eigenvalues.

The K-theory is $K_0(A_\theta) \cong \Z^2$ as an abstract abelian
group, while the **range of the trace** on projections is
$\tau\bigl(K_0(A_\theta)\bigr) = \Z + \theta\Z \subset \R$
(Pimsner--Voiculescu). The **Powers--Rieffel projection** $p_\theta \in A_\theta$
realizes $\tau(p_\theta) = \theta$, so the trace pairing
$\langle \tau, [p_\theta]\rangle = \theta \in \R \setminus \Q$
is **irrational**. This is a different pairing from the Fredholm pairing:

* pairing a K-homology/Fredholm class with $[p] \in K_0(A_\theta)$ always gives
  an integer; for the standard fundamental class and the Rieffel generator it gives
  the integral Chern number (up to the chosen orientation convention);
* pairing the degree-0 cyclic cocycle $\tau$ with the same K-theory class gives the
  real number $\tau(p)$, in particular $\theta$ for $p_\theta$.

Cyclic cohomology accommodates both the trace cocycle and the higher cocycle representing
the fundamental class, but it does not turn a Fredholm index into an irrational number.
The NC torus is valuable precisely because one K-theory class has complementary integer
Chern-number and real trace pairings.

**Group $C^*$-algebras.** For a finitely generated discrete group
$\Gamma$ with a proper length function $\ell\colon \Gamma \to \R_{\geq 0}$
(word length on a Cayley graph; restriction of a Lie-group norm), the
reduced $C^*$-algebra $C^*_r(\Gamma)$ has a spectral triple with
$\H = \ell^2(\Gamma)$, $\pi$ left convolution, and
$D\colon \delta_g \mapsto \ell(g)\,\delta_g$ the length operator.
Compact resolvent holds iff $\ell$ is **proper**:
$\#\{g : \ell(g) \leq R\} < \infty$. This is the basic input to the
Baum--Connes assembly map and to Connes--Moscovici's transverse
fundamental class for foliations.

**Quantum groups.** $C^*$-completions of $\mathcal{O}(SU_q(2))$, $\mathcal{O}(SU_q(n))$,
and Podleś quantum spheres carry spectral triples (Chakraborty--Pal;
Connes--Landi; Dąbrowski--Sitarz). These deform the canonical Dirac
triples of compact Lie groups / homogeneous spaces, and exhibit the
cyclic-cohomology refinement explicitly via twisted traces.

**Crossed products $\A \rtimes G$.** Classically, suitable equivariant Fredholm data can
be reorganized as non-equivariant data over a crossed product $\A \rtimes G$ (subject to
the usual covariance and completion hypotheses). This is the
algebraic mechanism by which equivariance is absorbed into a larger
noncommutative algebra; foliation $C^*$-algebras and mapping-torus
algebras arise this way.

**Fuzzy spheres.** $\A = M_n(\C)$ acting on a spin-$j$ representation of
$\mathfrak{su}(2)$ with $j = (n-1)/2$, equipped with a $D$ built from
$\mathfrak{su}(2)$ Casimirs, gives a sequence of finite-dimensional
spectral triples converging — in Rieffel's quantum Gromov--Hausdorff
sense (§6.6) — to the spectral triple of $S^2$ as $n \to \infty$. The
canonical *finite* test case for the continuum-limit programme; closer
to §6 stretch goals than to initial deliverables.

**Implications for the formalization.** None of these examples requires
changes to `Basic.lean`: its assumptions are `Semiring A`, `StarRing A`, and
`Algebra K A`; no `StarModule K A` instance is required.
The noncommutative torus is concrete enough — purely algebraic on
$\ell^2(\Z^2)$, no spin bundles, no Sobolev embedding — to formalize at
Phase 3 level; see Phase 3.6 in §3.6. Group $C^*$-algebras, quantum
groups, and fuzzy spheres are stretch goals comparable in scope to the
manifold construction.

# 3. Formalization design

## 3.1 Encoding choice: bounded vs unbounded D

The unbounded `LinearPMap` formulation is the implemented **spine**. Mathlib's adjoint,
closed-operator, and Hilbert-space APIs are sufficient for the core definition and the
resolvent arguments now in this repository. The bounded API is currently used for
explicit Fredholm operators; a general bounded-transform/Fredholm-module bridge is still
planned.

| Layer | Lean type / file | Status |
|---|---|---|
| spectral-triple core | `IsOddSpectralTriple`, `IsEvenSpectralTriple` / `Basic.lean` | done |
| resolvent definitions | `LinearPMap.resolventSet`, `resolvent` / `Resolvent.lean` | done |
| self-adjoint off-real-axis criterion | `IsSelfAdjoint.mem_resolventSet` / `CompactResolvent.lean` | done |
| compact-resolvent package | `IsCompactResolventSpectralTriple` / `CompactResolvent.lean` | done |
| bounded Fredholm predicate and index | `Fredholm.IsFredholm`, `Fredholm.index` / `Fredholm.lean` | done |
| compact perturbation result | `Fredholm.isFredholm_one_sub` / `CompactOperators.lean` | done |
| full-operator graded kernel invariant | `gradedKernelIndex` / `Index.lean` | done |
| chiral restriction and projection pairing | not yet defined | open |
| finite or `p`-summability | no Schatten/singular-value structure yet | open |

The old `FinitelySummable.lean` module is now a compatibility import, and
`IsFinitelySummableSpectralTriple` is a deprecated alias. Compact resolvent alone is
strictly weaker than finite or $p$-summability, so new code and documentation must use
`IsCompactResolventSpectralTriple` unless an actual Schatten-class decay condition is
added.

The remaining large bridge is the bounded transform
$F = D(1+D^2)^{-1/2}$ for an unbounded self-adjoint $D$. It needs functional calculus
and domain-sensitive results not supplied by the current code. Classically it preserves
the index pairing (GBF §9.4), but that equivalence is not yet a Lean theorem. The spectral
distance (§2.7) remains intrinsically unbounded and does not wait for this bridge.

## 3.2 Algebra category

We parametrize over `(K : Type*) [RCLike K]` (so the constructions work
over both $\R$ and $\C$) and an algebra
`(A : Type*) [Semiring A] [StarRing A] [Algebra K A]`.
The implemented core does not require a `StarModule K A` instance.

We deliberately do **not** require `A` to be a `C*`-algebra at this
level: the representation field
`π : A →⋆ₐ[K] (H →L[K] H)`
records a $*$-homomorphism into $\B(\H)$, which is the only place
boundedness of $\pi(a)$ enters. This matches Connes' "pre-$C^*$" stance:
$\A$ may be the dense subalgebra $C^\infty(M)$ of $C(M)$.

## 3.3 Hilbert space

`(H : Type*) [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]`.

Completeness is essential for compactness arguments. Separability is not
imposed at the type level (it is rarely needed in Mathlib formalizations
of operator theory and can be added when required).

## 3.4 Grading

The grading $\gamma$ is bounded, so it lives in `H →L[K] H`; the unbounded Dirac
operator is a separate parameter. `IsEvenSpectralTriple A D π γ` extends the odd core
with self-adjointness of $\gamma$, $\gamma^2=1$, commutation with $\pi(A)$, preservation
of `D.domain`, and domain-sensitive anticommutation with $D$. The code proves the
$\pm1$ eigenspace decomposition and that the grading preserves `Dkernel`.

A future bounded `IsEvenFredholmModule` may mirror this bundled design for a bounded
transform $F$, but no such structure exists in the present repository. In particular,
roadmap statements about $F^+$ or projection compression are not current API claims.

## 3.5 File structure

The checked-in Lean tree is:

```text
SpectralTriples.lean                       -- root re-export
SpectralTriples/
├── Basic.lean                             -- unbounded core + canonical bounded commutators
├── Resolvent.lean                         -- LinearPMap resolvent definitions
├── CompactResolvent.lean                  -- criterion and compact-resolvent package
├── FinitelySummable.lean                  -- deprecated compatibility import
├── Fredholm.lean                          -- bounded IsFredholm and integer index
├── CompactOperators.lean                  -- compact-adjoint and 1 − K Fredholm theory
├── Index.lean                             -- Dkernel and gradedKernelIndex
├── DiagonalOperator.lean                  -- block-diagonal ℓ² operators
├── FourierHolomorphic.lean                -- automorphic function-space dimension results
├── HermiteL2.lean                         -- normalized Hermite L² orthonormal family
└── Examples/
    ├── Circle.lean                        -- S¹ Fourier spectral triple
    ├── Shift.lean                         -- bounded unilateral shift Fredholm index
    ├── MagneticDirac.lean                 -- bounded magnetic phase and translations
    ├── ThetaSections.lean                 -- explicit automorphic theta sections
    └── Torus.lean                         -- flat T² Fourier spectral triple
```

Planned files such as `BoundedTransform.lean`, `Distance.lean`, `Cyclic.lean`,
`ChernCharacter.lean`, `Examples/TorusLineBundle.lean`, and the `Manifold/` hierarchy
are design targets; they are not shown in the checked-in tree and must not be cited as
implemented modules.

## 3.6 Phases

**Phase 1 — abstract definitions and compact resolvent. [DONE]** `Basic.lean` implements
the unbounded `IsOddSpectralTriple` / `IsEvenSpectralTriple` API: dense domain,
closedness, bounded commutator data, grading involution, domain preservation,
anticommutation, and the $\pm1$ eigenspace decomposition. `Resolvent.lean` supplies the
`LinearPMap` resolvent definitions. `CompactResolvent.lean` now proves the formerly open
basic criterion

$$
D=D^*,\quad \operatorname{Im}z\ne0 \quad\Longrightarrow\quad z\in\rho(D),
$$

including the bounded-below, closed-range, and dense-range steps, and packages compact
resolvent as `IsCompactResolventSpectralTriple`. Circle and torus instantiate this
structure. This phase establishes compact resolvent only, not $p$-summability.

**Phase 2 — Fredholm foundations and index pairing. [PARTIAL]** The following foundation
is implemented and checked:

- `Fredholm.IsFredholm f` records finite-dimensional kernel, closed range, and
  finite-dimensional quotient cokernel for a bounded linear map;
- `Fredholm.index f` is the kernel dimension minus quotient-cokernel dimension;
- `Fredholm.isFredholm_one_sub` proves the Riesz--Schauder result for `1 − K` with `K`
  compact;
- `finiteDimensional_Dkernel` proves finite-dimensionality of the kernel of a full
  self-adjoint operator with compact resolvent;
- `gradedKernelIndex D γ` is the difference between the $+1$ and $-1$ pieces of that
  full kernel;
- the unilateral shift and bounded magnetic phase have explicit `IsFredholm` and index
  theorems.

The name `gradedKernelIndex` is deliberate. It is not yet the Fredholm index of a
formalized chiral operator. The remaining Phase-2 work is to define the chiral spaces and
domain-restricted map $D^+ : H^+ \to H^-$ (or a rigorously connected bounded transform),
prove Fredholmness, define projection compression $pD^+p$, and prove agreement with the
graded-kernel formula. Direct sums, homotopy invariance, and K-theory descent follow only
after that operator is available. No fill-in partial isometry should be assumed without
proving its source/target defect dimensions and Fredholm properties.

**Phase 2.5 — Connes' spectral distance (see §2.7). [FOUNDATION DONE;
DISTANCE PLANNED]** This parallel invariant remains attached to the unbounded
spectral-triple core. `IsOddSpectralTriple.boundedCommutator` now supplies the canonical
bounded extension and `boundedCommutator_apply` proves its domain formula; the former
commutator-extension blocker is closed.

* Define `connesDistance (φ ψ : StateSpace A) : ℝ≥0∞` as the supremum
  of $|\phi(a) - \psi(a)|$ over self-adjoint $a \in \A$ with
  $\|\texttt{hT.boundedCommutator}\,a\| \leq 1$; do not add duplicate
  commutator data.
* Prove: the Connes distance on a commutative finite spectral triple
  (a graph, via the §3.9 `SusyGraphop` bridge) equals the
  shortest-path graph distance. This is the simplest non-trivial
  verification and re-validates the §3.9 bridge.
* (Goal, beyond initial scope.) Connes' theorem on the canonical Dirac
  triple: $d_D(\delta_x, \delta_y) = d_g(x, y)$ — geodesic distance
  recovery. Requires the manifold construction (Phase 4) and
  significant analytic work; flag as Phase 4 territory.

**Phase 2.75 — cyclic cohomology and the Chern--Connes character (see §2.8).**
The cohomological dual to Phase 2: encode the cocycle on the algebra
side that the index pairing factors through.

* `Cyclic.lean`: build Hochschild cohomology $HH^*(\A)$ and cyclic
  cohomology $HC^*(\A)$ from the algebraic $(b, B)$-bicomplex of an
  arbitrary unital $*$-algebra; define the periodicity operator $S$
  and the $\Z/2$-graded periodic cyclic cohomology $HP^*(\A)$. Purely
  algebraic — Mathlib's cochain-complex and tensor-power infrastructure
  suffices.
* `ChernCharacter.lean`: on a genuinely *finitely-summable* graded
  Fredholm module (once that planned structure exists, parametrized by $p$ via an added Schatten-class
  axiom on $[F, \pi(a)]$), define the Connes $(b, B)$-cocycle $\tau_p$
  and prove it is a cyclic $p$-cocycle on $\A$. Define the K-theory
  Chern character $\mathrm{ch}(p) \in HC_*(\A)$ for a projection $p \in \A$.
  State and prove
  $$\bigl\langle [F],\,[p] \bigr\rangle \;=\; \bigl\langle \mathrm{ch}(F),\,\mathrm{ch}(p) \bigr\rangle,$$
  the factorization of the integer index pairing through cyclic cohomology.
* **Schatten ideals are partial in Mathlib.** A
  `pSummableFredholmModule p` extension carrying the axiom
  $[F, \pi(a)] \in \mathcal{L}^{p+1}(\H)$ for every $a$ is the cleanest
  design, but Schatten classes themselves are still being upstreamed
  (`Mathlib.Analysis.InnerProductSpace.Schatten`). Design Phase 2.75 to
  be parametric in that gap: require Schatten membership as an explicit theorem
  parameter or a centrally declared, policy-vetted interface. Do not use a local
  `sorry`/`admit` placeholder.
* **Deferred:** the JLO presentation (needs unbounded $D$ and the heat
  semigroup; out of scope until the unbounded-API phase) and the
  HKR / Connes iso $HP^*(C^\infty(M)) \cong H^*_{\mathrm{dR}}(M)$
  (needs smooth-form infrastructure; out of scope until Phase 4a / 5).

This phase is **algebraic-only**: zero unbounded analysis, zero
manifold tools. It states the framework's central structural theorem
— *the index pairing factors through the Chern--Connes character* — at
the level of generality of Phase 2, lifting the integer pairing to its
natural cohomological refinement.

**Phase 3 — example: the circle $S^1$. [CORE DONE]** `Examples/Circle.lean` builds the
Dirac triple directly from Fourier series. With $\H = \ell^2(\Z)$ (Fourier
basis of $L^2(S^1)$) and $\D = -i\,d/d\theta$ acting as the diagonal
operator $\delta_n \mapsto n\,\delta_n$, the spectrum is $\Z$, the implemented
resolvent $(i\,1-D)^{-1}$ is the diagonal operator with eigenvalues
$1/(i-n)$ (compact because $|1/(i-n)| \to 0$). The implemented algebra is the
star-subalgebra generated by the Fourier shift `W 1`, the operator image of the
trigonometric/Laurent polynomials; bounded commutators are proved on the generators and
propagated algebraically. The full classical $C^\infty(S^1)$ algebra is not bundled here.
This bypasses spin bundles, Sobolev compactness,
and Levi--Civita connections. The circle is also the natural
testbed for Phase 4.5 (the rotation action of $S^1$ on itself).
Caveat: $S^1$ is odd-dimensional, so the Dirac triple is *ungraded*
(no chirality $\gamma$) — it pairs with $K^1(\A)$, not $K_0(\A)$.
The index pairing here is the Toeplitz-type spectral-flow pairing rather
than the even pairing of Phase 2. `Examples/Shift.lean` separately proves that the
bounded unilateral forward shift is Fredholm with index $-1$; the repository has not yet
assembled that theorem into a K¹ pairing for the circle triple.

**Phase 3.5 — example: $T^2$ and a degree-$d$ line bundle. [PARTIAL]** The
flat torus $T^2 = \R^2/\Z^2$ with the trivial spin structure is the
simplest *even-dimensional* concrete Dirac triple, and the simplest
case where the index pairing produces a non-trivial, parameter-controlled
integer.

*Setup.* The spinor bundle on $T^2$ is rank 2 with both $S^\pm$ trivial
(since $TT^2$ is trivial). In the standard complex coordinate
$z = x_1 + i x_2$ the Dirac operator reduces to
$D^+ \cong 2\,\overline{\partial}\colon C^\infty(T^2) \to \Omega^{0,1}(T^2)$.
Concretely, at a nonzero Fourier mode $e^{2\pi i(m x_1 + n x_2)}$, the $2\times2$
Dirac block has the two simple eigenvalues $\pm2\pi\sqrt{m^2 + n^2}$.
$\H = L^2(T^2, S) \cong \ell^2(\Z^2; \C^2)$ carries these blocks diagonally.

*Untwisted index.* $\mathrm{ind}(D^+) = h^0(\mathcal{O}_{T^2}) - h^1(\mathcal{O}_{T^2})
= 1 - 1 = 0$ (genus-1 Hodge). Baseline.

*Twist by a line bundle $L$ of degree $d$.* On $T^2$, line bundles are
classified by $\mathrm{Pic}(T^2) \to H^2(T^2; \Z) \cong \Z$, with the
degree map $L \mapsto c_1(L)[T^2] = d$. The twisted Dirac
$D_L^+ \colon \Gamma(S^+ \otimes L) \to \Gamma(S^- \otimes L)$
satisfies Atiyah--Singer / Riemann--Roch:
$$
\mathrm{ind}(D_L^+) \;=\; \chi(L) \;=\; \deg L - g + 1 \;=\; d.
$$
This is the cleanest sanity check available for the index pairing:
a single integer, parametrized by $\Z$, computable in several independent
ways. The next paragraph spells out the framework-level computation.

*Classical worked computation: the index is $d$, three ways.* This subsection records
the target mathematics. Only the untwisted Fourier triple—using the star-subalgebra
generated by the two coordinate shifts, not the full $C^\infty(T^2)$ algebra—and the
supporting function/phase results identified below are currently formalized.

**Base spectral data.** With $\A = C^\infty(T^2)$,
$\H = L^2(T^2) \otimes \Sigma$ ($\Sigma = \C^2$),
$D = -i(\sigma_1\,\partial_1 + \sigma_2\,\partial_2)$, $\gamma = \sigma_3$.
Fourier diagonalises: $\H \cong \ell^2(\Z^2) \otimes \Sigma$, with $\pi(a)$
acting by convolution by the Fourier coefficients of $a$ and $D$ diagonal
on Fourier modes,
$$
D|_{(m, n)} \;=\; 2\pi \begin{pmatrix} 0 & m - in \\ m + in & 0 \end{pmatrix}
\quad \text{on } \Sigma.
$$
Classically, the bounded transform $F = D(1 + D^2)^{-1/2}$ has off-diagonal block
$F^+_{(m, n)} = 2\pi(m + in)/\sqrt{1 + 4\pi^2(m^2 + n^2)}$, vanishing only
at $(m, n) = (0, 0)$. The untwisted check is immediate:
$\ker F^+ = \ker F^- = \C$, so $\langle [F], [1]\rangle = 1 - 1 = 0$.

**Serre--Swan projection $p_d$ (TODO: construct from clutching data).** Present the
degree-$d$ line bundle first as the quotient of $[0,1]\times S^1\times\C$ by

$$
(1,y,z) \sim (0,y,e^{2\pi i d y}z).
$$

Choose a finite open cover $\{U_i\}$ of $T^2$, local frames, transition functions
$g_{ij}:U_i\cap U_j\to U(1)$ induced by this clutching map, and a subordinate smooth
partition of unity $\{\rho_i\}$. The standard Serre--Swan construction then gives an
$N\times N$ projection

$$
(p_d)_{ij}(x) = \sqrt{\rho_i(x)}\,g_{ij}(x)\,\sqrt{\rho_j(x)}.
$$

The cocycle identity and $\sum_i\rho_i=1$ prove $p_d^2=p_d$; unitarity of the transition
functions proves $p_d^*=p_d$. Its image bundle is isomorphic to the clutched line bundle,
whose first Chern number is $d$ after fixing the stated orientation/sign convention. The
Lean TODO is to choose an explicit cover and smooth
partition of unity, construct this finite matrix projection, and prove that bundle
identification and Chern number.

Do not reuse the earlier sine/cosine $2\times2$ formula: despite its apparent winding,
its image admits a periodic nowhere-zero global frame and hence represents degree zero.

**Compressed operator (not yet in Lean).** Amplify the Fredholm module to act on
$\H' := \H \otimes \C^N_{\mathrm{aux}}$ via $\pi_N := \pi \otimes \mathrm{id}_{M_N}$,
$F' := F \otimes 1_N$, $\gamma' := \gamma \otimes 1_N$. Let $P_d := \pi_N(p_d)$
— a bounded self-adjoint idempotent on $\H'$. The pairing is the
Fredholm index of the compression
$$
T_d^+ \;:=\; P_d\,(F^+ \otimes 1_N)\,P_d \;\colon\; P_d\,\H^{\prime,+} \to P_d\,\H^{\prime,-}.
$$
Serre--Swan identifies $P_d\,\H^{\prime,\pm} \cong L^2(T^2,\,L_d \otimes \Sigma^\pm)$,
and under this iso $T_d^+$ is the bounded transform of the twisted Dirac
$D_{L_d}^+ \colon L^2(T^2, L_d \otimes \Sigma^+) \to L^2(T^2, L_d \otimes \Sigma^-).$
The bounded transform preserves $\ker$, $\mathrm{coker}$, and the
Fredholm index, so
$$
\bigl\langle [F],\,[p_d] \bigr\rangle \;=\; \mathrm{ind}(T_d^+) \;=\; \mathrm{ind}(D_{L_d}^+).
$$

**Three independent computations of $d$.**

* **(i) Riemann--Roch.** $\mathrm{ind}(D_{L_d}^+) = \chi(L_d) = \deg L_d + 1 - g(T^2) = d + 1 - 1 = d$.
* **(ii) Aharonov--Casher / Landau levels.** Choose the
  constant-curvature connection on $L_d$, with curvature
  $F_{L_d} = 2\pi i d\,dx_1 \wedge dx_2$ (total flux $2\pi d$). The
  Lichnerowicz--Bochner identity on the flat $T^2$ specialises to
  $D_{L_d}^2 = \nabla^*\nabla - \pi d\,\sigma_3.$
  For $d > 0$: on $\Sigma^+$, $\ker$ requires $\nabla^*\nabla = \pi d$ —
  the lowest Landau level, with degeneracy exactly $d$; on $\Sigma^-$,
  $\ker$ would require $\nabla^*\nabla = -\pi d < 0$, impossible. Thus
  $\dim\ker D_{L_d}^+ = d$ and $\dim\ker D_{L_d}^- = 0$, giving
  $\mathrm{ind} = d$. The chiralities swap for $d < 0$ and the index is
  still $d$.
* **(iii) Chern--Connes character (Phase 2.75).** The degree-2 cyclic
  cocycle of the $T^2$ Fredholm module pairs with the K-theory Chern
  character of $p_d$ as
  $$
  \bigl\langle [F],\,[p_d] \bigr\rangle \;=\; \bigl\langle \mathrm{ch}_2(F),\,\mathrm{ch}_2(p_d) \bigr\rangle
  \;=\; \frac{1}{2\pi i}\int_{T^2} \mathrm{tr}\bigl(p_d\,dp_d \wedge dp_d\bigr)
  \;=\; c_1(L_d)[T^2] \;=\; d.
  $$
  The middle integral is the classical Chern--Weil formula for the
  first Chern class of the rank-1 image of a matrix-valued projection.
  The pairing factors literally through the de Rham class
  $c_1 \in H^2(T^2;\,\R)$ — Phase 2.75 in action on a manifold.

Three classical perspectives, same integer. **(ii)** is the direct operator-theoretic
target for `Examples/TorusLineBundle.lean`; **(iii)** is the longer-term Phase-2.75
target. Neither computation has been formalized, and both require an explicit bridge to
the geometric twisted operator.

*Status and deliverables.*

* **Done:** `Examples/Torus.lean` builds the untwisted unbounded even spectral triple on
  $\ell^2(\Z^2;\C^2)$, proves compact resolvent, and proves
  `isEvenSpectralTriple.gradedKernelIndex = 0`. This is not yet a compressed Fredholm
  pairing theorem.
* **Done, function-theoretic:** `Examples/ThetaSections.lean` and
  `FourierHolomorphic.lean` prove the explicit positive-degree sections, exact dimension
  $k$, and negative-degree holomorphic-section vanishing. They do not construct operator
  kernels or cokernels.
* **Done, bounded model:** `Examples/MagneticDirac.lean` proves the bounded phase
  `magneticPhase k` is Fredholm of index $k$. `HermiteL2.lean` proves the correctly
  normalized probabilists' Hermite functions
  $h_n(x)=H_n(x)e^{-x^2/4}/\sqrt{n!\sqrt{2\pi}}$ form an orthonormal family in
  $L^2(\R)$; completeness and a `HilbertBasis` remain open. The exponent is $-x^2/4$,
  because squaring produces the $e^{-x^2/2}$ orthogonality weight.
* **Open:** construct `Examples/TorusLineBundle.lean` from clutching data and a partition
  of unity, then build the weighted line-bundle `L²` space and twisted chiral operator.
* **Open:** identify the geometric chiral operator with the unbounded
  $\sqrt{n+1}$-weighted Landau lowering operator. Its bounded polar phase—not the weighted
  operator itself—should be identified with `magneticPhase k`. See `INDEX_PAIRING.md`.
* (Bonus) Bridge to `graphops-qft`: the square-lattice approximation
  of $T^2$ with a discrete $U(1)$ cocycle of holonomy class $d \in \Z$
  gives a SUSY graphop whose Witten index is also $d$. As the mesh
  refines, the two integers agree — a sanity check on the
  continuum-limit story.

This phase is the natural test bed for Phase 4.5 too (the $T^2 = S^1 \times S^1$
action gives an equivariant version with both index and equivariant
index computable).

**Phase 3.6 — example: the noncommutative torus $A_\theta$ (see §2.9). [PLANNED]**
The canonical genuinely noncommutative test case. It should exhibit two different
pairings on the same K-theory: an integer Fredholm/Chern-number pairing and the
real-valued trace pairing.

*Setup.* Fix $\theta \in [0, 1) \setminus \Q$. Encode $A_\theta^\infty$
concretely as the algebra of rapid-decay sequences $a = (a_{m,n})_{(m,n) \in \Z^2}$
under the twisted convolution
$(ab)_{p,q} = \sum_{m, n} a_{m, n}\,b_{p-m,\,q-n}\,e^{2\pi i \theta\,n(p-m)}$.
The Hilbert space is $\H = \ell^2(\Z^2) \otimes \C^2$, the GNS
representation of the unique tracial state $\tau(a) = a_{0, 0}$ tensored
with the two-dimensional spinor representation. The derivations
$\delta_j$ act diagonally on Fourier modes:
$\delta_1(\delta_{m, n}) = 2\pi i m \delta_{m, n}$,
$\delta_2(\delta_{m, n}) = 2\pi i n \delta_{m, n}$. The Dirac is
$D = \delta_1 \otimes \sigma_1 + \delta_2 \otimes \sigma_2$, diagonal on
Fourier modes with eigenvalues $\pm 2\pi\sqrt{m^2 + n^2}$ — identical
to the flat $T^2$ Dirac spectrum (Connes' isospectral deformation).
The chirality is $\gamma = 1 \otimes \sigma_3$.

*Deliverables.*

* `Examples/NoncommutativeTorus.lean`: construct $A_\theta^\infty$ on
  rapid-decay $\Z^2$-sequences, the GNS representation on $\H$, the
  Dirac $D$, and chirality $\gamma$; first verify the unbounded
  `IsEvenSpectralTriple` and compact-resolvent structures. A bounded-transform theorem
  is a later bridge, not a prerequisite that already exists.
* Construct the **Powers--Rieffel projection** $p_\theta \in A_\theta$
  explicitly: $p_\theta = U^* f(V) + g(V) + f(V) U$ for smooth
  $f, g \in C^\infty(S^1)$ chosen so that $p_\theta^2 = p_\theta = p_\theta^*$
  and $\tau(p_\theta) = \theta$ (Rieffel 1981; explicit closed forms for
  $f, g$ in terms of bump functions).
* Verify $\tau(p_\theta) = \theta$. The cyclic-cohomology pairing
  $\langle [\tau], \mathrm{ch}(p_\theta) \rangle$ then equals
  $\tau(p_\theta) = \theta \in \R \setminus \Q$ — the irrational
  trace pairing.
* Construct the fundamental Fredholm/K-homology pairing separately and compute its
  integer Chern number on the Rieffel generator (with the orientation/sign convention
  stated explicitly). Do not identify this integer with the trace value $\theta$.

*Why it matters.* Fredholm indices remain integer-valued for noncommutative algebras.
What changes is the supply of other cyclic cocycles: the canonical trace induces
$K_0(A_\theta)\to\R$ with range $\Z+\theta\Z$, while the fundamental higher cocycle
extracts an integral Chern number. Phase 2.75 should encode both pairings and keep their
codomains and cocycles distinct.

*Mathlib gap.* This avoids spin bundles and Sobolev geometry, but it still requires a
rapid-decay algebra, twisted convolution, boundedness of its representation, and direct
compactness or Schatten estimates. None is currently a repository module. Schatten
claims must be proved from explicit estimates or carried as vetted hypotheses; compact
resolvent alone is not a substitute.

**Phase 3.7 — example: the Morse complex of $S^2$. _Extra, not core._**
A concrete instance of the Witten--Morse setup of §2.6, formalizable
without semiclassical analysis. Take $f \colon S^2 \to \R$ the height
function (two critical points: north pole $p_+$ of Morse index 2,
south pole $p_-$ of Morse index 0). The **Morse complex** is the
two-term chain complex $\Z\langle p_-\rangle \xrightarrow{0} \Z\langle p_+\rangle$
with zero differential (no flow lines connect critical points of equal
Morse index parity, and the indices differ by 2). Wrap it as a finite
`SusyGraphop` with $n_+ = 1$ (even = index-0 generator), $n_- = 0$
(odd = index-1 generators, none), giving $Q_+ = 0$ and Witten index =
$\dim\ker Q_+ - \dim\ker Q_- = 1 - 0 = 1$... wait — Morse complex of
$S^2$ has one generator each in degree 0 and 2 (both even); odd degree
(index 1) is empty. So the Witten index (= Euler char) is $1 + 1 = 2$
when we sum over even degrees correctly. Concretely, set $n_+ = 2$
(generators $\langle p_-, p_+\rangle$ in even degrees 0 and 2),
$n_- = 0$ (no odd generators), $Q_+ = 0$. Then Witten index = $2 - 0
= 2 = \chi(S^2)$. ✓

*Deliverables.*

* `Examples/MorseS2.lean`: construct the Morse complex of the height
  function on $S^2$ as a finite `SusyGraphop` (via the `graphops-qft`
  bridge of §3.9).
* Verify $\langle F, [1] \rangle = \chi(S^2) = 2$.
* Compare against the smooth Hodge--de Rham triple of $S^2$ at $t = 0$
  (which has $\dim \ker = h^0 + h^2 = 2$ on the even side, $h^1 = 0$
  on the odd side, so the index is also $2$). The point: two
  representatives of the same K-homology class — smooth ($t=0$) and
  finite ($t = \infty$ limit) — give the same integer.

This is a sanity check both for the Witten--Morse framework
description in §2.6 and for the `SusyGraphop` bridge in §3.9. It does
*not* require formalizing the $t \to \infty$ analysis itself — only the
combinatorial endpoint.

**Phase 4 — general manifold construction. [PLANNED]** Two sub-phases, which
should not be split into separate Lake targets but should be tackled in
order.

*Phase 4a — Mathlib lemmas for the spin construction.* Audit Mathlib
for what we need that may not exist yet:

* Spin group $\mathrm{Spin}(n)$ as a double cover of $\mathrm{SO}(n)$,
  with the universal property of lifting orthogonal frames.
* Complex spinor representation of $\mathrm{Cl}_n$.
* Levi--Civita connection on the spinor bundle, lifted from $TM$ via
  the local-frame formula
  $\nabla^S_X \psi = X(\psi) + \tfrac{1}{4}\sum_{i<j} g(\nabla_X e_i, e_j)\,c(e^i)c(e^j)\,\psi$.
* Sobolev sections $H^k(M, E)$ for vector bundles on a compact
  manifold, with **Rellich--Kondrachov compactness** of the inclusion
  $H^1(M, E) \hookrightarrow L^2(M, E)$.

For Rellich--Kondrachov in particular, thread the result as an explicit
`(rellichKondrachov : …)` theorem parameter until it is proved in Mathlib. If a global
axiom is ever unavoidable, it must be centralized, documented, and admitted by the
repository's axiom-vetting policy. A local `sorry` or `admit` is prohibited. The full
Mathlib proof requires substantial PDE infrastructure; the algebraic assembly can be
developed conditionally without obscuring that dependency.

Likely outcome: a separate library of supporting lemmas
(`Mathlib.Geometry.Manifold.Spin`?) suitable for upstreaming emerges
from this phase.

*Phase 4b — assembly.* Tie the pieces together in `Manifold/Canonical.lean`. First
produce an unbounded `IsEvenSpectralTriple` (or the odd version in odd dimension) and an
`IsCompactResolventSpectralTriple` using explicit Phase-4a hypotheses. Only after the
bounded-transform bridge exists should this be converted to a planned Fredholm-module
structure and a chiral pairing. The Phase-3 circle construction supplies a Fourier model
against which the unbounded assembly can be compared.

**Phase 4.5 — equivariance. [PLANNED]** Introduce an equivariant mixin over the relevant
unbounded or future bounded structure (see §3.8). The algebraic covariance data is
straightforward, but an equivariant chiral index depends on completing Phase 2: the
chiral Fredholm operator and its finite-dimensional kernel/cokernel are not yet in the
generic API.

*Why it's clean.* The unitary $U(g)$ commutes with $pF^+p$ by the
covariance axiom, so $\ker(pF^+p)$ and $\mathrm{coker}(pF^+p)$ are
$U(g)$-invariant. They are therefore finite-dimensional unitary
representations of $G$, not merely finite-dimensional vector spaces.
The pairing's codomain promotes from $\Z$ to the **representation
ring** $R(G)$ (for compact $G$):
$$
\mathrm{ind}_G(F) \;:=\; [\ker(pF^+p)] \,-\, [\mathrm{coker}(pF^+p)] \;\in\; R(G).
$$
Specializing the character at $g = 1$ recovers the integer index.

*Fixed-point localization (Atiyah--Segal--Singer 1968).* Evaluating
$\chi_{\mathrm{ind}_G(F)}(g) = \mathrm{Tr}(g\mid_{\ker}) - \mathrm{Tr}(g\mid_{\mathrm{coker}})$
gives a global analytic quantity that, by the
Atiyah--Segal--Singer fixed-point theorem, equals a *local* topological
sum over the fixed-point submanifold $M^g := \{x : g \cdot x = x\}$.
For isolated fixed points this collapses an infinite-dimensional
spectral computation to a finite sum of fractions. (Physics application:
the rigorous foundation of supersymmetric localization — path integrals
collapsing to finite instanton sums in SUSY field theory.) Formalizing
the full theorem is out of scope, but the *type-level* refinement
$\Z \rightsquigarrow R(G)$ is in scope and gives the framework for
stating it.

*Crossed-product perspective.* An equivariant spectral triple over $\A$
with $G$-action $\sigma$ is mathematically equivalent to a (non-equivariant)
spectral triple over the **crossed-product algebra** $\A \rtimes G$.
This is the NCG mechanism by which an algebra "knows" it carries a
group action — the equivariance is absorbed into a larger algebra.
Thus `EquivariantFredholmModule G σ` could equivalently be reformulated
as `IsOddFredholmModule ℂ (A ⋊[σ] G) H`; we choose the mixin form for
practical Lean ergonomics, but a `crossedProduct_equivalence` theorem
witnessing the two formulations as the same data is a natural Phase 4.5
deliverable.

*Worked example.* The rotation action $S^1 \curvearrowright S^1$
turns the Phase 3 Dirac triple into an $S^1$-equivariant one with
explicit Fourier-mode decomposition — the Fourier modes $\delta_n$
are the irreducible $S^1$-representations, so the equivariant index
lives in $R(S^1) = \Z[t, t^{-1}]$ and decomposes by Fourier weight.

*Mathlib support.* `Mathlib.RepresentationTheory.*` has finite group
representations, characters, and the representation ring as a Grothendieck
group; the formalization needs no new representation-theory plumbing
beyond what is already upstream.

*Non-compact $G$ — Baum--Connes territory.* The representation ring
$R(G)$ is defined for compact $G$; for non-compact $G$ the right
target is $K_0(C^*_r(G))$, the K-theory of the reduced group
$C^*$-algebra, via the Baum--Connes assembly map. This is out of
scope for the initial formalization but flagged here for completeness.

**Phase 4.75 — super-Bakry--Émery curvature (see §3.9). _Extra, not
core._** This phase is a stretch goal: none of the project's three
stated deliverables (abstract triple, Fredholm index pairing, canonical
Dirac triple) requires the super-$CD(\rho, \infty)$ machinery, and the
Lichnerowicz formula is not load-bearing for the canonical-triple
axioms (those reduce to Chernoff / Rellich--Kondrachov / local-frame
computations). Pursue Phase 4.75 only if (i) the `graphops-qft`
unification (§3.9 bridge) is itself a goal, or (ii) Phase 5
(heat-kernel route to the local index formula) becomes in-scope. Three
concrete deliverables once started:

* `BakryEmeryFredholmModule (ρ : ℝ) extends IsEvenFredholmModule`
  carrying the operator-ordering inequality $\Gamma_2(a, a) \geq \rho\,\Gamma(a, a)$,
  with $\Gamma, \Gamma_2$ defined via $\delta(a) = [F, \pi(a)]$ and
  $L = F^2$ in the bounded picture (or via $D$ once unbounded API
  arrives).
* Equivalence theorem: the operator $CD(\rho, \infty)$ inequality
  $\Leftrightarrow$ the gradient-decay form $\|\nabla P_t a\|^2 \leq
  e^{-2\rho t} P_t\|\nabla a\|^2$.
* Bridge `Bridge/SusyGraphop.lean`: a constructor
  `ofSusyGraphop : SusyGraphop → IsOddFredholmModule ℝ A H` exhibiting the
  finite graph case (`graphops-qft`) as an instance, with
  $\mathrm{Witten\,index} = \langle [F], [1] \rangle$.

The Lichnerowicz specialization (Phase 5 / Phase 4b territory):
`Ric_g ≥ K` ⇒ canonical Dirac triple satisfies
`BakryEmeryFredholmModule (K/4)`. Proving this on Mathlib requires the
Lichnerowicz identity for the spinor bundle, which goes through Phase
4a.

**Phase 5 — toward the local index formula.** Out of initial scope, but
worth scoping: Connes--Moscovici residue formula, requiring zeta
functions of $|D|^{-s}$ and the Wodzicki residue. Connection to Phase
4.75: the heat-kernel route to Atiyah--Singer (McKean--Singer, via
$\Tr(\gamma e^{-tD^2})$) uses the same Lichnerowicz formula that drives
the Phase 4.75 Ricci bound; both are downstream of the spin-bundle
Bochner formula.

**Phase 6 — families / Kasparov modules.** Generalize from Hilbert
spaces to Hilbert $C^*$-modules over a coefficient $C^*$-algebra $B$ (see
§3.8). Define `KasparovModule A B` in the bounded form, verify it
specializes to `IsOddFredholmModule` when $B = \C$, and lift the index pairing
to a homomorphism $K_0(\A) \to K_0(B)$. The Atiyah--Singer index theorem
for families (with $B = C(X)$) is the target. Prerequisite: Mathlib
support for Hilbert $C^*$-modules and the $\mathcal{K}_B(\mathcal{E})$
ideal is sufficient.

## 3.7 Risks and dependencies

| Risk                                            | Mitigation                                                              |
|-------------------------------------------------|-------------------------------------------------------------------------|
| Mathlib unbounded-operator API (revised)        | **Sufficient** for the core and compact resolvent (`Basic`/`Resolvent`/`CompactResolvent`); the off-real-axis criterion and its closed-range step are now proved. Functional calculus for the unbounded bounded transform $D \mapsto F$ remains the large gap and the general chiral pairing is still open |
| Spinor bundle / Dirac operator not in Mathlib   | Build a self-contained `Manifold/` sub-library; upstream candidates     |
| Rellich--Kondrachov in the required form        | Pass it as an explicit theorem hypothesis; any unavoidable global axiom must be centralized and policy-vetted. Local `sorry`/`admit` placeholders are prohibited |
| Sign / phase conventions diverge between GBF, Connes, Higson–Roe (e.g. orientation of $\gamma$, choice of $i$ in $D \mapsto F$) | Fix a single convention in `Basic.lean` docstrings; record translation tables to the other two references when relevant |
| Hilbert $C^*$-module / $\mathcal{K}_B$ API partial | Defer families to Phase 6; design Phase 1 to be parametric in `H` so the lift is local |

## 3.8 Generalizations: encoding equivariance and families

The two extensions of §2.4 differ sharply in formalization cost.

### Equivariance — cheap, add as a mixin

Define a structure parameterized by a topological group `G` together
with a continuous action on `A`:

```
structure EquivariantFredholmModule
    (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (σ : G →* (A ≃⋆ₐ[K] A))
    extends IsOddFredholmModule K A H where
  U : G →* (H ≃ₗᵢ[K] H)        -- unitary representation
  /-  Strong-operator-topology (SOT) continuity: g ↦ U(g) x is continuous
      for every x ∈ H. Operator-norm continuity is far too strong here —
      for the typical regular representation of an infinite group on
      L²(H) the orbit map is never norm-continuous (if it were, by
      Stone's theorem the infinitesimal generator would be bounded). -/
  U_continuous : ∀ x : H, Continuous (fun g : G => U g x)
  covariance   : ∀ g a, (U g : H →L[K] H) * π a = π (σ g a) * (U g)
  U_commutes_F : ∀ g, (U g : H →L[K] H) * F = F * (U g)
```

A graded variant adds `U_commutes_γ`. The analysis is unchanged from the
non-equivariant case: nothing is harder to prove; the new fields are
purely algebraic compatibility. Mathlib provides unitary groups,
continuous group homomorphisms, and strongly-continuous representations
(SOT continuity is exactly what Mathlib's `ContinuousSMul G H` records,
modulo unitarity), so this is a small layer. We will introduce it as
`Equivariant.lean` in Phase 4.5 *after* the index pairing of Phase 2
has stabilized.

### Families — heavy, defer but design for it

A "family of Fredholm modules over a coefficient $C^*$-algebra $B$" is a
Hilbert $C^*$-module $\mathcal{E}$ over $B$ together with a bounded
$B$-linear operator $F \in \mathcal{L}_B(\mathcal{E})$ satisfying the
Fredholm-module axioms with `IsCompactOperator` replaced by membership
in the $B$-compact ideal $\mathcal{K}_B(\mathcal{E})$.

Mathlib status (as of `v4.29.0-rc8`):

* `Mathlib.Analysis.CStarAlgebra.Module.*` — basic Hilbert $C^*$-module
  API exists.
* $\mathcal{L}_B(\mathcal{E})$ (adjointable operators) — partial.
* $\mathcal{K}_B(\mathcal{E})$ (the closed two-sided ideal generated by
  $\theta_{\xi,\eta}$) — not yet developed in usable form.
* Regular self-adjoint unbounded operators on $\mathcal{E}$ — absent.

**Forward compatibility.** The Phase 1 definitions in `Basic.lean` are
written with `H : Type*` plus typeclasses, *not* with $\C$ baked into the
analysis lemmas. To lift to families, the substitution will be:

| Single-space (current)                  | Families (Phase 6)                       |
|-----------------------------------------|------------------------------------------|
| `[InnerProductSpace K H] [CompleteSpace H]` | `[HilbertCStarModule B E]`           |
| `H →L[K] H`                             | `E →L[B] E` (adjointable $B$-linear)     |
| `IsCompactOperator (T : H →L[K] H)`     | `T ∈ 𝒦_B(E)` (the $B$-compact ideal)     |
| Index lands in `ℤ`                      | Index lands in `K₀(B)`                   |

The structural fields (one operator, three compactness axioms) and the
proof outline of the index pairing survive unchanged. The implementation
work for Phase 6 is the Mathlib gap — not a redesign of our structures.

### Combined: equivariant families

The full generality is a `G`-equivariant Kasparov $(\A, B)$-bimodule,
$KK^G(\A, B)$. Out of scope for this project. We list it for
completeness: once Phases 4.5 and 6 are in place, combining them is
formally a product (both add commuting layers of structure).

## 3.9 Super-Bakry--Émery: encoding sketch

The mathematical definitions are in §2.5; the encoding follows the
same mixin pattern as §3.8.

```
structure BakryEmeryFredholmModule (ρ : K) extends IsEvenFredholmModule K A H where
  /-  The carré du champ Γ(a, b) := ½ (δ(a)* δ(b) + δ(b*) δ(a*)*)
      with δ(a) := F * π a - π a * F. Returned as a bounded operator
      on H. -/
  Γ : A → A → H →L[K] H
  Γ_def : ∀ a b, Γ a b = ½ • ((δ a)* * δ b + (δ (star b)) * (δ (star a))*)
    where δ a := F * π a - π a * F
  /-  Iterated Γ via L = F². The factor convention matches §2.5. -/
  Γ₂ : A → A → H →L[K] H
  Γ₂_def : ∀ a b, Γ₂ a b = ½ • (L * Γ a b - Γ a (L_act b) - Γ (L_act a) b)
    where L := F * F
  /-  The CD(ρ, ∞) inequality: Γ₂(a, a) ≥ ρ • Γ(a, a) as a
      self-adjoint operator inequality. -/
  CD : ∀ a, Γ₂ a a - ρ • Γ a a ∈ {T : H →L[K] H | 0 ≤ T}
```

Three places this differs from a naive translation:

1. **`L_act` is the dual action of `L` on `A`** — not all $L = F^2$ has
   an action on $\A$ in the abstract setting. For commutative $\A$
   acting by multiplication, $L_act(a)$ is defined by the unique
   element $b \in \A$ with $\pi(b) = L \pi(a) - \pi(a) L - [L, \pi(a)]_+$ when
   such $b$ exists; otherwise the structure is formulated directly on
   the operator level (no action of $L$ on $\A$). For the canonical
   manifold case $L$ acts as the Laplacian on $\A = C^\infty(M)$, so
   this is fine.
2. **Operator-positivity** `0 ≤ T` is via Mathlib's
   `IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪x, T x⟫` (or the equivalent positive
   operator API in `Mathlib.Analysis.InnerProductSpace.Positive`).
3. **Equivalence theorem** (gradient-decay $\Leftrightarrow$ $CD$):
   stated as `theorem BakryEmeryFredholmModule.gradient_decay_iff_CD`.
   In the manifold case the proof goes via Lichnerowicz; abstractly via
   semigroup interpolation (Bakry's original argument).

### Bridge to `graphops-qft`

A finite `SusyGraphop` over $\R$ is essentially a finite-dimensional
graded Fredholm module after complexification:

```
def SusyGraphop.toFredholmModule (S : SusyGraphop) :
    IsOddFredholmModule ℂ (Matrix (Fin S.n_plus) (Fin S.n_plus) ℂ)
                   ((Fin S.n_plus → ℂ) × (Fin S.n_minus → ℂ)) where
  π := Matrix.toLin'   -- diagonal-matrix action on the first factor
  F := blockMatrix 0 S.Q_minus.cmap S.Q_plus.cmap 0
       |>.normalize    -- F := (something)·Q with appropriate scaling
  ...
```

with the grading $\gamma := \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$
on the direct sum. The Witten index of `graphops-qft` then coincides
with our index pairing at $[p] = [1] \in K_0(\A)$ (the unit projection):
$\langle [F], [1] \rangle = \dim \ker Q_+ - \dim \ker Q_- =
\mathrm{Witten}(S)$.

This bridge unifies the two projects under one abstraction: any theorem
about `BakryEmeryFredholmModule` specializes to a theorem about
`SusyGraphop` via `toFredholmModule`, and vice versa for theorems
specific to the finite case.

# 4. Notation conventions

Internal to the formalization we use:

* `K` — base field (`ℝ` or `ℂ`).
* `A` — the algebra (in math: $\A$).
* `H` — the Hilbert space (in math: $\H$).
* `π` — the representation.
* `F` — the bounded operator (Fredholm-module form).
* `D` — the unbounded Dirac-type operator (spectral-triple form).
* `γ` — the chirality / grading.

For manifold-specific objects we add a subscript `M`:
`D_M`, `γ_M`, `H_M = L^2(M, S)`.

# 5. Resolved decisions

The five questions in the original draft are answered below.

1. **Unbounded operators — yes for the spine (revised 2026-08-20).** The core,
   resolvent theory, the off-real-axis self-adjoint criterion, and compact-resolvent
   package are implemented on `LinearPMap` $D$. This is not a finite-summability result.
   The bounded transform $D \mapsto F = D(1+D^2)^{-1/2}$ still needs additional
   functional calculus. Phase 2 currently supplies a generic bounded Fredholm API and
   explicit examples, not a general `IsOddFredholmModule` or chiral pairing. See §3.1.
2. **Algebra category — `StarRing ℂ A` + `Algebra ℂ A`, not
   `CStarAlgebra`.** Demanding $C^*$-completeness would exclude
   $C^\infty(M)$ (which is Fréchet, not $C^*$) and break the canonical
   manifold construction. Connes' framework was specifically designed
   over dense, holomorphically closed pre-$C^*$-algebras for this
   reason.
3. **Index encoding — distinguish two current invariants.** `Fredholm.index` applies to
   bounded maps and is used only after an `IsFredholm` proof. `gradedKernelIndex` applies
   to the full even Dirac kernel and is not yet proved equal to a chiral Fredholm index.
   The trace formula $\ind = \Tr(\gamma e^{-tD^2})$ is beautiful but
   requires heat semigroups, trace-class estimates, and the
   McKean--Singer asymptotic expansion — none of which is in Mathlib.
   The algebraic definition is exact, native, and far easier to
   manipulate.
4. **Examples first — yes; swap Phases 3 and 4.** The $S^1$ Dirac
   triple is essentially a diagonal operator on $\ell^2(\Z)$; building
   it first stress-tests the unbounded core without differential geometry. The separate
   shift example tests the bounded Fredholm API. The chiral pairing layer remains open.
5. **Equivariance — defer to Phase 4.5.** Baking $G$-equivariance into
   the Phase 1 definitions would complicate typeclass inference and
   force every non-equivariant theorem to carry an unused
   `[TopologicalGroup G]` instance. Lean's `extends` makes adding the
   equivariance layer cheap when we get to it.

# 6. Continuation: noncommutative metric geometry from the algebraic core

*The phases above are scoped to definitions, the index pairing, the
spectral distance, and concrete examples. This section sketches the
theorems that **emerge automatically** from the same algebraic data
once both §2.5 (Bakry--Émery $\Gamma_2$) and §2.7 (Connes' spectral
distance) are in place. None of these is a deliverable of the current
plan; together they are the natural research-level continuation,
encompassing modern noncommutative metric geometry.*

The unifying observation: every result in this section follows from
operator inequalities on $\Gamma$, $\Gamma_2$, $[D, \pi(a)]$, and the
heat semigroup $P_t = e^{-tD^2}$. No manifold tools — no geodesics,
volume forms, Jacobi fields, or Levi--Civita connection — are required.
Each theorem therefore specializes simultaneously to (i) the canonical
Dirac triple of a smooth manifold, (ii) the finite `SusyGraphop` of a
graph, and (iii) any further instance of the abstract framework.

## 6.1 Optimal transport (the Wasserstein-1 metric)

For commutative $\A = C(X)$ with $X$ compact, states are probability
measures on $X$. The Connes distance evaluated on states $\phi_\mu, \phi_\nu$
corresponding to measures $\mu, \nu$ satisfies, by
**Kantorovich--Rubinstein duality**:
$$
d_D(\phi_\mu, \phi_\nu) \;=\; W_1(\mu, \nu)
\;=\; \inf_{\pi \in \Pi(\mu, \nu)} \int d_g(x, y)\,d\pi(x, y),
$$
the Wasserstein-1 (earth-mover) distance. The Lipschitz condition
$\|[D, \pi(a)]\| \leq 1$ is the dual Kantorovich condition. For the
graph case (finite $\A$, Dirac masses), the same formula reduces to
the linear-programming form of $W_1$ and recovers the shortest-path
metric. **One `sSup` definition absorbs the entire optimal-transport
formalism.**

## 6.2 Entropic curvature and heat-flow contraction (Lott--Sturm--Villani)

The synthetic Ricci-curvature lower bound $CD(\rho, \infty)$ is
*equivalent* to the heat flow being a strict exponential contraction
on $(\mathcal{S}(\A), d_D)$:
$$
d_D\bigl(\phi \circ P_t,\;\psi \circ P_t\bigr) \;\leq\; e^{-\rho t}\;d_D(\phi, \psi)
\qquad \forall\, t \geq 0,\ \phi, \psi \in \mathcal{S}(\A).
$$
This is the von Renesse--Sturm characterization, lifted to the
noncommutative setting by Lott, Erbar--Maas, Carlen--Maas, and
Wirth--Zhang. **Heat distributions exponentially collapse together at
rate $\rho$** — a pure metric-geometric reformulation of the
gradient-decay form of §2.5, useful as an *alternative* axiomatization
of $CD(\rho, \infty)$ that avoids operator-positivity.

## 6.3 Poincaré inequality and spectral gap

Integrating $\Gamma_2(a, a) \geq \rho\,\Gamma(a, a)$ along the heat
semigroup yields the noncommutative **Poincaré inequality**: for any
mean-zero state, the variance is controlled by the Dirichlet energy,
$$
\mathrm{Var}_\phi(a) \;\leq\; \tfrac{1}{\rho}\,\phi\bigl(\Gamma(a, a)\bigr) \qquad (\rho > 0).
$$
Equivalently, the first non-zero eigenvalue of $L = D^2$ satisfies
$\lambda_1 \geq \rho$ (Lichnerowicz spectral gap for manifolds; mixing
rate for finite graphs / quantum Markov semigroups). The proof is a
two-line algebraic manipulation of $P_t$ and requires no manifold
infrastructure — strikingly different from the classical Lichnerowicz
proof, which uses the Bochner formula and integration by parts on the
sphere/manifold. In the discrete case it specializes to bounds on
random-walk convergence rates on finite graphs.

## 6.4 Log-Sobolev inequality and hypercontractivity

A strictly positive curvature bound $CD(\rho, \infty)$, $\rho > 0$, in
fact implies the much stronger **logarithmic Sobolev inequality**
$$
\mathrm{Ent}_\phi(a^2) \;\leq\; \tfrac{2}{\rho}\,\phi\bigl(\Gamma(a, a)\bigr),
$$
which by Gross's theorem is equivalent to **hypercontractivity**:
the heat semigroup $P_t$ maps $L^2 \to L^p$ for $p > 2$ in finite time,
with explicit time constants. This is the original purpose of the
Bakry--Émery $\Gamma_2$ calculus (1985) and is the technical backbone
of statistical-mechanics phase transitions and (in the
quantum-Markov-semigroup setting of Junge--Mei--Parcet, Carlen--Maas)
the sharpest known bounds on noncommutative mixing. **All three
inequalities — Poincaré, log-Sobolev, hypercontractivity — fall out of
the same operator inequality $\Gamma_2 \geq \rho \Gamma$.**

## 6.5 Quantum Bonnet--Myers (diameter bounds)

Upgrade the curvature condition to the **dimensional**
$CD(\rho, n)$ inequality by adding a $\tfrac{1}{n}(La)^2$ correction:
$$
\Gamma_2(a, a) \;\geq\; \rho\,\Gamma(a, a) \;+\; \tfrac{1}{n}\,(La)^2.
$$
Then (Rieffel; Connes; Bakry--Qian) the **Connes--Wasserstein diameter**
of the state space is finite,
$$
\mathrm{diam}\bigl(\mathcal{S}(\A), d_D\bigr) \;\leq\; \pi\sqrt{\tfrac{n}{\rho}}.
$$
This is the **noncommutative Bonnet--Myers theorem**: positive Ricci
curvature forces compactness with a quantitative diameter bound — a
purely operator-algebraic statement of the classical Riemannian
result, working uniformly for manifolds, graphs, and abstract
$C^*$-algebras. The classical proof uses Jacobi field ODEs along
geodesics; the algebraic proof uses three lines of $\Gamma_2$ calculus.

## 6.6 Quantum Gromov--Hausdorff convergence (continuum limits)

The **Lipschitz seminorm** $L(a) := \|[D, \pi(a)]\|$ on a spectral
triple is the data of a **compact quantum metric space** in Rieffel's
sense (1999, 2004). The **quantum Gromov--Hausdorff distance**
$d_{\mathrm{QGH}}$ defines a metric on the proper class of all compact
quantum metric spaces. Statement:
$$
\bigl(\A_n, L_n\bigr) \xrightarrow{\;d_{\mathrm{QGH}} \to 0\;} \bigl(\A, L\bigr)
$$
makes "the lattice graphop converges to the smooth manifold" into a
precise mathematical statement. For our Phase 3.5 $T^2$ test: the
square-lattice `SusyGraphop` at mesh $\varepsilon$ converges in
quantum Gromov--Hausdorff to the smooth Dirac `IsEvenFredholmModule`
of $T^2$ as $\varepsilon \to 0$. This is the rigorous form of the
**continuum-limit thesis** that underwrites both this project and
[`graphops-qft`].

## 6.7 What ties it together

Each section above is a theorem about $\Gamma$, $\Gamma_2$,
$[D, \pi(a)]$, and $P_t = e^{-tD^2}$. Each classical proof relies on
manifold-specific tools (geodesics, Jacobi fields, Bochner integration
by parts, volume forms, the Levi--Civita connection); the
algebraic-operator proofs replace all of these with operator
inequalities on the spectral triple. Once Phases 4.75 (super-BE) and
2.5 (spectral distance) are in place, **the same Lean theorem proves
each result simultaneously for smooth manifolds, finite graphs, and
arbitrary `BakryEmeryFredholmModule`s** — including fractal spaces,
quantum groups, and the C\*-algebraic deformations of `graphops-qft`.

This is the long-term payoff of the synthesis: a uniform metric-geometric
calculus, formalized algebraically, that specializes to the classical
results without re-proof.

# 7. References

1. **Connes**, *Noncommutative Geometry*, Academic Press, 1994. Chapter
   VI (definition + index pairing); Chapter IV §2 (local index formula
   with Moscovici).
2. **Gracia-Bondía, Várilly, Figueroa**, *Elements of Noncommutative
   Geometry*, Birkhäuser, 2001. Chapters 9–11 (Dirac operator, canonical
   triple, axiomatics).
3. **Higson, Roe**, *Analytic K-Homology*, OUP, 2000. Chapter 8
   (Fredholm modules, index pairing); Chapter 10 (Dirac).
4. **Kasparov**, "The operator $K$-functor and extensions of
   $C^*$-algebras", *Izv. Akad. Nauk SSSR Ser. Mat.* 44 (1980), 571–636
   (English transl.: *Math. USSR-Izv.* 16, 513–572); "Equivariant
   $KK$-theory and the Novikov conjecture", *Invent. Math.* 91 (1988),
   147–201. Foundational for the families and equivariant
   generalizations of §2.4 / §3.8.
5. **Atiyah, Singer**, "The index of elliptic operators I, III", *Ann.
   of Math.* 87 (1968), 484–530 and 546–604; "IV" (1971), 119–138. The
   classical index theorem and its families generalization; the target
   that Phases 4 and 6 specialize to in the manifold case. The
   equivariant fixed-point theorem of Phase 4.5 is from
   Atiyah--Segal--Singer (same series, paper II).
5a. **Atiyah, Patodi, Singer**, "Spectral asymmetry and Riemannian
    geometry I, II, III", *Math. Proc. Camb. Phil. Soc.* 77 (1975)
    43–69, 78 (1975) 405–432, 79 (1976) 71–99. The index theorem for
    manifolds with boundary, the eta-invariant, and the APS non-local
    boundary conditions of §2.6's "Manifolds with boundary"
    out-of-scope note.
6. **Lawson, Michelsohn**, *Spin Geometry*, Princeton University Press,
   1989. Chapters I–II for Clifford algebras, $\mathrm{Spin}(n)$, spinor
   bundles and Dirac operators — the bundle-theoretic input to Phase 4a.
7. **Bakry, Émery**, "Diffusions hypercontractives", *Séminaire de
   Probabilités XIX*, Springer LNM 1123 (1985), 177–206. The original
   $\Gamma_2$ calculus and curvature-dimension condition referenced in
   §2.5 / Phase 4.75.
8. **Cipriani, Sauvageot**, "Derivations as square roots of Dirichlet
   forms", *J. Funct. Anal.* 201 (2003), 78–120. The noncommutative
   carré du champ from a spectral triple — the technical basis for the
   $\Gamma(a, b) = \tfrac{1}{2}(\delta(a)^*\delta(b) + \dots)$ formula.
9. **Cushing, Kamtue, Liu, Münch, Peyerimhoff, Snodgrass**,
   "Bakry–Émery curvature sharpness and curvature flow in finite
   weighted graphs", arXiv:2204.10064 (2022). Rigorous convergence
   theory for the BE flow on finite graphs, providing test cases for the
   `graphops-qft` bridge.
10. **`graphops-qft`** (related internal project). The finite-dimensional /
    graph-theoretic instantiation of the same
    `SusyGraphop = IsEvenFredholmModule` structure, with super-BE
    curvature flows and the spectral-triple connection worked out at
    the discrete level.
11. **Witten**, "Supersymmetry and Morse theory", *J. Differential
    Geom.* 17 (1982), 661–692. The deformation $d_t = e^{-tf} d e^{tf}$
    and the heuristic Morse-complex picture referenced in §2.6 / Phase
    3.7.
12. **Helffer, Sjöstrand**, "Puits multiples en mécanique
    semi-classique IV: étude du complexe de Witten", *Comm. Partial
    Differential Equations* 10 (1985), 245–340. The rigorous
    semiclassical analysis of the $t \to \infty$ limit of the Witten
    Laplacian, recovering Morse inequalities and the Morse complex.
13. **Connes**, "Compact metric spaces, Fredholm modules, and
    hyperfiniteness", *Ergodic Theory Dynam. Systems* 9 (1989),
    207–220. The spectral-distance formula of §2.7.
14. **Rieffel**, "Metrics on state spaces", *Doc. Math.* 4 (1999),
    559–600. The Lipschitz-seminorm / compact-quantum-metric-space
    framework — when the spectral distance metrizes the weak-$*$
    topology on $\mathcal{S}(\A)$.

### For §2.8 (cyclic cohomology)

14a. **Connes**, "Noncommutative differential geometry",
     *Publ. Math. IHÉS* 62 (1985), 41–144. The original cyclic
     cohomology paper and the $(b, B)$-cocycle definition of the
     Chern--Connes character of a Fredholm module.
14b. **Loday**, *Cyclic Homology*, Springer Grundlehren 301, 2nd ed.
     (1998). Textbook reference for Hochschild and cyclic
     (co)homology, the $(b, B)$-bicomplex, and periodicity.
14c. **Jaffe, Lesniewski, Osterwalder**, "Quantum K-theory I: The
     Chern character", *Comm. Math. Phys.* 118 (1988), 1–14. The JLO
     entire-cyclic cocycle representing $\mathrm{ch}(D)$ in the
     unbounded picture.
14d. **Hochschild, Kostant, Rosenberg**, "Differential forms on
     regular affine algebras", *Trans. Amer. Math. Soc.* 102 (1962),
     383–408. The original HKR theorem identifying Hochschild
     cohomology with differential forms; the algebraic input to
     Connes' iso $HP^*(C^\infty(M)) \cong H^*_{\mathrm{dR}}(M)$.

### For §2.9 (noncommutative instances)

14e. **Connes**, "$C^*$-algèbres et géométrie différentielle",
     *C. R. Acad. Sci. Paris Sér. A-B* 290 (1980), A599–A604. The
     original construction of the spectral triple on the
     noncommutative torus $A_\theta$, including the isospectral
     property.
14f. **Rieffel**, "$C^*$-algebras associated with irrational rotations",
     *Pacific J. Math.* 93 (1981), 415–429. Construction of the
     Powers--Rieffel projection $p_\theta$ realizing $\tau(p_\theta) = \theta$;
     the K-theory of $A_\theta$.
14g. **Pimsner, Voiculescu**, "Exact sequences for $K$-groups and
     Ext-groups of certain cross-product $C^*$-algebras", *J. Operator
     Theory* 4 (1980), 93–118. The Pimsner--Voiculescu exact sequence
     computing $K_0(A_\theta) \cong \Z + \Z$ and the range of the trace
     $\tau(K_0(A_\theta)) = \Z + \theta\Z$.
14h. **Connes, Landi**, "Noncommutative manifolds, the instanton
     algebra and isospectral deformations", *Comm. Math. Phys.* 221
     (2001), 141–159. The isospectral-deformation construction,
     generalizing the NC torus to a broad class of noncommutative
     manifolds with the same Dirac spectrum as a classical model.

### For §6 (continuation directions)

15. **Villani**, *Optimal Transport: Old and New*, Springer
    Grundlehren 338 (2009). The reference for Wasserstein distance,
    Kantorovich--Rubinstein duality (§6.1), and the Lott--Sturm--Villani
    synthetic-Ricci framework (§6.2).
16. **Sturm**, "On the geometry of metric measure spaces I, II",
    *Acta Math.* 196 (2006), 65–177. The metric-measure-space
    formulation of $CD(K, N)$ via entropy convexity in Wasserstein space.
17. **Lott, Villani**, "Ricci curvature for metric-measure spaces
    via optimal transport", *Ann. of Math.* 169 (2009), 903–991.
    The independent (and complementary) synthetic formulation; jointly
    with [16] this is "LSV theory".
18. **Bakry, Gentil, Ledoux**, *Analysis and Geometry of Markov
    Diffusion Operators*, Springer Grundlehren 348 (2014). The
    comprehensive reference for $\Gamma_2$-calculus, Poincaré, LSI,
    hypercontractivity, and the diffusion analogue of Bonnet--Myers
    (§§6.3--6.5).
19. **Rieffel**, "Gromov--Hausdorff distance for quantum metric
    spaces", *Mem. Amer. Math. Soc.* 168 (2004), no. 796. Defines
    $d_{\mathrm{QGH}}$ on the class of compact quantum metric spaces
    (§6.6).
20. **Carlen, Maas**, "Gradient flow and entropy inequalities for
    quantum Markov semigroups with detailed balance", *J. Funct.
    Anal.* 273 (2017), 1810–1869. Entropic Ricci curvature for
    quantum Markov semigroups — the noncommutative form of the
    Lott--Sturm--Villani contraction (§6.2).
21. **Wirth, Zhang**, "Complete gradient estimates of quantum Markov
    semigroups", *Comm. Math. Phys.* 387 (2021), 761–791. Sharpest
    known $\Gamma_2$-style bounds in the noncommutative setting.
