# Higson, Roe — *Analytic K-Homology*

**Authors:** Nigel Higson, John Roe
**Publisher:** Oxford University Press (2000), *Oxford Mathematical Monographs*
**ISBN:** 978-0-19-851176-5
**Zotero:** _TODO — add via Zotero connector and paste `zotero://select/library/items/<KEY>`_

## Summary

A self-contained development of analytic K-homology — the dual theory to K-theory, defined directly via operator-theoretic data on Hilbert space — and a proof of the Atiyah–Singer index theorem within that framework. The central object is the **Fredholm module**: a pair `(H, F)` where `H` carries a representation `π` of a `C*`-algebra `A` and `F : H → H` is a bounded self-adjoint operator with `F² − 1` and `[F, π(a)]` compact for every `a`. Even/odd Fredholm modules give classes in `K⁰` / `K¹`.

The link to spectral triples is the **bounded transform** `F = D(1+D²)^{-1/2}`: given an unbounded spectral triple `(A, H, D)`, this produces a Fredholm module representing the same K-homology class. Higson–Roe stay almost entirely in the bounded picture, which is technically simpler (no domain issues, no unboundedness) and pairs cleanly with KK-theory and Kasparov's framework.

The index pairing `K^0(X) ⊗ K⁰(X) → ℤ` is constructed analytically (Chapter 8) and computed for the Dirac operator on a spin manifold (Chapters 10–11), giving Atiyah–Singer. Their proof uses the Connes–Skandalis tangent groupoid / asymptotic morphism approach, which is cleaner than the heat-kernel proof and lifts to formalization more naturally.

## Relevance

**Companion reference** for Phase 2 (index pairing). If the unbounded D approach hits a wall in Mathlib, falling back to the bounded F-picture is the natural escape, and Higson–Roe is the cleanest source for that route. Their Chapter 10 (Dirac operators on Riemannian manifolds) is also a good cross-check for Phase 3, more analytic and less geometric than GBF.
