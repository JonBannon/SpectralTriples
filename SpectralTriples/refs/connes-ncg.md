# Connes — *Noncommutative Geometry*

**Authors:** Alain Connes
**Publisher:** Academic Press (1994)
**ISBN:** 978-0-12-185860-5
**Open PDF:** [alainconnes.org/wp-content/uploads/book94bigpdf.pdf](https://alainconnes.org/wp-content/uploads/book94bigpdf.pdf)
**Zotero:** _TODO — add via Zotero connector and paste `zotero://select/library/items/<KEY>`_

## Summary

The foundational monograph for the entire programme. Chapter VI ("The Metric Aspect of Noncommutative Geometry") introduces the spectral triple `(A, H, D)` — originally called a "K-cycle" — as the noncommutative replacement for a Riemannian manifold. The data: a `*`-algebra `A` represented on a Hilbert space `H`, plus a self-adjoint unbounded operator `D` on `H` with compact resolvent and bounded commutators `[D, π(a)]` for `a ∈ A`. The Z₂-graded case adds `γ` satisfying `γ² = 1`, `γ* = γ`, `[γ, π(a)] = 0`, `γD + Dγ = 0`.

Two results from this book are the technical core of what we want to formalize. First, the **index pairing**: a class `[D] ∈ K^0(A)` (even case) pairs with `[p] ∈ K_0(A)` to give `⟨[D], [p]⟩ = ind(pD⁺p) ∈ ℤ`. Connes proves Fredholmness of `pD⁺p` from the spectral-triple axioms — this is the abstract result that specializes to Atiyah–Singer when `A = C^∞(M)`. Second, the **local index formula** (Connes–Moscovici, Chapter IV §2): the index is computable as a finite sum of residues of zeta functions of `D`, generalizing the heat-kernel expansion to the noncommutative setting.

Connes also introduces the example of `(C^∞(M), L²(S), D)` for a Riemannian spin manifold (Chapter VI §1–2). The treatment is more concise than GBF — bundle constructions are sketched rather than derived — but Connes' choices set the conventions that downstream references inherit.

## Relevance

**Foundational reference** for Phase 1 (abstract definition). Use Chapter VI for the axiom statement and the conventions for `γ` and the index pairing. Defer the local index formula to a later phase — it is the natural endpoint but well beyond the initial formalization scope.
