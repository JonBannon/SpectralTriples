# Gracia-Bondía, Várilly, Figueroa — *Elements of Noncommutative Geometry*

**Authors:** José M. Gracia-Bondía, Joseph C. Várilly, Héctor Figueroa
**Publisher:** Birkhäuser Boston (2001), *Birkhäuser Advanced Texts*
**ISBN:** 978-0-8176-4124-5
**DOI:** [10.1007/978-1-4612-0005-5](https://doi.org/10.1007/978-1-4612-0005-5)
**Zotero:** _TODO — add via Zotero connector and paste `zotero://select/library/items/<KEY>`_

## Summary

A textbook-length development of noncommutative geometry built around the spectral triple. The first half covers prerequisites (C\*-algebras, K-theory, cyclic cohomology, Clifford algebras and spinors). The second half builds spectral triples and the local index formula, with unusually explicit attention to the *commutative* case: how a closed Riemannian spin manifold gives a canonical spectral triple `(C^∞(M), L²(S), D)` where `S` is the spinor bundle and `D` is the Dirac operator.

Of the three primary references this is the one that most carefully writes out the bundle-theoretic construction: Clifford bundle as a sub-bundle of `End(S)`, the Levi–Civita connection lifted to the spin bundle, the Dirac operator as `D = c ∘ ∇^S`, and the verification of each spectral-triple axiom (self-adjointness, compact resolvent via Rellich–Kondrachov, bounded commutators `[D, M_f] = c(df)`, the chirality grading `γ` in even dimension). Chapters 9–11 are the core for our purposes.

GBF state Connes' **reconstruction theorem axiomatics** — the seven conditions (dimension, regularity, finiteness, reality, first-order, orientation, Poincaré duality) under which a commutative spectral triple comes from a unique smooth spin manifold. We only need the subset relevant to the index pairing, but having all seven written out in one place is useful.

## Relevance

**Primary reference** for Phase 3 (manifold → triple) of the formalization. Use the chapter on Dirac operators as the template for the Lean construction. Cross-check the Z₂-grading definition against Connes' conventions — GBF and Connes use compatible signs but spell out different intermediate steps.
