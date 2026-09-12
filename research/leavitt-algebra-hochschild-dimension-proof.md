---
rg: 2
id: leavitt-algebra-hochschild-dimension-proof
kind: route
title: Base-change the free bimodule of differentials along the flat universal localization of the path algebra
target: leavitt-algebra-hochschild-dimension-at-most-one
requires: []
---

Let `P = P(E) = k<x_1, x_2>` be the path algebra of the quiver with one vertex
and two loops, and `L = L(E) = Σ^(-1) P` its universal localization.

1. **Epimorphism.** Universal localizations are ring epimorphisms, so
   `L ⊗_P L = L`.
2. **Flatness.** Ara--Cortiñas arXiv:1108.0352v3, proof of Lemma 6.1, read from
   the PDF text on MSI on 2026-09-12: "the universal localization
   P(E) -> L(E) = Σ^(-1)P(E) is flat on the left" (their reference [3],
   Proposition 4.1). Flatness on one side gives `Tor_1^P(L, L) = 0`.
3. **Differentials of the free algebra.** `Ω¹P = ker(P ⊗_k P -> P)` is the free
   bimodule `P ⊗_k V ⊗_k P` on `dx_1, dx_2`.
4. **Base change.** The sequence `0 -> Ω¹P -> P ⊗_k P -> P -> 0` splits as left
   `P`-modules, so `L ⊗_P -` keeps it exact. Applying `- ⊗_P L` gives the long
   exact sequence
   `Tor_1^P(L, L) -> L ⊗_P Ω¹P ⊗_P L -> L ⊗_k L -> L ⊗_P L -> 0`.
   The first term is zero by step 2 and the last is `L` by step 1. So
   `0 -> L ⊗_k V ⊗_k L -> L ⊗_k L -> L -> 0` is exact, and its first term is a
   free `L`-bimodule.

Trust surface: the flatness statement is read through Ara--Cortiñas'
quotation; the primary [3] was not read.
