---
rg: 2
id: type-f-bnsr-invariants-stabilize-at-dimension-citation
kind: route
title: Import the dimension bound for BNSR invariants of groups of type F from Ershov–Zaremsky
target: type-f-bnsr-invariants-stabilize-at-dimension
requires: []
---

Citation import. M. Ershov and M. C. B. Zaremsky, "Dense and empty
BNSR-invariants of the McCool groups", arXiv:2505.18826, §2.1
("BNSR-invariants"), read 2026-09-13 through the ar5iv rendering:
"Note that if G is of type F with a finite classifying space of dimension n,
then Σn(G)=Σ∞(G)". They add "(for example this follows from [Zar17, Citation
1.5])".

Corroboration of the homological half (not a replacement for the import).
Let `X` be the universal cover of a finite `n`-dimensional `K(G,1)`, a
contractible free cocompact `G`-complex. Let `Y ⊆ X` be any subcomplex, for
instance a superlevel set of a character height function. Then
`H_k(Y) = 0` for `k > n` by dimension. Also `H_n(Y) = Z_n(Y) ⊆ Z_n(X) = H_n(X)
= 0`, since neither complex has `(n+1)`-cells. So the essential-acyclicity
condition defining `Σ^m(G;Z)` is automatic in every degree `≥ n`, and
`Σ^m(G;Z) = Σ^n(G;Z)` for `m ≥ n`. The homotopical statement then follows
from the Bieri–Renz comparison `Σ^m(G) = Σ^2(G) ∩ Σ^m(G;Z)` for `m ≥ 2`, which
this node does not import; the cited sentence covers it directly.
