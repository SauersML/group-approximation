---
rg: 2
id: bkko-reduced-traces-concentrate-on-amenable-radical
kind: claim
title: Every tracial state on a reduced group C-star algebra concentrates on the amenable radical
distinct_from:
  kt-q2-double-reduced-algebra-has-unique-trace: that applies the unique-trace corollary to one explicit double with trivial amenable radical; this is the general concentration theorem, which also speaks about groups whose amenable radical is nontrivial.
---

ESTABLISHED (literature import).  Breuillard--Kalantar--Kennedy--Ozawa,
*C*-simplicity and the unique trace property for discrete groups*,
arXiv:1410.2518v3, Theorem 4.1, read from the source PDF on 2026-09-11:

> Let `G` be a discrete group.  Then every tracial state `tau` on the reduced
> C*-algebra `C*_r(G)` concentrates on the amenable radical `R_a(G)`.  That
> is, `s notin R_a(G)` implies that `tau(lambda_s) = 0` for every `s in G`.

Corollary 4.3 of the same paper is the unique-trace characterization
(`C*_r(G)` has a unique tracial state exactly when `R_a(G)` is trivial), which
is what `kt-q2-double-reduced-algebra-has-unique-trace` uses.
