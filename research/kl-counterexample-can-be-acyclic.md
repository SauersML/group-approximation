---
rg: 2
id: kl-counterexample-can-be-acyclic
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken over a countable acyclic coefficient group
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that places a counterexample over a two-generator simple group, whose homology is not controlled; this places one over a group whose integral homology vanishes in every positive degree, where Schur kernels are automatically zero.
  kl-counterexample-absorbs-any-countable-group: that forces a prescribed countable subgroup into a simple counterexample; this forces acyclicity, a homological property that is not of the "contains a copy of" form.
---

If `kervaire-laudenbach-nonsingular-conjecture` fails, then there are a
countable group `Y` with `H_n(Y; Z) = 0` for every `n >= 1`, an element
`1 != a in Y`, and `w in Y * <t>` with `deg_t(w) != 0`, such that `a` dies in
`Y_w = (Y * <t>)/<<w>>`.

The mechanism is upward transfer: if `a` dies in `A_w` for the coefficient
subgroup `A`, it dies in `Y_w` for every group `Y` containing `A`.

## Why it matters for the Schur route

An acyclic `Y` is superperfect, so its Schur kernel `K_2(Y, w)` is zero for
every equation. Over acyclic coefficient groups the Schur kernel detects
nothing, yet the conjecture restricted to them is the whole conjecture. A
Schur-kernel argument therefore has to pass through an auxiliary group with
second homology. `kl-iff-acyclic-torus-amalgam-schur-injectivity` identifies
the smallest one that suffices.

DERIVATION
kl-counterexample-acyclic-envelope-proof
