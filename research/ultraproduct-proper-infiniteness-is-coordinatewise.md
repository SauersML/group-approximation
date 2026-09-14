---
rg: 2
id: ultraproduct-proper-infiniteness-is-coordinatewise
kind: claim
title: A matrix algebra over an ultraproduct is properly infinite iff almost all coordinate matrix algebras are
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

**ESTABLISHED (literature).**  Let `(A_n)` be unital C\*-algebras, `omega` a
free ultrafilter on `N`, and `k >= 1`.  Then `M_k(prod_omega A_n)` is properly
infinite iff `{n : M_k(A_n) properly infinite}` belongs to `omega`.

This is Lemma 4.5 of Milhøj–Rørdam, arXiv:2309.17412v2.  Proper infiniteness
is witnessed by approximate relations: a unital algebra is properly infinite iff
it contains `a_1, a_2` with `||a_j* a_i - delta_ji 1|| < 1/2` (their
Lemma 3.4), and such relations lift to coordinates for `omega`-many `n`.

With `quasitrace-iff-not-stably-properly-infinite` this gives the ultraproduct
mechanism of Milhøj–Rørdam Theorem 4.6.  If `mu(A_n) -> infinity`, then
`prod_omega A_n` admits a normalized 2-quasitrace.
