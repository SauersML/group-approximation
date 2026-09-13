---
rg: 2
id: af-k0-order-divisible-iff-no-elementary-subquotient
kind: claim
title: The K_0 group of an AF algebra divides with order-small remainders exactly when the algebra has no elementary subquotient
distinct_from:
  separable-exact-nowhere-scattered-tensor-permanence: that proves permanence of nowhere scatteredness under minimal tensor products; this characterizes the absence of elementary subquotients in an AF algebra by an order-divisibility property of its K_0 group.
---

**Theorem.**  Let `D` be an AF algebra, unital or not.  The following are
equivalent.

1. (ND) holds in `K_0(D)`.  For every `c in K_0(D)^+` and all `N, M >= 1`
   there is `d in K_0(D)^+` with `N d <= c` and `M (c - N d) <= c`.
2. No corner `p (D tensor K) p` by a nonzero projection has a nonzero
   finite-dimensional representation.
3. `D` has no elementary subquotient: there are no closed ideals `I subset J`
   of `D` with `J/I isomorphic to K(H)` for a nonzero Hilbert space `H`.

Thiel--Vilalta's nowhere scattered algebras satisfy 3 (their Theorem 3.1, as
used in `stw96-rr0-nowhere-scattered-generator-corridor-proof`).  We use 3
itself as the hypothesis.

**Examples.**

* 1--3 hold for UHF algebras, simple non-elementary AF algebras, and
  `C(X) tensor B` for a totally disconnected compact `X` and a UHF algebra `B`.
* 1--3 fail for `C(X)` with `X` a Cantor space (every point gives a
  one-dimensional quotient), for the unitization of `K`, for extensions of UHF
  algebras by `K`, and for every AF algebra with a finite-dimensional
  representation.

In the second group, `c = 1` (or a rank-one projection in `K`), `N = 2k` and
`M = 2` witness the failure of 1.

**Use.**  Condition 1 is the divisibility axiom of
`coinvariant-tarski-lemma-minimal-nowhere-scattered`.  So that lemma, and the
crossed-product dichotomy built on it, apply to every AF coefficient algebra
without elementary subquotients.  The threshold is sharp for the division
mechanism, because condition 1 fails as soon as a single elementary subquotient
exists.
