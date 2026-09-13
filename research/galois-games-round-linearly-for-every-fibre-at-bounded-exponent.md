---
rg: 2
id: galois-games-round-linearly-for-every-fibre-at-bounded-exponent
kind: claim
title: For every finite G of exponent m and every K <= G, SDP 1-eps of a symmetric Galois game forces val >= 1 - C(m) eps log k
distinct_from:
  free-subgroup-rounding-is-universal-at-bounded-exponent: that asked for a free subgroup, which fails for non-normal K; this asks only for the value, which permutable subgroups or non-subgroup transversals may still reach.
  normal-fibre-galois-games-round-linearly-over-all-groups: that proves this for normal K (via free subgroups); this is the non-normal case.
---

**OPEN.** Is there `C(m)` such that for every finite `G` of exponent `m`, every
`K <= G` of order `k`, and every symmetric conjugation-invariant `mu`,
`SDP Gal(G,K,mu) >= 1 - eps` implies `val Gal(G,K,mu) >= 1 - C(m) eps log k`?

For normal `K` this holds (`normal-fibre-galois-games-round-linearly-over-all-groups`;
uniform in `m` over solvable groups, and over all groups by CFSG). A no for some
non-normal `K` would be a genuinely non-abelian symmetric integrality gap at
bounded exponent in the regime `eps log k = O(1)`. A yes would say that
symmetric quotient constructions over bounded-exponent groups never beat
Khot--Vishnoi, for any fibre.

## Attempts

* **Free subgroups.** Dead for this purpose:
  `free-subgroup-rounding-fails-for-non-normal-fibres`. Free rounding pays
  `[G : N_G(K)]` (`free-rounding-pays-the-number-of-fibre-conjugates`), which is
  unbounded at exponent `4`.
* **Permutable primitive kernels.** Permutable rounding (part 5 of
  `galois-games-round-through-free-subgroups`) needs `L cap K = {e}` and `KL = LK`.
  If at every step of the halving chain the chosen conjugate `x H_rho x^-1` of the
  inducing subgroup contains `K`, then `K` normalizes each `x (ker sigma) x^-1`,
  hence normalizes `L`, and `val >= 1 - 3 eps log_q k/c(G,m)` follows. This is how
  the wreath-product family rounds: the certificate is induced from the base `B`,
  which contains `K`. **Where it dies:** `K` may have no fixed point on
  `G/H_rho`. By Mackey, the admissible conjugates correspond to double cosets
  `K x H_rho` with `K <= x H_rho x^-1`, and nothing forces one of them to have a
  kernel omitting the chosen `a`.
* **Test: translation fibre in `F_2 wr F_2^n`.** Take `K = <t>` with `t` a nonzero
  translation, and `mu = (1-delta) delta_e + delta` uniform on the class
  `{ (c,t) : c in Im(1+t) }`. Since `t` centralizes `V = Im(1+t)`, any admissible
  vector splits into `V`-invariant and non-invariant parts, which gives
  `SDP = 1 - delta/2`. `L = W x <(c_0, t)>`, with `W` a hyperplane of `V` omitting
  `c_0 in V`, meets `K` trivially, is centralized by `K`, and has
  `mu(L) = 1 - delta/2`. So `val = SDP`. No gap.
* **Abelian normal closure: yes.** `abelian-normal-closure-fibres-round-linearly`.
  If `K` lies in an abelian normal `A`, every irreducible is induced from a
  primitive representation of a subgroup containing `A`, so every conjugated
  primitive kernel is normalized by `K`. The permutable-kernel attempt above then
  works, with constant `3/c(G,m)`. This covers the wreath-product family and the
  translation-fibre test above. Open: fibres whose conjugates do not all commute.
* **Transversals made of `L`-cosets reduce to permutable subgroups when `k = 2`.**
  Let `K = <a>` and `L cap K = {e}`. A transversal that is a union of left
  `L`-cosets is one colour class of the graph on `G/L` with edges
  `gL -- gaL`. That graph is bipartite iff `a` is not in the normal closure
  `M_0 = <L, aLa>` of `L` in `<L, a>`. Then `M_0 cap K = {e}`, `M_0 K` is a
  subgroup, and `mu(M_0) >= mu(L)`. So coset-structured labelings give nothing
  beyond permutable rounding, and a counterexample must defeat unstructured
  transversals.
* **Where a counterexample would live.** Certificates carried by representations
  induced from subgroups on whose cosets `K` acts freely, with `[G : N_G(K)]` large,
  while every `L` permuting with `K` misses a fixed fraction of `mu`. No candidate
  has been checked.
