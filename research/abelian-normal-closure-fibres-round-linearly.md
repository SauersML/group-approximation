---
rg: 2
id: abelian-normal-closure-fibres-round-linearly
kind: claim
title: If K lies in an abelian normal subgroup of G, SDP 1-eps gives L normalized by K with L cap K = {e} and mu(G minus L) <= 3 eps log_q k / c(G,m), so val >= 1 - that
distinct_from:
  normal-fibre-galois-games-round-linearly-over-all-groups: that treats normal K through free subgroups; this treats K inside an abelian normal subgroup, which may be far from normal, through permutable subgroups.
  free-rounding-pays-the-number-of-fibre-conjugates: that bounds free subgroups at the cost of [G:N_G(K)]; this bounds the value with no such factor when the normal closure of K is abelian.
---

**ESTABLISHED.** Let `G` be finite of exponent `m`, `mu` symmetric and
conjugation-invariant, and `K <= A` with `A` an abelian normal subgroup of `G`.
Equivalently, the normal closure of `K` is abelian. Let `k = |K|` and `q` the
least prime dividing `k`, and suppose `SDP Gal(G,K,mu) >= 1 - eps`. With `c(G,m)`
as in `normal-fibre-galois-games-round-linearly-over-all-groups`, some `L <= G`
normalized by `K` has `L cap K = {e}` and

```text
mu(G \ L) <= 3 eps log_q k / c(G,m),     hence     val Gal(G,K,mu) >= 1 - 3 eps log_q k / c(G,m).
```

When `G` is an M-group, `c` may be replaced by `1 - cos(2 pi/m)`.

The key fact: **every irreducible of `G` is induced from a primitive
representation of a subgroup containing `A`.** Then every conjugate of every
primitive kernel is normalized by `K`, so the halving chain produces a
permutable `L`, and permutable rounding gives the value. Here `L` is usually not
free: in `free-subgroup-rounding-fails-for-non-normal-fibres` (`K = <e_0>` inside
the abelian base) no free subgroup is good, while this claim gives
`val >= 1 - 3 eps`.

This settles `galois-games-round-linearly-for-every-fibre-at-bounded-exponent`
for fibres with abelian normal closure. That includes both tests recorded there:
the coordinate fibre and the translation fibre `<(0,t)>`, whose normal closure
`Im(1+t) x <t>` is abelian. The open case is a fibre whose conjugates do not
commute.
