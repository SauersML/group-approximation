---
rg: 2
id: galois-games-round-linearly-for-bounded-fibre-size
kind: claim
title: For every K <= G of order k and exponent m, SDP 1-eps gives val >= 1 - 3 eps min(k, [G:N_G(K)]) log_q k / c(G,m), linear in eps at fixed k
distinct_from:
  abelian-normal-closure-fibres-round-linearly: that removes all dependence on the number of conjugates when K lies in an abelian normal subgroup; this covers every K at the cost of a factor k.
  free-rounding-pays-the-number-of-fibre-conjugates: that is the [G:N_G(K)] half of the minimum, through free subgroups; this adds the k half, through permutable subgroups.
---

**ESTABLISHED.** Let `G` be finite of exponent `m`, `K <= G` of order `k`, `q`
the least prime dividing `k`, and `mu` symmetric and conjugation-invariant with
`SDP Gal(G,K,mu) >= 1 - eps`. With `c(G,m)` as in
`normal-fibre-galois-games-round-linearly-over-all-groups`, some `L`
normalized by `K` has `L cap K = {e}` and
`mu(G \ L) <= 3 eps k log_q k/c(G,m)`. Together with
`free-rounding-pays-the-number-of-fibre-conjugates`,

```text
val Gal(G,K,mu) >= 1 - 3 eps min(k, [G : N_G(K)]) log_q k / c(G,m).
```

**Construction.** Run the primitive-kernel halving chain. At each step replace the
chosen conjugate `L_i` of a primitive kernel by its `K`-core
`intersection over b in K of b L_i b^-1`. The core is normalized by `K`, still
omits the chosen `a`, and costs at most `[K : K cap N_G(L_i)] <= k` times as
much. The final `L` permutes with `K`, and permutable rounding gives the value.

**Meaning.** At bounded exponent and bounded alphabet, symmetric Galois games
never show square-root loss. The loss in `eps` is linear for every fibre, not
only normal ones. The odd cycle `Z_(2n)` loses `sqrt(eps)` only because its
exponent grows. This contrasts with general unique games. There
Charikar--Makarychev--Makarychev round to `1 - O(sqrt(eps log k))` [recalled],
and square-root loss already occurs at `k = 2` on odd cycles.

**What stays open.** The factor `k` is `1` when `K` is normal or has abelian
normal closure. Whether it can always be replaced by a constant is
`galois-games-round-linearly-for-every-fibre-at-bounded-exponent`. That matters
only when `k` and `[G : N_G(K)]` are both large.
