---
rg: 2
id: free-rounding-pays-the-number-of-fibre-conjugates
kind: claim
title: For any K, SDP 1-eps gives H free on G/K with mu(G minus H) <= 3 eps [G:N_G(K)] log_q k / c(G,m), and the factor [G:N_G(K)] is necessary
distinct_from:
  free-subgroup-rounding-fails-for-non-normal-fibres: that is the exponent-4 lower bound showing a factor N is forced; this is the matching upper bound over every finite group.
  normal-fibre-galois-games-round-linearly-over-all-groups: that is the normal case, where [G:N_G(K)] = 1; this covers arbitrary fibres at the cost of the number of conjugates.
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

**ESTABLISHED.** Let `G` be finite of exponent `m`, `K <= G` of order `k`, `q`
the least prime dividing `k`, `r = [G : N_G(K)]` the number of conjugates of
`K`, and `mu` symmetric and conjugation-invariant with an admissible certificate
of value `1 - eps`. With `c(G,m)` as in
`normal-fibre-galois-games-round-linearly-over-all-groups`, some `H` acting
freely on `G/K` has

```text
mu(G \ H) <= 3 eps r log_q k / c(G,m).
```

The kernels of good irreducibles are normal, so they meet every conjugate `K_j`
trivially. Run the halving chain of conjugated primitive kernels on `K_1`, then
on `K_2 cap L`, and so on, for at most `r log_q k` steps in all.

**The factor `r` is necessary.** In
`free-subgroup-rounding-fails-for-non-normal-fibres` (`G = F_2 wr F_2^n`,
`K = <e_0>`, `r = N`, `k = 2`, `m = 4`), every free `H` loses at least
`(N - 1) eps`. Since `G` is a 2-group, all primitive representations are linear,
the constant is `1 - cos(pi/2) = 1` (Theorem 14 of the part-3 artifact), and the
upper bound is `3 N eps`.

So free-subgroup rounding is linear in `eps log k` exactly when the number of
conjugates of the fibre is bounded. The value can still be `1 - O(eps)` when
`r` is large, through permutable subgroups; whether it always is at bounded
exponent is `galois-games-round-linearly-for-every-fibre-at-bounded-exponent`.
