---
rg: 2
id: char-zero-linear-bh-via-polynomial-s-integer-hosts
kind: route
title: Move the coordinates into Z[1/m][s_1..s_k] by Noether normalization, then apply the polynomial theorem
target: char-zero-linear-groups-satisfy-boone-higman
requires:
  - char-zero-linear-groups-embed-in-polynomial-s-integer-groups
  - polynomial-linear-groups-satisfy-boone-higman
---

Let `K` be a field of characteristic zero and let `H <= GL_n(K)` be finitely
generated.

1. **Coordinates.** By `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`,
   `H` embeds in `GL_M(R)` with `R = Z[1/m][s_1,...,s_k]`.
2. **Envelope.** By `polynomial-linear-groups-satisfy-boone-higman`, every subgroup
   of `GL_M(R)` embeds in a finitely presented simple group. So `H` does. ∎

**The host.** Take a prime `p` not dividing `m` and `n' = max(k+4, 2M)`. The simple
group is the commutator subgroup of a Röver--Nekrashevych group of
`R^(n') x| E_(n')(R)`, which is self-similar on `Z_p^(n') x Z_p^k`.

**Example.** `SL_3(Z[t^(+-1)]) <= SL_6(Z[s])` with `s = t + t^-1` (worked in the
claim). So `k = 1`, `m = 1`, `M = 6` and `n' = 12`.

**Trust.**
- Step 1 is standard commutative algebra, proved in
  `char-zero-polynomial-embedding-via-noether-normalization`.
- Step 2 rests on `polynomial-linear-groups-satisfy-boone-higman`. That claim is
  ESTABLISHED but not yet independently reviewed (lane `bh-poly-linear-review`).
