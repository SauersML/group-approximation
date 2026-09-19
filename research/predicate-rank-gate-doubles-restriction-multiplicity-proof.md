---
rg: 2
id: predicate-rank-gate-doubles-restriction-multiplicity-proof
kind: route
title: Apply the rank dictionary to both blocks and count dimensions
target: predicate-rank-gate-doubles-restriction-multiplicity
requires:
  - boolean-predicate-is-one-rank-jump
  - clifford-commutator-rank-is-packet-dimension
---

The subgroup `A_f` is itself of the form `K(U_f)` for the leading block, with
the same central generators, so its sector commutation matrix is `U_f(x)`.  By
`boolean-predicate-is-one-rank-jump` that block is invertible for every Boolean
`x`, so `rank_F2 U_f(x) = N` and there is no degenerate part.  Applying
`clifford-commutator-rank-is-packet-dimension` with `m = r = N` gives sector
algebra `M_(2^N)(C)`, a simple algebra, so `A_f` has a unique simple module
`S_x` in the sector and `dim S_x = 2^N`.

For `B_f = K(M_f)` the sector commutation matrix is `M_f(x)`, of rank
`N + f(x)` by `(BPR1)`, so `dim T = 2^(N+f(x))` for every irreducible `T` in the
sector, again by `clifford-commutator-rank-is-packet-dimension`.

Restriction: the sector algebra of `A_f` is a full matrix algebra, hence has
`S_x` as its only simple module, so `T` restricted to `A_f` is a direct sum of
copies of `S_x`.  Counting dimensions,

```text
number of copies = 2^(N+f(x)) / 2^N = 2^(f(x)),
```

which is `(PRM1)`.  `(PRM2)` follows by additivity of restriction over a direct
sum decomposition into irreducibles over the fixed assignment.

The central characters match because `J` and the `z_l` lie in `A_f` by
construction, so the sector of `B_f` restricts to the sector of `A_f` and not to
a different one.
