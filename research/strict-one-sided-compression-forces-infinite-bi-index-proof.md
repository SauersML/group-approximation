---
rg: 2
id: strict-one-sided-compression-forces-infinite-bi-index-proof
kind: route
title: Inverse powers of a strict compressor give pairwise distinct one-coset double cosets
target: strict-one-sided-compression-forces-infinite-bi-index
requires: []
---

A complete direct proof.  `requires: []` is a proof commitment; nothing
external is used.  The target's display has damaged TeX escapes
(`Hackslash`, `	ag`), so the derivation is written out again here in plain
notation.  It checks (SCI1)--(SCI5) of the target.

Let `H <= G` and `t in G` with `t H t^(-1) < H` strictly (SCI1).

**(SCI4) Iterated strictness.**  From `t H t^(-1) <= H`, induction gives
`t^j H t^(-j) <= H` for all `j >= 0`.  Conjugation by `t^(k-1)` is a
bijection of `G`, so it carries the strict inclusion `t H t^(-1) < H` to a
strict inclusion:

```text
t^k H t^(-k)  <  t^(k-1) H t^(-(k-1))  <=  H        (k >= 1).
```

**(SCI3) One-coset double cosets.**  Fix `n >= 1`.  For `h, h' in H`,

```text
h t^(-n) h' = t^(-n) (t^n h t^(-n)) h'  in  t^(-n) H,
```

because `t^n h t^(-n) in H` by the induction above.  So
`H t^(-n) H <= t^(-n) H`.  The reverse inclusion is trivial, since
`1 in H`.  Hence `H t^(-n) H = t^(-n) H`.

**Pairwise distinct.**  Suppose `t^(-m) H = t^(-n) H` with `m > n >= 1`.
Then `t^n t^(-m) = t^(-(m-n)) in H`, so `t^(m-n) in H`.  Put `k = m - n >= 1`.
Conjugation by an element of `H` maps `H` onto `H`, so
`t^k H t^(-k) = H`, contradicting (SCI4).  So the double cosets
`H t^(-n) H`, `n >= 1`, are pairwise distinct sets.  Therefore
`|H \ G / H| = infinity` (SCI2).

**(SCI5) Infranormal non-normal pairs.**  Let
`P_H = {g in G : g H g^(-1) <= H}` generate `G`, and suppose `H` is not normal
in `G`.  If every `g in P_H` satisfied `g H g^(-1) = H`, then
`P_H <= N_G(H)`.  A subgroup containing a generating set contains the group it
generates, so `G <= N_G(H)` and `H` would be normal, a contradiction.  So some
`t in P_H` is a strict compressor, and (SCI2) gives `|H \ G / H| = infinity`.
`∎`

(SCI6), the Fournier--Facio instance, is an application recorded in the target.
It is not needed for (SCI2) or (SCI5), and this route does not certify it.
