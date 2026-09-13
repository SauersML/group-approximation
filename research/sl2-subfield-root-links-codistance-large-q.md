---
rg: 2
id: sl2-subfield-root-links-codistance-large-q
kind: claim
title: For q = 2^f >= 32 every subfield root link u(F_q), v(sF_q) of SL_2(q^2) is connected with second singular value below 1 - 2/q
distinct_from:
  sl2-subfield-root-links-codistance-q8-q16: that certifies the same inequality for q = 8 and 16 by exact computation; this proves it for every q >= 32 by hand, from girth and a multiplicity bound
---

Let `q = 2^f >= 32`, `k = F_q ⊂ F = F_{q^2}`, `s ∈ F \ k`, and `Γ_s = Γ_{SL_2(F)}(u(k), v(sk))`. The graph
is `q`-regular with `n = q(q^4 - 1)` vertices on each side. Put `T_8(d) = 14d^4 - 28d^3 + 20d^2 - 5d`, the
number of closed walks of length 8 at a vertex of the `d`-regular tree.

**ESTABLISHED (by hand; unreviewed).**

```text
σ_2(Γ_s)^8  <=  ( n T_8(q) / q^8  -  1 ) / (q^2 - 1)  <  14q / (q^2 - 1)  <  (1 - 2/q)^8 .
```

Consequences:
- `Γ_s` is connected, so `<u(k), v(sk)> = SL_2(F)`.
- `cos ∢(V^{u(k)}, V^{v(sk)}) < 1 - 2/q` in every unitary representation
  (`coset-graph-singular-values-bound-fixed-space-angles`).

**Numbers.**
- `q = 32`: `σ_2 <= 0.8948`, against the threshold `0.9375`.
- `q = 64`: `σ_2 <= 0.8237`, against `0.96875`.
- As `q -> ∞`, `σ_2 <= (14/q)^{1/8} (1 + o(1))`.

The actual values are near `2/√q`: the Lanczos values are `0.683` for `q = 8` and `0.496` for `q = 16`.

**Where the method stops.** For `q = 16` the right-hand bound is `0.9677 > 7/8`, and for `q = 8` it is
worse. Those two cases are certified by computation in `sl2-subfield-root-links-codistance-q8-q16`.

**Model tests.**
- The tree count `T_8(q)` equals the computed closed-walk counts `W_8 = 2092, 44248, 807856` for
  `q = 4, 8, 16`.
- The multiplicity step is consistent with a known spectrum. On the root link of `SL_2(q)`
  (`sl2-opposite-root-subgroups-codistance-inverse-sqrt-q`), `σ_2 = q^{-1/2}` has multiplicity
  `q^2 - q - 2`, which is at least the minimal degree `q - 1` of `SL_2(q)`.

Proof: `sl2-subfield-root-links-codistance-large-q-proof`.
