---
rg: 2
id: halvable-corner-makes-elementary-groups-nonsofic
kind: claim
title: One nonzero halvable idempotent makes the elementary groups of an algebra over a finite field nonsofic
distinct_from:
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that needs a unital Leavitt family in the algebra itself; this needs only one nonzero idempotent e of a matrix amplification with eA isomorphic to eA plus eA, and carries nonsoficity out of the corner.
  leavitt-algebra-has-no-unital-rank-model: that is the rank-metric non-embedding of one algebra; this is the Hamming-metric conclusion for every algebra with a halvable corner.
---

**ESTABLISHED.** Let `k` be a finite field, `R` a countable unital `k`-algebra, `d >= 1`, and
`A = M_d(R)`. Suppose `A` has a nonzero idempotent `e` with `eA ≅ eA ⊕ eA` as right `A`-modules.
Equivalently, there are `s_0, s_1, t_0, t_1` in `eAe` with

```text
t_i s_j = delta_ij e,        s_0 t_0 + s_1 t_1 = e.
```

Then `GL_(nd)(R)` and `EL_(nd)(R)` are nonsofic for every `n >= 2`. When `d = 1`, the unit group
`R^x` is nonsofic as well.

**What it separates.** For a coefficient ring `R`, "no halvable idempotent in any `M_d(R)`" is a
necessary condition for any `EL_n(R)` to be sofic.
- A Sylvester matrix rank function gives `rk(e) = 2 rk(e)`, so it vanishes on every halvable
  idempotent.
- On a simple ring, a rank function with `rk(1) = 1` vanishes on no nonzero element: its zero set
  is a two-sided ideal. The same holds on every `M_d(R)`, which is again simple.
- Hence a simple ring with a unital rank model (a unital homomorphism into a rank ultraproduct of
  matrix algebras) has no halvable corner.

**Model test.**
- `L_k(1,2)` has `e = 1` halvable, and its `EL_n` are nonsofic, as the claim says.
- `LC(X, F_q) ⋊ Z` for an infinite minimal subshift has a unital rank model, its periodic-model
  embedding. So it has no halvable corner, consistent with `EL_3` of it being LEF.
- A field `k` has none: `k^d ≅ k^(2d)` is impossible.

Route: `halvable-corner-makes-elementary-groups-nonsofic-proof`.
