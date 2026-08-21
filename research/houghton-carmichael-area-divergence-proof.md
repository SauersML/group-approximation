---
rg: 2
id: houghton-carmichael-area-divergence-proof
kind: route
title: Use the finitary-symmetric kernel and amenability of Houghton groups
target: houghton-carmichael-sections-have-unbounded-edge-area
requires:
  - hyperlinear-groups-force-area-divergence-in-high-chromatic-sections
---

The Houghton group `H_k` consists of permutations of `k` rays which are
eventual translations.  Its translation homomorphism has kernel
`Sym_fin(Omega)` and image `Z^(k-1)`.  The kernel is locally finite, so `H_k`
is amenable and hence hyperlinear.  Brown proved that `H_k` is finitely
presented for `k>=3` (indeed of type `F_(k-1)` but not `FP_k`; Johnson gave an
explicit presentation for `H_3`).

The finitary symmetric kernel contains every displayed cycle.  Direct
permutation multiplication gives `(HCA1)`, which is Carmichael's presentation
pattern.  Because `u_i=h_i b h_i^(-1)` as free words after choosing the
conjugate representative,

```text
u_i^3=h_i b^3 h_i^(-1),
```

so all cube areas equal the fixed finite number `Area_R(b^3)`.  The graphs are
the complete graphs `K_M`, whose chromatic numbers are `M`, and `b` is
nontrivial in `H_k`.  Applying
`hyperlinear-groups-force-area-divergence-in-high-chromatic-sections` proves
`(HCA2)` for every finite presentation and every choice of conjugators.
