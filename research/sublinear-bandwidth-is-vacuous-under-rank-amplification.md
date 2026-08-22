---
rg: 2
id: sublinear-bandwidth-is-vacuous-under-rank-amplification
kind: claim
title: Sublinear bandwidth is vacuous under rank-metric amplification
distinct_from:
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: that uses one fixed commutative cyclic algebra to extract residue-field modes; arbitrary band matrices have no common mode algebra.
  atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch: that fixes two diagonal phase types and proves a flag rank floor; this applies to every rank-metric tuple before imposing a phase or flag decomposition.
  growing-rank-decoder-is-linear-soficity: that identifies arbitrary rank approximations with rank-ultraproduct embeddings; this proves that an asymptotic bandwidth restriction does not shrink that class.
---

Let `E` be any fixed finite menu of matrix Laurent equations over a field
`k`.  The following two existence statements are equivalent:

1. there are invertible matrix tuples `T_n` of sizes `d_n` for which every
   normalized-rank residual in `E` tends to zero;
2. there are such tuples of sizes `D_n` for which both every variable and its
   inverse have bandwidth `o(D_n)`.

Indeed, from (1) choose any integers `r_n` tending to infinity and put

```text
T_hat_n = T_n direct_sum ... direct_sum T_n       (r_n copies),
D_n = r_n d_n.                                      (SBV1)
```

In the contiguous-copy ordering, every variable and inverse has bandwidth at
most `d_n-1`, hence relative bandwidth at most `1/r_n`.  Laurent evaluation
commutes with direct sums, so for every residual `R` one has

```text
rank R(T_hat_n) / D_n = rank R(T_n) / d_n.          (SBV2)
```

The converse is immediate by forgetting bandwidth.  The same proof works in
fixed coefficient blocks and preserves every normalized-rank separation
condition.

Applied to the repeated-module Atlas packet with collision `19243` and q14,
this shows that width-growing noncirculant band gauges are exactly as general
as unrestricted rank-metric microstates.  Sublinear bandwidth alone cannot
support a Fourier-mode, domain-wall, or finite-section promotion theorem.
