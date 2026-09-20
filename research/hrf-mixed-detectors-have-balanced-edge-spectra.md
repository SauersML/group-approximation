---
rg: 2
id: hrf-mixed-detectors-have-balanced-edge-spectra
kind: claim
title: Every nonzero scalar five-twist detector has regular edge spectra and two exact composition-factor balances
distinct_from:
  hrf-amplified-sym4-five-twists-have-no-detectors: that excludes a specified stable isotypic family; this gives necessary integer balance conditions on arbitrary possibly nonsemisimple vertex modules
artifacts:
  - research/artifacts/hrf-mixed-spectral-balance-2026-09-20.md
---

Let `S=PSL_2(F_19)` and pin the three cyclic triangle edges by the
classes of `[[2,11],[16,3]]`, `[[5,11],[4,9]]`, and
`[[6,15],[12,8]]`. For a nonzero `d in F_5^3`, impose central
`Z^5=1` and edge relations `s_i(xij)=Z^(dij)s_j(xij)`.

In every positive finite-dimensional representation over an
algebraically closed field of characteristic different from five
(including characteristic zero) taking `Z` to a
nontrivial scalar, the dimension is `5m` and every vertex restriction
to every cyclic edge is `m` copies of the regular `C_5` module.
This holds without any semisimplicity assumption on vertex modules.

In characteristic 19 specifically, at each vertex let `n_r` denote the composition multiplicity of
the defining-characteristic simple `L_r=Sym^r(K^2)`, for even
`r=0,...,18`. Then the following exact integer equations hold:

```
n0+n10=n8+n18,   n2+n12=n6+n16.
```

Conversely these two equations are exactly the condition that a
vertex composition vector has uniform order-five spectrum. They
do not assert that any balanced vertex triple extends to a detector.

Proof: [[hrf-mixed-detectors-have-balanced-edge-spectra-proof]].
