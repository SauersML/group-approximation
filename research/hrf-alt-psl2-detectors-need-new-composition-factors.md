---
rg: 2
id: hrf-alt-psl2-detectors-need-new-composition-factors
kind: claim
title: For primes at least five, PSL2-vertex twist detectors need a cyclic p-factor or a non-PSL2 simple composition factor
distinct_from:
  hrf-alt-edge-twist-finite-detector-spectrum: that identifies the central detector through a Schur-multiplier discrepancy; this excludes every finite detector quotient assembled from any PSL2 simple groups and cyclic groups of order prime to the twist prime
artifacts:
  - research/artifacts/hyperbolic-rf-alternatives-2026-09-20.md
---

Let `S={PSL_2(q) : q>=4 is a prime power}`. Fix any prime `p>=5`.
Let `Λ` be a nonpositively curved triangle colimit with vertex groups in `S`,
cyclic order-`p` edge groups, and trivial face group. These include the
corresponding perfect-vertex candidates in
[[hyperbolic-triangle-colimit-with-persistent-edge-twist]].

Let `c` be a nonzero edge twist and `Λ_c` its central `C_p` extension.
For any finite quotient `ρ:Λ_c ->> F` detecting `C_p`, the quotient
`Q=F/ρ(C_p)` must have a composition factor outside the collection

```
S union {C_l : l is prime and l != p}.
```

In particular, combining arbitrarily many quotients of `Λ` onto the
PSL2 simple groups, by taking their product image, cannot supply the
quotient `Q` of a central detector. Nor can any finite group whose
composition factors stay in that collection. A detecting quotient must
introduce a `C_p` composition factor or a non-PSL2 nonabelian simple factor;
these conditions remain only necessary.

**Status:** proved finite-group obstruction, independently reviewed on
2026-09-20, including both characteristic cases, extension closure, and
the product-image consequence. See the cross-review in
`research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md`.
It does not exclude all finite quotients and proves no persistence.
It concerns the quotient after dividing out the detected central `C_p`,
not `F` itself (which necessarily already has a `C_p` factor).

Proof: [[hrf-alt-psl2-detector-composition-obstruction-proof]].
