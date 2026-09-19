---
rg: 2
id: prime-scaling-maximal-kazhdan-blocks
kind: claim
title: Prime scaling factors are recorded by maximal Kazhdan block radicals
distinct_from:
  scaling-family-non-mf: that proves every scale is non-MF but does not distinguish abstract isomorphism types.
  scaling-family-pairwise-nonisomorphic: that asks for all integer scales; this computes a complete intrinsic invariant on the prime subfamily.
artifacts:
  - research/artifacts/prime-scaling-kazhdan-block-rigidity-2026-08-30.md
---

Let `p` be prime and let `E_p` be the member of the scaling family whose
stable letter multiplies the three translations by `p`.  Put
`B_{p,1}=t^(-1)Bt`.  Then `E_p` has the Bass--Serre decomposition

```text
E_p = (V_p x <w>) *_(B_(p,1) x <w>)
      (ClLamp(p^3) semidirect B_(p,1)).                    (PK1)
```

The maximal property-`(T)` subgroups of `E_p` are exactly the conjugates
of

```text
L_p = ClLamp(p^3) semidirect B_(p,1).                      (PK2)
```

Moreover, `ClLamp(p^3)` is the unique largest finite normal subgroup of
`L_p`, and

```text
|ClLamp(p^3)| = 2^(p^3+1).                                (PK3)
```

Thus the number `2^(p^3+1)` is an invariant of the abstract group `E_p`:
it is the order of the finite radical of any maximal property-`(T)`
subgroup.

DERIVATION
prime-scaling-maximal-kazhdan-blocks-proof
