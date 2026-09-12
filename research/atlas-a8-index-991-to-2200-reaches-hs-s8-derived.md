---
rg: 2
id: atlas-a8-index-991-to-2200-reaches-hs-s8-derived
kind: claim
title: The first simple A8 overgroup after A11 is the S8-derived class in HS at index 2200
artifacts:
  - experiments/atlas_a8_index_991_to_2200_order_sieve.py
  - experiments/atlas-a8-index-991-to-2200-order-sieve.json
distinct_from:
  atlas-a8-index-507-to-990-reaches-natural-a11: that reaches a natural alternating-support class; this crosses the first projective odd-characteristic candidate and isolates a sporadic S8-derived class.
  atlas-a8-index-33-to-89-is-orthogonal-sp6: that also obtains A8 as the derived subgroup of a maximal S8, but in Sp6(2); this proves the corresponding and genuinely new HS boundary.
---

Let `S` be finite simple and suppose `A~=A8<S`.  If

```text
991 <= [S:A] <= 2200,                               (SIH1)
```

then equality holds on the right:

```text
S~=HS,       [S:A]=2200.                            (SIH2)
```

Moreover `A` is the derived subgroup of a maximal `S8<HS`.  These `A8`
subgroups form one `HS`-conjugacy class and

```text
N_HS(A)=S8,       N_HS(A)/A ~= Out(A8) ~= C2.       (SIH3)
```

Thus all abstract marking automorphisms are induced by the ambient
normalizer.  After fixing the first marked chart, the full equality problem
is one conjugator family `g in HS`; there is no second graph-parity screen.

