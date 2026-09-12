---
rg: 2
id: atlas-a4-classical-two-holonomy-profile-proof
kind: route
title: Exhaust both A8 automorphism cosets and count fixed nonzero vectors
target: atlas-a4-classical-two-holonomy-profile
requires:
  - atlas-a4-19243-classical-collapse
  - atlas-t30-is-one-parabolic-c3-bridge
---

The verifier enumerates all `20160` matrices in `GL_4(F_2)` twice, using
`x |-> g x g^(-1)` on the inner branch and
`x |-> g (x^(-1))^T g^(-1)` on the outer branch.  It evaluates the thirty
fixed packet words exactly over `F_2`; each branch leaves exactly thirty
alignments, and direct evaluation shows that `q_19243` is nonidentity at
every survivor.

For each surviving alignment it evaluates the two cocycles of `c=hk` and
`a=zb`.  If `v in GL_4(F_2)` has fixed-space dimension `d_v`, its permutation
on the fifteen nonzero vectors fixes `2^(d_v)-1` points.  Therefore

```text
15 ||pi_15(v)-I||_2^2=2(16-2^(d_v)),
```

so every displayed defect and ratio is an exact integer computation.  The
maximum of `E_2HOL/||q-I||_2^2` is `80/16=5` on the inner branch and
`84/16=21/4` on the outer branch.  The equality counters are fourteen and
ten respectively.  Assertions in the script pin the survivor count and
exclude a zero collision defect; the JSON artifact records every survivor
and the complete joint histogram.
