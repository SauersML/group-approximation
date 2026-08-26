---
rg: 2
id: fixed-arity-mark-fusion-has-finite-character-model
kind: claim
title: Every fixed product-fusion of conjugate marks has a finite character model
invalidates:
  - fixed-arity-mark-fusion-closes-tagged-code
artifacts:
  - research/fixed-arity-mark-fusion-character-proof.md
distinct_from:
  bounded-tagged-mark-seam-complex-has-finite-row-range: that reduces bounded pairwise seams to one based centralizer cocycle; this treats a genuinely non-pairwise cell with no distinguished pairwise seam decomposition.
  payload-range-sum-whitehead-has-three-character-model: that realizes the specific binary relation C_0C_1=J and attaches two branch Pauli pairs; this gives arbitrary fixed arity and isolates the general character-linear fusion escape.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that closes the finite binary coefficient actor menu; this applies directly to proposed chromatic chart-mark fusion cells, independently of the coefficient actors inside each chart.
---

**ESTABLISHED FIXED-ARITY FUSION FIREWALL.**  Fix `r>=3`.  A bare
non-pairwise fusion prototype has conjugated involutions

```text
Z_j=g_j z g_j^(-1),                 1<=j<=r,            (FMF1)
```

and one higher-arity boundary

```text
Z_1 Z_2 ... Z_r=z.                                      (FMF2)
```

No pairwise equality among the `Z_j` is assumed.  This whole table has an
exact finite marked model.

On `H_r=l^2(F_2^r)`, for `v in F_2^r` put

```text
D_v delta_x=(-1)^(v dot x) delta_x.                    (FMF3)
```

Let `v_j=e_j` and `v=e_1+...+e_r`.  Then

```text
D_(e_1)...D_(e_r)=D_v.                                 (FMF4)
```

Every nonzero `D_w` has equal positive and negative rank.  The permutation
representation of `GL_r(F_2)` on `F_2^r` is transitive on the nonzero
vectors, so there are permutation unitaries `G_j` with

```text
G_jD_vG_j^(-1)=D_(e_j).                                (FMF5)
```

Taking `z=D_v`, `Z_j=D_(e_j)`, and `g_j=G_j` proves
`(FMF1)--(FMF2)`.  The marks are pairwise distinct, so the fusion is
genuinely non-pairwise, while the `z=-1` projection has rank `2^(r-1)`.

The model also accepts a fixed marked payload in every chart.  Tensor with
one Pauli pair and control it by `(1-D_v)/2`; define the payload in chart
`j` by conjugation with `G_j`.  Every local marked commutator and every
fusion occurrence remains exact.  The generated actor is a finite subgroup
of

```text
(C_2)^r semidirect GL_r(F_2),                           (FMF6)
```

so regular amplification supplies arbitrary finite multiplicity without
changing any defect.

Consequently a fixed ternary or higher product of conjugated copies of the
mark does not align the chart gauges and cannot by itself prove a uniformly
filled tagged edge.  To escape this firewall, the fusion boundary must read
noncommuting row/column payloads in an address-sensitive way, or its arity
or character rank must grow.  No Property `(T)`, Kazhdan input, matrix
approximation theorem, trace hypothesis, or literature result is used.

## Attempts

- **Use a ternary relation instead of pairwise seams.**  At `r=3`, the
  three distinct signs `D_(e_1),D_(e_2),D_(e_3)` multiply to the equally
  ranked conjugate `D_(e_1+e_2+e_3)` exactly.
- **Attach one fixed Pauli payload to each fused chart.**  Conjugating the
  controlled payload with the same `G_j` preserves every local commutator;
  the fusion still sees only the abelian character signs.

DERIVATION
fixed-arity-mark-fusion-character-proof

