---
rg: 2
id: leavitt-compression-preserves-root-position-support
kind: claim
title: The canonical Leavitt compression preserves root-position support and misses the Singer move
invalidates:
  - leavitt-compression-cell-supplies-moving-square-bridges
artifacts:
  - research/leavitt-compression-root-support-proof.md
  - GroupApproximation/Leavitt/LeavittMatrixCompression.lean
distinct_from:
  fano-semidir-bridges-are-wrong-subgroup-or-gauged: that treats words inside the finite Fano semidirect packet; this treats the canonical full-Leavitt corner endomorphism and its Whitehead implementation outside that packet.
  literal-whiteheads-give-gauged-moving-bridge-table: that gives exact subgroup-moving bridges with the wrong reservoir typing; this proves that the natural ungauged coefficient compression does not move the subgroup at all.
  el20-six-moving-coefficient-square-bridges: that still permits a genuinely mixed coefficient/opposite-root word; this rules out only the canonical Leavitt self-similarity and Hilbert-hotel compression cell.
---

**ESTABLISHED ROOT-POSITION FENCE.**  Let
`R=L_(F_2)(1,2)`, put `p_1=s_1t_1`, and let

```text
alpha(M)=p_1 I+s_0 M t_0                                (LCR1)
```

be the canonical Leavitt matrix-compression endomorphism.  On every
elementary root it acts by

```text
alpha(x_ab(r))=x_ab(s_0 r t_0).                         (LCR2)
```

Thus `alpha` changes the coefficient but preserves the ordered root position
`(a,b)` exactly.  More generally, it preserves every zero pattern defined
only by the matrix indices.

In the actor basis `(2,4,5,6,7,8,9)`, the signed Hecke subgroup `L_0`
contains

```text
d=x_28(1),                                              (LCR3)
```

and every displayed generator of `L_0` fixes the basis vector `e_7`.
Consequently every element of `alpha(L_0)` still fixes `e_7`.  The first
Singer head `t=t_1`, however, satisfies

```text
t d t^(-1)=x_27(1),                                    (LCR4)
```

which does not fix `e_7`.  Hence

```text
alpha(L_0) != tL_0t^(-1).                              (LCR5)
```

If `Q=e_(L_0,lambda_0)` is the signed Reynolds idempotent, injectivity of
`alpha` makes its group-algebra support exactly `alpha(L_0)`, whereas the
support of `tQt^(-1)` is `tL_0t^(-1)`.  Therefore

```text
alpha(Q) != tQt^(-1).                                  (LCR6)
```

The same conclusion holds for any coordinate copy of the explicit
20-by-20 Whitehead/Hilbert-hotel cell on which conjugation implements
`alpha`: its compression of `Q` has range Gram `alpha(Q)`, not the next
Singer cut.  Its six Singer conjugates merely repeat the same mismatch.

Thus the most canonical full-Leavitt word outside the finite Fano packet is
ungauged but has the wrong full Gram.  A successful bridge cannot be a pure
Leavitt self-similarity/compression occurrence.  It must contain an
additional subgroup-moving matrix-index word.  The literal such word is the
gauged Whitehead from `literal-whiteheads-give-gauged-moving-bridge-table`,
so the remaining search is sharply for a genuinely mixed coefficient and
opposite-root occurrence whose extra relation also removes that gauge.

No Property `(T)`, trace-profile hypothesis, or Steinberg-kernel lift is
used.

DERIVATION
leavitt-compression-root-support-proof
