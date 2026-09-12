---
rg: 2
id: fused-cross-return-positive-l0-cancellation-proof
kind: route
title: Fuse the exact branch returns and apply their positive signed-Hecke typing
target: fused-cross-returns-cancel-positive-l0-gauge
requires:
  - cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
  - signed-hecke-normalizer-has-eight-external-root-returns
---

Use `(CWR6)--(CWR7)` with `g=r` in branch zero and `g=p` in branch
one.  Since `pr=q_0` and `rp=q_1`, this gives `(FAR2)`.  Root-subgroup
addition and `q_0+q_1=1` give `(FAR3)`; the same argument gives the input
fusion with coefficient `p+r`.

In source-to-target notation, `x_(7,k)(1)` is the arrow `k->7`.  For
`k=6,9`, both arrows occur among the ten generators in `(ERN1)`, and both
have positive character.  The defining Reynolds identity gives

```text
rho(x_(7,k)(1))Q=lambda_0(x_(7,k)(1))Q=Q.
```

Each returned `O_i` preserves `Q` by `(CWR8)`.  Restrict `(FAR3)` to `QH`
to obtain `b_0b_1=1`.  Characteristic two makes every elementary root an
involution, so `b_i^2=1` and therefore `b_0=b_1`.

The old `S_3 times S_3` assignment omitted the positive-`L_0` row: its
value `b_0b_1=(b,b)` contradicts the displayed Reynolds identity.  Hence
it is not a model of the established signed-Hecke occurrence table.
