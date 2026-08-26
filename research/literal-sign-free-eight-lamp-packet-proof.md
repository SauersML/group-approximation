---
rg: 2
id: literal-sign-free-eight-lamp-packet-proof
kind: route
title: Select the level-one block and its affine character holonomy
target: literal-sign-free-eight-lamp-packet
requires:
  - literal-kazhdan-clifford-inputs
  - literal-lamp-kernel-clifford-block-amalgam
artifacts:
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - GroupApproximation/Sofic/LiteralSignFreeQuotient.lean
---

The sign-free block decomposition is

```text
E/<w> = (*_(i in I) (C_2)^8) semidirect_product V.
```

Choose the block containing `dbar=q(tct^-1)`.  Its eight sites are the cosets
of `tBt^-1` in `B`, so the block stabilizer acts through the affine action on
`(F_2)^3`; this identifies the block group with `(C_2)^8` and the action with
`AGL_3(F_2)`.  The dual action permutes its 256 characters.

The literal compression relations give `sLs^-1<=L` and say that this
compressed subgroup fixes `dbar`.  Property `(T)` for `L` is
`literal-kazhdan-clifford-inputs`.  The parity class of `v_1` is nonzero, so
`q(v_1)` sends `dbar` to a different basis lamp.  Injectivity of the selected
free-product factor makes those two lamps distinct; equivalently, the
commutator detected in `LiteralSignFreeQuotient.signFree_collapse` is
nontrivial.

