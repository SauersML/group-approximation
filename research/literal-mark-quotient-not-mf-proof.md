---
rg: 2
id: literal-mark-quotient-not-mf-proof
kind: route
title: The level-one block carries an eight-coordinate involutive witness
target: literal-mark-quotient-not-mf
requires: [literal-lamp-kernel-clifford-block-amalgam, compression-torsion-collapse]
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean
---

## Why sufficient

By `literal-lamp-kernel-clifford-block-amalgam`, the lamp kernel of `E` is
the amalgam of order-512 Clifford blocks over the common central `<w>`;
modulo `<w>` each block becomes elementary abelian `(Z/2)^8` and the lamp
kernel of `E/<w>` is their free product, with `V` permuting blocks and the
block set `V`-isomorphic to the site set.  The level-one root block is the
eight sites `{(1,[v]) : v in Z^3/2Z^3}`; it contains both marked sites
`tau o = (1,[0])` and `v_1 tau o = (1,[e_1])`.  Every element of the base
`Gbar = Z^3 semidirect SL_3(Z)` preserves this block: integral translations
and `SL_3(Z)` preserve the image of `Z^3` in `Z[1/2]^3/2Z^3`.

Apply the involutive collapse (formalized endpoint behind
`compression-torsion-collapse`) in `H = E/<w>` with `L` the image of the
base, `s = t`, and witness `k = dbar`, the image of `d = tct^{-1}`:

- (W1) `dbar^2 = 1` since `c^2 = 1`.
- (W2) `[d, t iota(B) t^{-1}] = 1` holds exactly in `E`: `c` commutes with
  the base by the defining relators, conjugate by `t`.
- (W3) the `L`-conjugates of `dbar` are the eight coordinate involutions
  of the level-one root block — one abelian `(Z/2)^8` factor — so they
  commute pairwise.  This is the step that fails in `E` itself (there the
  block is Clifford, and the failure IS `w`) and becomes true exactly in
  the quotient.

The collapse places `[gamma, dbar] in Rad_MF(E/<w>)` for every `gamma` in
the image of the base.  Take `gamma = v_1`:
`[v_1, dbar] = ubar^{-1}` where `ubar` is the image of the unsquared
defect, and it is nontrivial because the two coordinates `[0]` and `[e_1]`
of the block are distinct and the block embeds into the free product,
which embeds into `E/<w>` (both by the block-amalgam normal form).

Hence `ubar` is a nontrivial element of `Rad_MF(E/<w>)`, and no corona
representation of `E/<w>` is injective.
