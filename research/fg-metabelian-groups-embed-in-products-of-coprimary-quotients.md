---
rg: 2
id: fg-metabelian-groups-embed-in-products-of-coprimary-quotients
kind: claim
title: A finitely generated metabelian group embeds in a finite product of quotients of pure characteristic, each linear over a field of that characteristic
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that is Boone--Higman for linear groups over one field of characteristic zero; this is a structure theorem splitting a metabelian group into linear quotients of pure characteristic, with no envelope.
  positive-char-linear-groups-satisfy-boone-higman: that is Boone--Higman for linear groups over one field of positive characteristic; this is the structural reduction that turns metabelian inputs into such linear quotients plus a product step.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a finitely generated metabelian group.

(a) There are finitely many normal subgroups `M_1, ..., M_r <= G'` with
`M_1 ∩ ... ∩ M_r = 1`, such that each derived subgroup `(G/M_i)' = G'/M_i` is
either torsion-free or of exponent a power of a single prime `p_i`. So `G` embeds
in `G/M_1 x ... x G/M_r`, a finite product of metabelian quotients of `G`.

(b) Each factor is linear over a field of its characteristic.
- *Torsion-free derived subgroup:* characteristic zero (Remeslennikov 1969, as
  quoted by Wehrfritz).
- *Derived subgroup a `p`-group:* characteristic `p` (Wehrfritz 1975, Theorem 1.1).

Merging the factors of equal characteristic gives an embedding
`G -> G_0 x G_(p_1) x ... x G_(p_s)`. Here the primes `p_j` are distinct, and
each `G_c` is a quotient of `G` that is linear over one field of characteristic
`c`. In Wehrfritz's words (Corollary 1.2), `G` is a quasi-linear group: a group
of matrices over a finite direct sum of fields.

**Mixing is unavoidable.** `(Z wr Z) x (Z/p wr Z)` is linear over no field
(artifact §2).

The derivation is `fg-metabelian-coprimary-quotients-proof`.
