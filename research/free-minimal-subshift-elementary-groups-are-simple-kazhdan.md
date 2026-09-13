---
rg: 2
id: free-minimal-subshift-elementary-groups-are-simple-kazhdan
kind: claim
title: For every free minimal Z^d subshift, elementary matrices over its crossed product algebra give an infinite simple Kazhdan group that is linear sofic
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that is the d = 1 coefficient ring, which is LEF and so makes its elementary group LEF; this is the Z^d family, where for SFTs without finite orbits no LEF certificate is available and only linear soficity is proved.
  lef-kazhdan-group-without-finite-quotients-exists: that is the d = 1 LEF Kazhdan group without finite quotients; this proves simplicity modulo centre for every free minimal Z^d subshift through box towers.
artifacts:
  - research/artifacts/free-minimal-subshift-elementary-groups-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `q` be a prime power, `X ⊆ A^(Z^d)` a free minimal subshift, and
`R = LC(X, F_q) ⋊ Z^d`. For every `n >= 3` put `G_n = EL_n(R)`.
- Every normal subgroup of `G_n` is central or all of `G_n`, and `Z(G_n) ⊆ F_q^x 1_n`.
- `S_n = G_n/Z(G_n)` is an infinite simple group with property (T), and it is `F_q`-linear sofic.

The artifact writes the case `n = 3`. The argument does not use the rank beyond `n >= 3`: level
ideals and signed permutations work for all `n >= 3`, the local matrix size is
`D = n|B_(m')| >= 27`, and the adjoint model of `rank-modelled-simple-rings-give-linear-sofic-projective-el`
holds for all `m >= 2`.

**Proof outline.**
- **Property (T).** `R` is a finitely generated ring (`elementary-groups-over-fg-rings-have-property-t`).
- **Linear soficity.** It comes from the Følner rank model and the adjoint
  (`free-minimal-crossed-products-are-simple-with-rank-models`,
  `rank-modelled-simple-rings-give-linear-sofic-projective-el`).
- **Simplicity.** It transcribes the reviewed root detection of the case `d = 1`, with box towers
  `B_m ⊆ Z^d` in place of intervals and cylinders of large radius as bases. Freeness and compactness
  give long return times.
  - Absorption lemma: boxes grow by the propagation.
  - Case 1 (a non-scalar local value): `SL_D(F_q)` with `D = 3|B_(m')| >= 27`.
  - Case 2 (scalar values): conjugation of `chi_Y u^(e_1)` just outside the tower produces a root.

**Scope.**
- For `d = 1` this is the reviewed Pestov 9.1 group, which is LEF.
- For `d >= 2` no LEF or sofic certificate is claimed (`free-minimal-subshift-elementary-groups-are-sofic`).
- If the subshift is a quantum rigid SFT, `R` is finitely presented
  (`sft-crossed-product-fp-iff-quantum-rigid`), and `S` becomes the candidate of the ring route.

Route: `free-minimal-subshift-elementary-groups-are-simple-kazhdan-proof`.
