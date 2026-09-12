---
rg: 2
id: wreath-soficity-is-decided-by-the-base-pair
kind: claim
title: Two compression pairs carry the wreath family and only one of them is sofic
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
distinct_from:
  wreath-sofic-not-mf: that states the sofic-and-not-MF conjunction for the mod-two wreath over the affine pair; this states the scope rule separating that group from the Kun--Thom-pair wreath, which is the identification step that a soficity claim about "the wreath" has to perform before it means anything.
  a5-wreath-contains-binary-kun-thom-wreath: that embeds the binary wreath in the A5 wreath over the PINNED KUN--THOM action and concludes nonsoficity there; this records that the same embedding argument does not reach the affine-pair wreath, which is the group the radical theorems are about.
  wreath-not-sofic: that is the nonsoficity verdict over the Kun--Thom Laurent pair; this is the scope rule that stops it being applied to the affine pair.
---

The graph carries the generalized wreath construction over **two different
compression pairs**, and the soficity verdict flips between them.  Neither
verdict transports.

1. **The Kun--Thom Laurent pair.**  `Gamma = EL_r(R_+)`,
   `G = EL_r(R) x| SL_d(Z)` with `R_+ = F_q[x_1..x_d]`,
   `R = F_q[x_1^(±1)..x_d^(±1)]` and `SL_d(Z)` acting by monomial
   substitutions.  Over `G/Gamma` the wreath product is **not sofic**, by
   Kun--Thom Theorem A, and the A5-lamp version is not sofic either, since it
   contains the binary one sitewise.

2. **The affine doubling pair.**  `G* = (Z[1/2]^3 x| SL_3(Z)) x| Z` with the
   doubling stable letter, and its coset space `X = G*/Gamma*`.  Over this pair
   the telescope-window structure restores soficity: the mod-two wreath is a
   finitely generated **sofic** group that is not MF.

**The scope rule.**  Soficity of a generalized wreath product here is a
property of the base pair's finite-window geometry, not of the wreath shape or
of the lamp.  So a nonsoficity verdict proved over pair 1 says nothing about
pair 2, and the sitewise-involution embedding that transports nonsoficity from
binary to `A_5` lamps transports it only *within* a fixed pair.

**Why this needs its own node.**  Every radical theorem of this family --
`compression-wreath-five-radicals-coincide`, `wreath-compression-mf-radical`,
`simple-lamp-radical-one-relation` -- is stated over pair 2, while the
nonsoficity nodes and the non-hyperlinear candidate route
`nonhyperlinear-via-simple-lamp-action-recovery` are stated over pair 1.  The
two families share the words "the wreath", "the A5 wreath" and "the compression
pair", and the distinction has until now been recorded only inside
`distinct_from` prose.  Reading a pair-1 nonsoficity node as a fact about the
pair-2 group is a live failure mode: it produced a false ESTABLISHED claim in
this graph on 2026-08-23, which this node replaces.
