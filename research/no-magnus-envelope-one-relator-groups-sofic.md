---
rg: 2
id: no-magnus-envelope-one-relator-groups-sofic
kind: claim
title: Torsion-free two-generator one-relator groups whose Magnus pieces admit no amenable envelope are sofic
distinct_from:
  unpeelable-extreme-one-relator-groups-sofic: that is the remainder after syllable peeling; this is the smaller remainder after amenable envelopes, which also close nested-conjugator relators with many extreme syllables.
  torsion-free-two-generator-one-relator-groups-sofic: that is the whole torsion-free two-generator class; this is only the part no amenable-envelope argument reaches.
  magnus-staggered-chain-sofic: that asks for all staggered kernels; this asks only for kernels whose pieces cannot be embedded over a Magnus subgroup into an amenable-edge envelope.
artifacts:
  - research/artifacts/amenable-envelope-magnus-piece-sofic-2026-09-11.md
---

OPEN. Let `G = <a,t | w>` be torsion-free. Suppose that for every free basis
in which `t` has exponent sum zero in `w`, neither `(B_0, F_-)` nor
`(B_0, F_+)` has an amenable envelope. Claim: `G` is sofic.

With [[amenable-envelope-magnus-piece-one-relator-sofic]] this gives
[[unpeelable-extreme-one-relator-groups-sofic]] and hence Pestov 4.10.

## Attempts

1. **Envelopes.** *Provably stop here.* For `n - m >= 2` and non-free
   `B_0`, an envelope forces a nontrivial splitting of `B_0` over amenable
   subgroups with `F_-` elliptic. Every group in this class therefore has, in
   every zero-exponent basis, Magnus pieces with no such relative splitting.
   One-ended hyperbolic pieces with trivial relative JSJ decomposition are the
   model case. The converse is also in place:
   [[relative-amenable-hierarchy-magnus-one-relator-sofic]] shows that a finite
   chain of such splittings, descending to `F_-` through the vertex groups that
   contain it, already suffices. The remaining core is
   [[no-magnus-hierarchy-one-relator-groups-sofic]].
2. **Profinite gluing.** *No permanence theorem.* In the model case the piece
   is virtually special and `F_-` is quasiconvex, hence separable. Residual
   finiteness of `S *_F B` from a residually finite `B` with separable `F`
   needs compatible finite quotients of `S` as well. Soficity of the previous
   window supplies approximations, not quotients, and none can be restricted
   to finite-quotient actions of `F`.
3. **Fold into a free generalized wreath product.** *Needs a sofic common
   quotient.* An amalgam `A *_C B` embeds in `Z wr^*_(H action H/C) H` whenever
   both factors inject into one group `H` agreeing on `C`, by the
   difference-cocycle argument of
   `coset-difference-cocycle-embeds-double-proof`. With `H` sofic and a sofic
   coset action, Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.7 gives
   soficity. For a Magnus window, the only natural common quotients are the
   window itself and its overgroups, so the argument is circular unless
   another sofic quotient injective on both pieces is found.
4. **What a profinite-gluing theorem would already contain.** *A calibration,
   not a proof.* Any theorem of the form "`S *_F B` is sofic when `S` is
   sofic, `B` is residually finite and the free subgroup `F` is a retract of
   `B`" applies to `B = F x Z`. There it gives soficity of
   `S *_F (F x Z) ~= Z wr^*_(S action S/F) S`, the free-lamp wreath product of
   `free-lamp-double-and-sofic-action-proof`, (FLD4)--(FLD6). So gluing rigid
   pieces is at least as hard as controlling the coset actions `S action S/F`
   of Magnus windows on their free Magnus subgroups. GKP record even the
   amenable-stabilizer case of such coset-action soficity as open.
