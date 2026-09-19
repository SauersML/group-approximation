---
rg: 2
id: wreath-sofic-not-mf
kind: claim
title: The mod-two wreath over the affine coset space is a finitely generated sofic group that is not MF
distinct_from:
  sign-free-quotient-sofic: that is the sofic half, proved by the telescope-window pipeline; this is the conjunction — one explicit group carrying both properties — which is the headline neither half states alone.
  commuting-lamp-quotient-not-mf: that is the non-MF half, the sign-free collapse; this is the conjunction with soficity, which is what separates soficity from matricial-field approximability on an explicit group.
  kun-thom-nonsofic-wreath: that wreath (over the Kun--Thom Laurent pair) is NOT sofic — the opposite soficity verdict; this wreath lives over the affine/doubling pair, whose telescope structure is exactly what buys soficity back while the compression still kills MF.
  wreath-not-sofic: that records nonsoficity of THIS REPOSITORY'S wreath candidate over the Kun--Thom pair, imported from the external theorem; this claim's group is the sign-free quotient over the AFFINE pair, where the soficity verdict flips — the two nodes together are the sharpest statement that the base pair, not the wreath shape, decides soficity.
  finitely-presented-sofic-non-mf: that is the strictly stronger separation at the finitely presented source E; this states the conjunction for the group in its honest WREATH-PRODUCT normal form — (ℤ/2) wr_X V — which E is not (E is a presented source and the Clifford witness a central extension; only the sign-free quotient is literally a wreath), and the wreath framing is what the Kun--Thom contrast in the body compares against.
  literal-group-not-sofic: that (refuted) claim denied soficity of the presented source E; this claim asserts the conjunction for the wreath-form quotient, whose soficity is the established half, not the question.
  sofic-non-mf-witness: that is the conjunction at the finitely generated CLIFFORD witness W, where the lamps anticommute up to the central sign; this is the conjunction at its sign-free quotient W/⟨ζ⟩ — a different group, and the only one of the family that is literally a permutational wreath product, which is the framing this node exists to state.
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Let `X = V/Ḡ` be the affine coset space of
`commuting-lamp-quotient-structure` and

```text
L = (⊕_X ℤ/2) ⋊ V  =  (ℤ/2) wr_X V  ≅  W/⟨ζ⟩
```

the permutational mod-two wreath product — equivalently the sign-free
quotient of the Kazhdan–Clifford witness.

**Theorem.**  `L` is a finitely generated **sofic** group that is
**not MF**: it admits no injective corona representation.

Both halves are established in-graph and the conjunction is packaged as
a single kernel statement about a single group term —
`literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF` in the Lean
artifact — so the subjects of the two halves are identified by the
type-checker itself, not by prose.  The sofic half
(`sign-free-quotient-sofic`) needs neither action-soficity nor
co-amenability transfer: killing the sign abelianizes the lamps by pure
universal-property algebra, and the telescope-window pipeline replays
verbatim on mod-two windows.  The non-MF half
(`commuting-lamp-quotient-not-mf`) is the sign-free compression
collapse.

**What the conjunction means.**

1. **Soficity and MF-ness are separated on an explicit finitely
   generated group.**  Sofic groups are the best-behaved approximation
   class in permutations; `L` is sofic yet its operator-norm
   approximation fails outright.  This answers the sofic half of the
   Fournier-Facio item-4 question for this family, with no open input.
2. The contrast with `kun-thom-nonsofic-wreath` is exact and
   instructive: the same wreath construction over the Laurent pair is
   NOT sofic, while over the affine/doubling pair the telescope
   structure restores soficity — and the compression defect survives to
   kill MF in both worlds.  Soficity of the wreath is a property of the
   base pair's finite-window geometry, not of the wreath shape.
3. `L` is not LEF (the exact-finite-model routes are refuted for marked
   quotients), so its soficity genuinely lives in the almost-action
   regime — the group is approximable by almost-actions but by no exact
   finite models, while its C*-algebra resists even almost-flat
   matricial approximation.

**Certification status.**  Both halves' Lean modules are sorry-free and
root-imported; the packaging declaration is in the artifact.  The
fleet kernel build certifying the sofic module (authored in the
2026-08-15 wave with "validation rides the next fleet build") is
running at the time of landing; this node's body will record the build
verdict when it returns.
