---
rg: 2
id: source-specific-pointed-rank-router-face
kind: claim
title: A non-tensor-closed pointed source face authenticates the independent-set rank cells
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
  - research/artifacts/seifert-coinvariant-router-2026-08-23.md
distinct_from:
  hybrid-rank-router-authenticates-affine-overlap-blocks: that demanded exact extension for every zero-overlap pair and is refuted by tensor closure; this permits only one distinguished perfect source trace and a pointed canonical-microstate soundness face.
  fixed-mass-same-gram-mixed-word-certificate: that asks one common Gram word to carry the original BCS verifier energy; this starts after independent-set normalization and may use separate rank cells, but must condition them on one global source face.
  central-word-state-face-compiler: that is a general state-face endpoint for an arbitrary predicate; this fixes the independent-set row-clock and rank-conjugacy interface explicitly.
---

**OPEN.**  Construct a fixed finite presentation tied to the fixed non-RU
independent-set game, a marked central word, and a finite pointed moment
packet with the following two deliberately non-functorial properties.

1. **One-source completeness.**  The one distinguished perfect commuting
   row-PVM trace extends to an exact tracial representation with nonzero
   mark.  No extension is promised for every abstract pair `PQ=0`.
2. **Pointed finite-matrix soundness.**  Every canonical-trace matrix
   microstate with separated mark and the prescribed global row-clock
   moments admits outcome-count-free PVM rounding and, for every forbidden
   pair, routed rank words `R_f,S_f` satisfying

   ```text
   R_f=diag(1-2P_f,1-2Q_f)+o(1),
   S_f=diag((1-2P_f)(1-2Q_f),1)+o(1),                 (SPR1)
   ```

   with total movement bounded by the fixed presentation defect.

The pointed face must exclude the tensor product in `(HRT1)--(HRT3)`.  A
nonmultiplicative global row-PVM moment, a trace-selected packet sector, or
a genuinely matrix-only proper-corner localization may do this; ordinary
central-character selection alone cannot.  Solving `(SPR1)` on this one
face, rather than in every exact marked representation, is the precise rank
router endpoint left by the tensor-closure refutation.


## The quotient-first router architecture does not supply the face

`seifert-coinvariant-router-2026-08-23` proposes reading the surviving
coordinate `gamma` as "the only statistic invariant under all permitted local
source-gauge moves".  Taken literally that is self-defeating, and the
dichotomy is sharp.

- If the permitted moves include the tensor extension that builds
  `(HRT1)--(HRT3)`, then every invariant statistic is tensor-blind, so
  `gamma(source)=gamma(tensor witness)` and the face fails exactly the
  exclusion it was introduced for.  This is the screening test of
  `local-exactification-invariants-cannot-close-gluing-holes` applied to the
  router row of its table.
- If the permitted moves exclude the tensor extension, then the relation
  closure does not annihilate that direction, so the architecture's promise —
  that the quotient kills every locally movable coordinate — is not delivered
  where it is needed.

Independently, the quantitative half of `(SPR1)` cannot come from the
arithmetic of the quotient at all: by
`gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap`, an integral
checksum on the cokernel of the locally realizable repair directions is
annihilated by amplification in its torsion part and driven to zero by
normalized-profile density in its free part.  A Smith-normal-form computation
on the router coordinates can still *refute* a moment vocabulary cheaply —
`coker=0`, or source and tensor witness equal in the cokernel — but it cannot
complete this node.

Both bounds leave the node's own reading intact and sharpen it: the surviving
`gamma` must be simultaneously non-invariant under tensor extension and not a
function of fixed packet rank arithmetic, i.e. a nonmultiplicative analytic
row-PVM moment or a matrix-only proper-corner localization.  The exact
`(3,4,infinity)` gadget of `seifert-coinvariant-defect-router` and
`two-cone-central-router-determinant` remains a correct and useful model of
the *presentation-design* side, where these two obstructions do not apply
because the twists are chosen by the compiler rather than read off a
microstate.
