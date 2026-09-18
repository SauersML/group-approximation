---
rg: 2
id: kms-2to2-reduction-is-sound-only-for-colorings
kind: claim
title: The Khot--Minzer--Safra 3LIN to transitive 2-to-2 reduction of ECCC TR16-124 is sound only against (j, delta)-colorings, and its authors state that value soundness needs a modification that removes constraints, so it is not a second value-sound family for the selector holes
distinct_from:
  two-to-two-games-theorem: that imports the value-sound 2-to-2 theorem of KMS TR18-006; this records that the earlier TR16-124 reduction by itself carries only the non-standard coloring soundness, and that value soundness is attributed to a constraint-removing modification.
  near-perfect-selectors-die-on-every-rigid-doubled-lec: that splits the non-DKKMS survivor into four failures; this checks that the KMS TR16-124 instances do not supply a value-sound member of that survivor.
artifacts: []
---

**ESTABLISHED.** Route: `kms-2to2-reduction-is-sound-only-for-colorings-citation`.

## Statement

In Khot, Minzer and Safra, *On Independent Sets, 2-to-2 Games and Grassmann
Graphs* (ECCC TR16-124):

1. **Theorem 1.8** maps regular `Gap3Lin(1 - eps, s*)` to a *Transitive 2-to-2
   Game*. YES instances have a `(1, 1 - delta)`-coloring. NO instances, assuming
   Hypothesis 2.5, have no `(j, delta)`-coloring. This is the non-standard
   soundness of their Conjecture 1.6, not the value soundness of their
   Conjecture 1.3 ("no coloring satisfies more than delta fraction").
2. **Remark 1.11** says that value soundness is the subject of ongoing work with
   Dinur and Kindler, and that "the modification of the reduction amounts to
   removing some of the constraints in the 2-to-2 Game constructed by the
   reduction".

## Consequence for the selector holes

The selector holes `parity-leaking-branch-selectors-reach-near-perfect-completeness`
and `efficient-branch-selector-on-proved-2to1-instances` need value-sound NO
instances, because a lift's NO value is bounded only by the value of the
underlying 2-to-1 or 2-to-2 game. By (1), the unmodified KMS TR16-124
instances do not give that. By (2), the value-sound version is the DKK(M)S
line, which in its 2-to-1 form is the construction already killed by
`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`.

So the question "is there a second proved value-sound family that the selector
kill misses?" gets no from this paper. What remains open is
`near-perfect-selectors-die-on-every-rigid-doubled-lec` (F1) to (F4): a new
construction. This is a literature reading, not a theorem about all reductions.
