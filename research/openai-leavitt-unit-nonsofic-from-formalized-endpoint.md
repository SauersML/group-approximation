---
rg: 2
id: openai-leavitt-unit-nonsofic-from-formalized-endpoint
kind: route
title: The same statement is a kernel-checked theorem of this development, by a different configuration
target: openai-leavitt-unit-nonsofic
requires: [universal-leavitt-el4-nonsofic]
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
  - GroupApproximation/Leavitt/UniversalLeavittOver.lean
  - GroupApproximation/Leavitt/UniversalRankFour.lean
---

## Why sufficient

A second, independent route into the same target, so that the node does not
stand or fall with the chapter.

**The algebras are the same object.**  `UniversalLeavitt.BinaryLeavittAlgebra`
is `RingQuot` of the free `ZMod 2`-algebra on four generators by exactly five
relations -- `t_0 s_0 = 1`, `t_0 s_1 = 0`, `t_1 s_0 = 0`, `t_1 s_1 = 1`,
`s_0 t_0 + s_1 t_1 = 1` (`Leavitt/UniversalLeavittOver.Relation`).  That is
the chapter's equation (1) with the `delta_ij` written out.  "Universal" and
"presented" name the same algebra here: the presentation *is* the universal
property.

**The statement is the same statement.**  The prerequisite carries
`Endpoint/MainResults.universalLeavittUnits_not_isSofic`,
`not IsSofic (BinaryLeavittAlgebra (ZMod 2))^x`, whose own docstring reads
"The full unit group of `L_(F_2)(1,2)` is nonsofic."  Its proof goes through
the complete four-leaf comb code `prefixUnitsEquiv`, identifying the unit
group with `GL_4`, which contains the nonsofic `EL_4`.

**It is a different proof.**  Rank four rather than nine; compressors from
`Leavitt/RankFourCompressors` rather than the two prefix tables of the
chapter's equation (16); and, most substantially, a different non-LEF witness
-- the Higman-free two-relator obstruction of `Sofic/ThompsonFObstruction`
rather than the simplicity of Thompson's `V`.  Property (T) is proved rather
than cited to Ershov--Jaikin-Zapirain.  The two proofs share their two
external inputs, Kun and Kun--Thom, and this development proves those too.

## Why this is not a restatement dressed as a reduction

The prerequisite is not equivalent to the target by renaming.  It is a
statement about the elementary group `EL_4` with a full property profile, and
it reaches the unit group only through the prefix-code identification, which
is a theorem.  More to the point, the route is doing the job the graph needs
done: it says that if the chapter were withdrawn tomorrow, the target would
still be established, from a machine-checked proof that does not read it.
What the chapter retains in that scenario is priority, which no route can
supply and which [[openai-leavitt-unit-nonsofic]] records in prose.
