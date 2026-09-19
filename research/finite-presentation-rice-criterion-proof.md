---
rg: 2
id: finite-presentation-rice-criterion-proof
kind: route
title: Seed the compiler and read the two branches
target: finite-presentation-rice-criterion-via-the-fixed-positive-rope
requires:
  - mf-safe-finite-presentation-compiler
  - local-approximation-properties-are-marked-closed
---

The compiler of [[mf-safe-finite-presentation-compiler]] takes a finitely
presented seed and a program code and outputs a finite presentation; its
`INF` branch collapses the switch group, so the output there does not
involve the seed, while its `FIN` branch embeds the seed through the
bridge and the Higman rope.  This is (RC1).

Given `P` with (C1) and (C2), take `D` from (C2).  For `e in INF`,
`Carrier(P_e(D)) = R_e` has `P` by (C1).  For `e in FIN`, `D` embeds in
`Carrier(P_e(D))`, so heredity and `¬P(D)` give `¬P(Carrier(P_e(D)))`.
Hence `e |-> P_e(D)` is a computable many-one reduction of `INF` to
`P_fp`, which is `Pi^0_2`-hard because `INF` is `Pi^0_2`-complete;
complements give the `Sigma^0_2` statement.  Membership plus hardness is
completeness.

(If the property is only isomorphism-invariant rather than hereditary, the
same argument works with (C2) strengthened to "`¬P(K)` for every finitely
presented `K` containing `D`".)
