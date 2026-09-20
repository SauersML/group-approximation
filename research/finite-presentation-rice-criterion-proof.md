---
rg: 2
id: finite-presentation-rice-criterion-proof
kind: route
title: Seed the compiler and read the two branches
target: finite-presentation-rice-criterion-via-the-fixed-positive-rope
requires:
  - mf-compiler-is-uniform-in-finite-seeds
  - local-approximation-properties-are-marked-closed
---

The uniform compiler premise gives P_e(d), retaining BOTH inputs.
On INF call its actual output R_e(d); on FIN it contains Carrier(d).
This is (RC1), without identifying outputs across seeds.

Given P and ONE d satisfying both (C1) and (C2), for e in INF,
Carrier(P_e(d))=R_e(d) has P by (C1). For e in FIN, Carrier(d) embeds
in Carrier(P_e(d)), so heredity and (C2) give failure of P there.
Hence e |-> P_e(d) is a computable many-one reduction of INF to
`P_fp`, which is `Pi^0_2`-hard because `INF` is `Pi^0_2`-complete;
complements give the `Sigma^0_2` statement.  Membership plus hardness is
completeness.

(If the property is only isomorphism-invariant rather than hereditary, the
same argument works with (C2) strengthened to failure of P for every
finitely presented group containing Carrier(d).)
