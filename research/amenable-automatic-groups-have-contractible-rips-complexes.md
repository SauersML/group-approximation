---
rg: 2
id: amenable-automatic-groups-have-contractible-rips-complexes
kind: claim
title: Every amenable automatic group has a contractible Rips complex
distinct_from:
  some-amenable-automatic-group-has-no-contractible-rips-complex: that is the negative answer to Zaremsky Problem 4.1; this is the affirmative answer
  hyperbolic-rips-complex-models-proper-actions: that is the theorem for hyperbolic groups; this is the claim for amenable automatic groups
---

**OPEN.** For every amenable automatic group `G` there are a finite
generating set `S` and `r >= 0` such that the Rips complex `P_r(G,S)` is
contractible. (Existential reading of Zaremsky Problem 4.1; see
`zaremsky-4-01-amenable-automatic-contractible-rips`.)

Consequences:

- every torsion-free amenable automatic group has a finite `K(G,1)`
  (`contractible-rips-complex-gives-finite-classifying-space`);
- Thompson's group `F` is not both amenable and automatic
  (route `thompson-f-not-amenable-and-automatic-via-rips`).

## Attempts

- 2026-09-13 (lane z4-01-amen-auto-rips): pushing simplices toward `1` along
  the automatic combing fails at a fixed scale; see the Attempts of the root
  `zaremsky-4-01-amenable-automatic-contractible-rips`.
- 2026-09-13: the natural split is (i) identify the amenable automatic groups,
  where the only examples this lane knows are virtually abelian, and (ii) prove
  contractibility for that class. Step (ii) is established
  (`virtually-abelian-groups-have-contractible-rips-complexes`), so what remains is
  (i), `amenable-automatic-groups-are-virtually-abelian` (route
  `amenable-automatic-rips-via-virtually-abelian`).
- 2026-09-13: alternatively, a contracting combing on each amenable automatic group
  would do (route `amenable-automatic-rips-via-contracting-combings`).
