---
rg: 2
id: atlas-q1920-low-index-proof
kind: route
title: Freeze each Q1920 marking and enumerate every colimit action through degree twelve
target: atlas-q1920-seam-has-no-low-index-action
requires:
  - atlas-a5-seam-obstruction-is-not-universal
artifacts:
  - experiments/atlas_a4_non_a5_fj_colimits.g
  - research/artifacts/atlas-a4-q1920-fj-low-index.json
---

Run the exact GAP verifier with `ONLY_ORDER:=1920` and `LOW_INDEX:=12`.
The outer census is complete for local coset actions through degree twelve;
it selects exactly two marked local groups.  As in the Q168 calculation,
`IsomorphismFpGroupByGenerators` freezes each finite marked group's complete
multiplication before the seam relations are adjoined.

For each resulting finitely presented colimit,
`LowIndexSubgroupsFpGroup(P,12)` enumerates every subgroup of index at most
twelve.  The verifier constructs the corresponding right-coset action and
computes directly the image orders of `Q`, `F=<r,z,c,u>`, and
`J=<t,s,c>`, together with the orders of `z` and `c`.  The full collected
histograms for both markings coincide and are preserved in the JSON
artifact.  Inspection against the required order triple `(1920,36,24)`
proves the claim.
