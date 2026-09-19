---
rg: 2
id: universal-local-property-tester-via-finite-obstruction-covers
kind: route
title: Embed every finite obstruction cover in one universal container
target: universal-local-approximation-fixed-two-generator-test-group
requires:
  - whitehead-universal-finitely-presented-container
  - local-approximation-properties-are-marked-closed
  - fournier-facio-group-is-nonsofic
  - torsion-free-finitely-presented-non-mf
  - mf-positive-controls
---

Choose the fixed two-generator finitely presented group `V` from
[[whitehead-universal-finitely-presented-container]]. It contains every
countably generated recursively presented group and has exactly all finite
torsion orders.

Fix an arbitrary model predicate `M` and suppose `P_M(V)` holds. If some
group `G` failed `P_M`, locality in
[[local-approximation-properties-are-marked-closed]] would give a finitely
generated subgroup `H<=G` which still fails. The finite-obstruction-cover
clause of that theorem then supplies a finitely presented group `H^` which
fails `P_M` and surjects onto `H`.

The group `H^` is recursively presented, so it embeds in `V`. But every
local approximation property `P_M` is hereditary to subgroups. Hence
`P_M(V)` would force `P_M(H^)`, a contradiction. Therefore every group
has `P_M`. The converse applies the universal assertion to `V`.

Nothing in the argument depended on `M`, so the same `V` works
simultaneously for every property in the finite-table framework. Applying
the result to hyperlinearity gives the fixed-group equivalence in the claim.

Finally, the finitely presented torsion-free nonsofic and non-MF witnesses
embed in `V`. Soficity and MF are hereditary to subgroups, the latter
recorded in [[mf-positive-controls]], so `V` has neither property. QED
