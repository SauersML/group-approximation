---
rg: 2
id: virtually-special-groups-embed-in-brin-thompson-group-2v
kind: claim
title: Every group that virtually embeds in a finitely generated right-angled Artin group embeds in the Brin-Thompson group 2V
distinct_from:
  virtually-special-groups-embed-in-some-brin-thompson-group: that gives some nV with n depending on the graph, by Belk-Bleak-Matucci; this fixes n = 2 and implies that claim.
  cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group: that is the hyperbolic cubulated case in some nV; this covers every group virtually in a finitely generated right-angled Artin group, in 2V.
  every-raag-embeds-in-brin-thompson-group-2v: that embeds the right-angled Artin groups themselves; this passes to groups with a finite-index subgroup inside one, through wreath products with finite symmetric groups.
---

Let `G` have a finite-index subgroup that is isomorphic to a subgroup of a
right-angled Artin group `A_Γ` on a finite graph `Γ`. Then `G` is isomorphic to a
subgroup of `2V`, and so of `nV` for every `n ≥ 2`.

**Examples.** Every finitely generated virtually special group: its finite-index
special subgroup is finitely generated, so it lies in a finitely generated
sub-RAAG. This includes the groups listed under
`virtually-special-groups-embed-in-some-brin-thompson-group`, such as finitely
generated Coxeter groups and limit groups. It also includes every hyperbolic
group acting properly and cocompactly on a CAT(0) cube complex (Agol, through
`cubulated-hyperbolic-groups-are-virtually-special`). The graph previously put
that class only in some `nV`.

**Not covered.** `H_3(Z)` has a distorted element in every finite-index subgroup,
so it virtually embeds in no right-angled Artin group (artifact, Part C). Nor
does any infinite group with property (T), and in particular no infinite
hyperbolic group with property (T). The reason is standard: RAAGs act properly
on CAT(0) cube complexes, so they have the Haagerup property. That property
passes to subgroups and to finite-index overgroups, and it is incompatible with
infinite property (T). These groups are the open cores of Zaremsky 2.19(c), (d)
and (a).

Route: `virtually-raag-groups-in-2v-via-finite-extensions`.
