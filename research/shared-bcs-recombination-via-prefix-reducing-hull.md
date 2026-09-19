---
rg: 2
id: shared-bcs-recombination-via-prefix-reducing-hull
kind: route
title: Amalgamate fresh context charts over literal shared variables and take their pulse-central reducing hull
target: shared-bcs-active-recombination-after-schur-returns
requires:
  - oriented-schur-child-branching-identity
  - translation-symmetrized-schur-child-reset
  - hnn-full-child-chart-transports-every-type-corner
  - shared-schur-retained-children-have-common-next-tag-prefix
  - finite-group-shared-overlap-polar-alignment
  - prefix-central-reducing-hull-recombines-context-returns
  - corner-localized-non-ce-bcs-energy-gap
---

Fix one level and write `D_c` for the elementary-abelian selector subgroup
of context `c`.  Build the fresh global shared-variable base first: it is the
right-angled Coxeter group on the literal next-level variables, with the
required context cliques.  Each `D_c` is a special clique subgroup and hence
embeds.  Attach the finite next child chart for context `c` by the iterated
amalgamated product over `D_c`.  Normal form for amalgamated products embeds
the shared base and every attached chart, even when different `D_c` overlap.
Take the direct product with the finite pulse-prefix packet.  Thus every
next-level packet generator commutes with the current positive prefix `C`.

For a context `c`, `(OCB1)--(OCB3)` split its corrected Schur child over the
current carrier into

```text
one retained child over every selector type
+ one additional exit child over every forbidden type.        (1)
```

The direct sum `L_c` of the retained types therefore has the trace of one
complete baseline carrier:

```text
tau(L_c)>=q_current-O(sqrt(E)).                         (2)
```

The translation-symmetrized reset makes all summands of `L_c` genuine
primitive central child types.  Pad both child charts by the same pulse
packet and use one full-chart HNN isomorphism.  By
`hnn-full-child-chart-transports-every-type-corner`, its image `P_c` has the
same trace as `L_c` and belongs to the fresh context chart.  Padding alone
only preserves the source pulse character.  The separate gate
`shared-schur-retained-children-have-common-next-tag-prefix` must place all
of these images under the same new survivor prefix `C_next`.  Multiple
context HNN letters cause no collapse: each associated subgroup embeds in
the common base, so the multiple-HNN normal form embeds that base.

The projections `P_c` need not coincide and their external multiplicity
unitaries need not be aligned.  Apply
`prefix-central-reducing-hull-recombines-context-returns` to their union and
to the complete finite list of fresh shared and context-packet generators.
Once that placement gate is supplied, the resulting projection `Q_next`
satisfies

```text
Q_next<=C_next,
tau(Q_next)>=q_current-O(sqrt(E)),
[Q_next,x_v^(next)]=0                                  (3)
```

for the corrected tuple.  Because every occurrence of a shared variable is
the same literal `x_v^(next)`, all induced context marginals on `Q_next`
agree.  The fixed perturbation back to the raw tuple costs `O(sqrt(E))`, and
`corner-localized-non-ce-bcs-energy-gap` applies on `Q_next` at the next
level.

No context selector centers are amalgamated beyond their actual shared
variable subgroups, so the construction does not classicalize distinct
contexts.  The survivor-prefix containment in `(3)` keeps every previous
negative first-hit layer orthogonal to the new carrier.  Without the required
placement gate, the construction produces only returned ranges under the old
prefix and does not prove `(3)`.

At the fixed terminal depth all groups, amalgams, and HNN menus above are
finite in number and finitely presented.  Their normal forms embed the
original marked base, so its nontrivial central involution remains
nontrivial.  A separate extension of the chosen perfect BCS trace is not
needed for this algebraic completeness clause; the final group has its
canonical finite regular trace once base embedding has preserved the mark.
