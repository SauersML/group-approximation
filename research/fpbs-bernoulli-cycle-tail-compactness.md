---
rg: 2
id: fpbs-bernoulli-cycle-tail-compactness
kind: claim
title: Bernoulli cost minimizers have tight finite-cycle dimension
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
distinct_from:
  fpbs-graphing-cost-betti-cycle-dimension-identity: that proves the identity and a conditional equivalence; this asserts the unproved existence of compact near-minimizing sequences for all finitely generated groups
---

**OPEN.** For every infinite finitely generated group Gamma, its free
Bernoulli action b admits bounded-degree graphings Phi_n generating its orbit
relation, with c(Phi_n)->C(b), such that

    lim_(L->infinity) limsup_(n->infinity) [z(Phi_n)-z_L(Phi_n)] = 0.

Here z is the von Neumann dimension of the closed finite-cycle span and z_L
is the dimension of the span of cycles of length at most L. The definition
and dimension conventions are those of the artifact, Sections 1--4.
No uniform degree bound across n is required. By the established identity
and short-cycle surgery, this is equivalent to C(b)=1+beta_1^(2)(Gamma).
It is therefore a stronger target than universal Fixed Price alone.

## Attempts

Use reduced relator circulations. For a finite presentation, the tail-rank
bound in `fpbs-reduced-circulation-tail-bounds-cost-excess` supplies this
condition if a near-minimizing sequence has uniformly bounded total expected
reduced circulation mass. Section 8 of the artifact gives an explicit
coherent routing calculation on F_r x Z with that bound despite divergent
route lengths. It uses an infinite commuting direction; no analogous
construction is supplied for arbitrary finitely presented groups, and the
finite-presentation estimate does not itself cover every finitely generated
group.

Pass to a limit of short-cycle surgery. For each fixed graphing all finite
cycles are eventually captured, but this limit is not uniform over
near-minimizers. Section 4 identifies the surviving nonuniform tail with the
possible cost--Betti gap. Interchanging the two limits assumes this claim.

Use independent-priority pruning. The existing
`fpbs-priority-deletion-density-above-action-cost` shows that this particular
rule can remain strictly above action cost. A new pruning construction must
control both its budget and all required connections.
