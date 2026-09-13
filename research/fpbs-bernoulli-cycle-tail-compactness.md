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

Test the claim where fixed price is known (checked 2026-09-12 against
Gaboriau's lecture notes,
<https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf>,
version of 3 October 2025, table in Section 2.9). Every infinite group
listed there with fixed price has cost 1+beta_1^(2). This covers amenable,
free and surface groups, lattices in SO(2,1), SL(2,Z) at 13/12,
(F_m x F_n)*F_k at k+1, Artin groups at their number of components, and
every fixed price one row. No known case kills the claim. For F_2 x Z the
center contains Z, so Corollary 2.52(3) gives fixed price one and the
homological bound gives beta_1^(2)=0. The identity
c(Phi)=1+beta_1^(2)+z(Phi) then forces z(Phi_n)->0 along every
near-minimizing sequence, so tight finite-cycle dimension holds there
without using z_L. For a single group the claim says that every free
action costs 1+beta_1^(2), since Bernoulli cost is the maximum and the
homological bound is the minimum. Question 2.65 of the notes lists this
cost--Betti equality as open. Question 2.67 records that infinite Kazhdan
groups have cost one (Hutchcroft--Pete), so beta_1^(2)=0 by the homological
bound, while their fixed price remains open. So proving the claim on the groups with
C_*=1+beta_1^(2) would prove fixed price for every infinite Kazhdan group.

Build the class by amalgamation. Write P for the groups satisfying the
claim. P contains every fixed price one group. It is closed under
amalgams G_1 *_H G_2 over any infinite H with beta_1^(2)(H)=0, amenable or
not. For a free action a, Corollary 2.40(a) of the notes gives
C(a)<=C(a|G_1)+C(a|G_2)-1, because the two restricted relations share the
infinite H-orbits. The Mayer--Vietoris computation quoted in the proof of
Theorem 2.47 gives beta_1^(2)(G)=beta_1^(2)(G_1)+beta_1^(2)(G_2), and the
homological bound closes the sandwich. This is the per-action form of
Theorem 2.47, which treats only infimum costs. It produced no new fixed
price group. In a free product A*B such as (F_2 x F_2)*F_k, a non-amenable
subgroup with beta_1^(2)=0 is freely indecomposable. By Kurosh it lies in a
conjugate of a factor, say A, and the amalgam is (G_1 *_H A)*B up to
conjugation. We found no member of P with beta_1^(2)>0 in which such a
subgroup escapes the fixed price one pieces.
