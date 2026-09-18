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
price group. Suppose G_2=A*B, for instance (F_2 x F_2)*F_k. A non-amenable
subgroup of G_2 with beta_1^(2)=0 has no nontrivial free splitting, because
every nontrivial free product other than Z/2*Z/2 has beta_1^(2)>0. By
Kurosh it lies in a conjugate of a factor, say A, and G_1 *_H G_2 is
isomorphic to (G_1 *_H A)*B. In each group with beta_1^(2)>0 listed above,
such a subgroup either does not exist or lies in a conjugate of a fixed
price one free factor. Amalgams of fixed price one groups over infinite
subgroups have fixed price one by Corollary 2.40(a), free products are
covered by Theorem 2.27, and amenable H falls under Corollaries 2.28 and
2.32.

Generalize the Section 8 routing to a hyperfinite spine (2026-09-17). The
F_r x Z calculation uses one feature: the orbit relation T_0 of the central
Z is aperiodic, hyperfinite and invariant under every generator. The measured
form keeps only aperiodicity of T cap T^g, where T^g={(x,y):(gx,gy) in T}.
`fpbs-q-normal-hyperfinite-chain-forces-cost-one` (OPEN: a written proof whose
main lemma referees found sound, demoted over the import scope of its
fixed-price consequence) shows that any countable
chain of such q-normalizers from an aperiodic hyperfinite T_0 up to the orbit
relation gives cost one. It pays for each generator only on a small complete
section of T cap T^g. For the Bernoulli action this gives fixed price one,
so beta_1^(2)=0 and z(Phi_n)->0 along near-minimizers, which is this claim for
that group. **Where it dies:** the mechanism yields cost one directly and never
a positive excess. It says nothing where beta_1^(2)>0, and there no chain
exists in any free action. So it cannot supply tail compactness for any group
with C(b)>1. Free products and the (F_m x F_n)*F_k rows above are known only
through their published fixed price, not through a routing of this shape. Among
beta_1^(2)=0 groups the hard remaining class is hyperbolic Kazhdan groups.
`fpbs-hyperbolic-no-q-normal-hyperfinite-chain` records that normal spines,
the literal Section 8 shape, cannot exist there, by Popa--Vaes Theorem 1.4
together with standard facts. It leaves the one-sided q-normal case open at
single-point boundary fields.

Replace tail control by well-founded Borel Morse matchings
(swarm-0917-w4-fp-cycle-tail; `fpbs-bernoulli-morse-collapse-criterion`).
Match relator cells over the Bernoulli space injectively to boundary edges,
with almost surely no infinite chain of removed edges, and delete the matched
edges of the Cayley graphing. König's lemma keeps the relation generated.
Hence C(b) <= |S| - mu(M), with no mass or length control. The Morse deficit
m(R) = |S| - 1 - beta_1 - sup mu(M) is nonincreasing in R, and over the full
lists P_L of trivial words it decreases to C_sub(S) - 1 - beta_1, the
subgraphing cost excess. The target for Gamma follows from m(R)=0 for a
single finite R, and conversely it gives m(R)=0 when combined with depth
compactness and subgraphing attainment. Calibrations: Z^2, products of groups
with infinite-order generators, and F_2 x F_2 all have deficit 0, with the
unmatched density on F_2 x F_2 equal to beta_2 = 1. For <S | w^m> the
proper-power ceiling 1/m equals z exactly. This is a reduction, not a proof:
no case with open fixed price was reached. The target stays OPEN.

Pass near-minimizers to a compact stability limit (lane b-p-fp4,
2026-09-17; `fpbs-tight-routes-iff-bernoulli-weakly-treeable`, artifact
`research/artifacts/fpbs-tight-routes-weakly-treeable-2026-09-17.md`). The
plan was to code near-minimizing graphings of b into a compact space, take a
weak* limit, and read tight cycle dimension off an exact minimizer. Such a
limit is a free action weakly contained in b, with a graphing of cost at most
C(b). It keeps generation exactly when routes for the generators stay of
bounded length with labels in a finite set, uniformly in n (condition (T)).
Theorem A shows that (T) holds for some near-minimizing sequence iff b is
weakly equivalent to a free treeable action, and then Gamma has fixed price.
The attempt dies at the generation step on every non-treeable group. By
Adams--Spatzier these include every infinite Kazhdan group, which are exactly
the open cases named above, and also F_2 x F_2 and every nonamenable group
with a cost-one free action. The invariant that kills it is treeability. The
claim itself is not refuted: condition (9.1) of the cost-cycle artifact is
about tau_L tails, not route lengths. The reduced-circulation channel of the
first attempt tolerates divergent routes, and it is the surviving quantitative
channel. On F_r x Z (non-treeable) its route lengths diverge as Corollary B
requires, while the reduced mass stays bounded.
