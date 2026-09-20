---
rg: 2
id: centralizing-hnn-sofic-via-regular-edge-centralizer
kind: claim
title: Finite-quotient models with exact edge centralization cannot separate profinite-closure pinches
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks for the whole compiler; this computes the exact finite-edge centralizer and excludes one restricted model class, without excluding approximate edge centralization.
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that proves soficity for the conjugate-basis family through a right-angled Artin kernel; this excludes an exact quotient-centralizer strategy for nonseparable edges.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that decides residual finiteness for the conjugate-basis family; this computes the centralizer and precise failure of exact finite-quotient models for arbitrary edges.
---

ESTABLISHED as a restricted no-go. The 2026-09-20 correction narrows the
earlier overbroad claim: **both exactness hypotheses below are needed.**

## Setting and exact centralizer

Let K be residually finite, L<=K any subgroup, and

    Gamma=<K,v | [v,L]=1>=K *_L (L times Z).

For a finite quotient q_n:K->Q_n write L_n=q_n(L), and let pi_n be
the left-translation action of K on Q_n.

1. The induced action of the **finite image L_n** is free. The action
   of L itself has stabilizer ker(q_n|L), so need not be free. Its
   orbits are the right cosets L_n g, with [Q_n:L_n] orbits.
   Infinite index [K:L] does not force these finite indices to grow:
   if L is profinitely dense, every L_n equals Q_n. The available finite
   indices detect the profinite closure of L, not just its abstract index.
2. The exact equivariant-bijection group is

       C_n=C_(Sym(Q_n))(pi_n(L)) ~= L_n wr Sym(O_n), O_n=L_n\Q_n.  (CE1)

   Choose an orbit permutation and one right-translation label per orbit.
   The right-regular group is isomorphic to L_n by inversion, giving the
   displayed wreath-product isomorphism.
3. Every sigma_v in C_n commutes with every element of pi_n(L) exactly.
   Thus (pi_n,sigma_v) defines an exact finite permutation representation
   of Gamma. The remaining issue is separation of nonidentity elements.

## Exact-edge no-go

Suppose k lies in the profinite closure of L in K but not in L. Then
q_n(k) lies in q_n(L) for every finite quotient q_n. Consequently every
sigma_v in the **exact** centralizer C_n commutes with pi_n(k).
Britton's lemma says [v,k] is nonidentity in Gamma, but its image in
every such model is identity. This holds at every scale and for every
stable letter inside C_n, including after finite amplification.

Thus no sequence combining a finite-quotient base action with exact
centralization of the edge image can give a sofic approximation of Gamma.
It does not exclude quotient base actions whose stable letters only
approximately centralize a tested generating set of L.

Indeed, let S generate L and suppose
max_s d_H([sigma_v,pi_n(s)],1)<=epsilon_n. If
q_n(k)=q_n(s_1...s_m), the triangle inequality gives at most m epsilon_n
as a bound for the pinch defect. Profinite closure supplies such a word
but no uniform bound on its length as n changes. Therefore
epsilon_n->0 alone does not force this pinch defect to vanish.

## What survives and what fails

CE1 remains useful as an exact finite-action computation. It does not
automatically apply to an approximate action: approximate actions need
not have exact edge orbits or a large exact centralizer.

A successful sofic construction must leave the excluded *joint* class.
It could perturb the base away from finite quotients, or retain those
quotients while relaxing exact edge centralization. Neither option is
established here. The separate target
[[centralizing-hnn-perturbed-edge-separation]] proposes a non-quotient
construction; that restriction is a design choice, not forced by this
no-go theorem.

The former proposal to sample sigma_v uniformly from C_n and separate
**every** Britton-reduced word is false for nonclosed L. For w=[v,k]
with k in cl(L)\L its separation probability is zero at every n.
This is not a missing probabilistic estimate. A replacement lemma must
change the model class or restrict its conclusion.

A large exact centralizer supplies many stable letters, but forces all
of them to kill the same closure pinches. No compiler-soficity conclusion
follows from CE1 alone.

## Attempts

- **Amplification with a stable letter on a separate factor fails.**
  On Q_n times {1,...,m}, a stable letter acting only on the second
  factor commutes with the whole base, so kills every [v,k], k notin L.
- **Random edge models provide no theorem here.** No distribution or
  centralizer estimate was specified for that earlier suggestion.
  Even a trivial centralizer contains the identity stable letter;
  separation, rather than existence of a commuting permutation, is the
  issue. CE1 needs no random-model assumption.
- **Quotient bases plus exact edge centralizers fail**, as proved above.
  This does not by itself force perturbing the base action.
- **Approximate edge centralization remains unexcluded.** Approximate
  commutation with finitely many generators does not imply uniform
  approximate commutation with every image of an edge element. A new
  argument would need to control growing word lengths or otherwise
  obtain a quantitative centralizer statement.

## Individual pinch separation and separability

The following equivalence concerns separation of each individual pinch
using exact quotient-base and exact edge-centralizer models, with finite
amplification allowed. It is not a proof of separation of all reduced
words or a criterion for soficity.

Let q:K->Q, H=q(L). Amplify to Q times {1,2,3}, so there are at least
three H-orbits. Its full H-equivariant bijection group C has double
centralizer exactly the group of left translations by H:

- For a point z, its stabilizer C_z fixes precisely the H-orbit of z.
  It fixes that orbit pointwise by equivariance, and can move every point
  of every other orbit, since at least two other orbits are available.
- A permutation f commuting with C must send z to hz for some h in H.
  Transitivity of C and commutation with H force f(cz)=c(hz)=h(cz)
  everywhere, so f is that same left translation.
- Conversely every left H-translation commutes with C.

The amplification avoids small exceptions to the unqualified statement,
such as H=1 acting on two points, whose double centralizer is Sym(2).
Thus some sigma_v in the amplified edge centralizer fails to commute
with pi(q(k)) exactly when q(k) is not in q(L).

Every individual pinch [v,k], k notin L, can therefore be separated by
this method if and only if L is profinitely closed in K. If L is finitely
generated, exact commutation with its generators means exact commutation
with all of L; approximate commutation does not have the same consequence.

For the Mikhailova subgroup
M={(u,v) in F times F : u=v in H}, where H is finitely presented with
undecidable word problem, M is finitely generated and membership is
undecidable. A separable finitely generated subgroup of a finitely
presented group has decidable membership: membership is recursively
enumerable, and finite quotients certify nonmembership. Thus this M
is not separable, and the exact-centralizer strategy fails for its rope.
This does not assert nonseparability for every Mikhailova-type subgroup.

**Conclusion.** For a nonseparable edge, abandon at least one of the two
exactness requirements. This node does not say which one, and does not
exclude exact quotient-base models with approximately edge-centralizing
stable letters.
