---
rg: 2
id: higman-group-embeds-in-no-lodha-moore-or-monod-group
kind: claim
title: Every homomorphism from Higman's group to Monod's group H(R) or to a Lodha-Moore group is trivial, answering Zaremsky's Oberwolfach 2018 Question 110 negatively
requires:
  - higman-group-embeds-in-no-piecewise-analytic-circle-group
  - lodha-moore-groups-embed-in-lodha-circle-group
distinct_from:
  higman-group-embeds-in-no-piecewise-analytic-circle-group: that excludes every group of piecewise real-analytic circle homeomorphisms; this records the instance at the two hosts named in a printed question, with the containments that make it apply.
  higman-group-satisfies-boone-higman: that is the open embedding question for Higman's group; this closes one proposed route to it.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**ESTABLISHED** (corollary; lane proof, not independently reviewed). It adds no
mathematics beyond `higman-group-embeds-in-no-piecewise-analytic-circle-group`; the new
content is that a printed question is answered by it.

**Printed question.** M. Zaremsky, in *Oberwolfach Report 26/2018* (DOI
10.4171/OWR/2018/26), "Open problems on Thompson-like groups", Question 110, p. 1624,
read from the PDF:

> Does the Higman group ⟨a, b, c, d | b^a = b², c^b = c², d^c = d², a^d = a²⟩ embed into
> the Lodha–Moore groups? Or at least into Monod's H(**R**)? It's built out of copies of
> the Baumslag–Solitar BS(1,2), so this seems like a natural question following the
> broken Baumslag–Solitar discussion.

**Statement.** Let `H4` be Higman's group.
1. Every homomorphism from `H4` to Monod's group `H(R)` is trivial. Here `H(R)` is the
   group of homeomorphisms of `RP^1 = R ∪ {∞}` that fix `∞` and are piecewise in
   `PSL_2(R)` with finitely many pieces.
2. Every homomorphism from `H4` to a Lodha–Moore group is trivial. This covers `G_0` and
   the larger group with percolating elements at every address, as in
   `lodha-moore-groups-embed-in-lodha-circle-group`.

So `H4` embeds in none of these groups, and Question 110 has a negative answer in both
of its forms.

**Proof.**
1. An element of `H(R)` is a homeomorphism of `RP^1 ≅ S^1`. On the closure of each of
   finitely many arcs it agrees with an element of `PSL_2(R)`, which is a real-analytic
   diffeomorphism of `RP^1`. So `H(R) ≤ PA_+(S^1)` in the sense of
   `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`, whose Setting already
   lists all piecewise-`PSL_2(R)` groups with finitely many breakpoints. Apply
   `higman-group-embeds-in-no-piecewise-analytic-circle-group`.
2. By `lodha-moore-groups-embed-in-lodha-circle-group`, each of these groups embeds in
   Lodha's group `S`, and `S ≤ PA_+(S^1)`, as recorded in the obstruction node. Compose.

The groups `H(A)`, for any subring `A ⊆ R`, are subgroups of `H(R)` and are covered too.
The Lodha–Moore groups are also known to be piecewise projective groups of `R`, hence to
lie in `H(R)`. That containment is recalled, not re-read, and the proof does not use it.

**Why the hosts were natural.** `BS(1,2)` embeds in all of them, for example via
`x ↦ x+1, x ↦ 2x` in `H(R)`. So no single BS(1,2) relation is an obstruction. What fails
is the cyclic chain of four square-conjugations around `Z/4`; see the obstruction node
and its proof route.

**Literature.** Rivas–Triestino (arXiv:1905.00938v2, Theorem C) prove that every action
of Higman's group by `C^1` diffeomorphisms of `R` or `S^1` is trivial. Elements of `H(R)`
have breakpoints, so that theorem does not apply. A bounded arXiv abstract search on
2026-09-18 ("Higman" with "piecewise projective", "Lodha-Moore", "Monod") found no
statement of this answer. No MathSciNet or zbMATH search was made, so no priority is
claimed.

**For Boone–Higman.** This closes the Lodha–Moore / Monod route to
`higman-group-satisfies-boone-higman`, which would have passed through Lodha's finitely
presented simple group `S`.
