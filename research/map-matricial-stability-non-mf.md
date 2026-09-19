---
rg: 2
id: map-matricial-stability-non-mf
kind: claim
title: A minimally almost periodic matricially stable group is not MF
distinct_from:
  normal-kazhdan-defect-non-mf: that claim obtains non-MF-ness from a normal Kazhdan subgroup in the compression defect and proves its own rigidity; this one assumes a stability hypothesis outright and needs no compression data at all.
  central-sign-corona-obstruction: that claim marks a central involution; this one has no mark and no torsion anywhere in its statement.
---

Let `G` be an infinite countable group that is **minimally almost
periodic** — every finite-dimensional unitary representation is trivial —
and **matricially stable** in Dadarlat's sense: for every asymptotic
homomorphism `phi_n : G -> U(k_n)`, not necessarily separating, there are
homomorphisms `pi_n : G -> U(k_n)` with `‖phi_n(s) - pi_n(s)‖ -> 0` for each
`s in G`.  Then `G` is not MF.

The argument is two lines and is written out in the proof route.  What makes
it worth a node is its shape: **no torsion, no mark, no central element, no
compression data**.  It is the cleanest torsion-free-compatible non-MF
criterion available, and its group-theoretic hypothesis is one this program
is already forced into from two other directions
(`bounded-rank-corners-excluded`,
`finite-dimensional-models-break-coordinate-generation`).

The price is the stability hypothesis, which is unproved for every candidate
here and is the same wall the repository already records for its Steinberg
group: proving operator-norm stability for `St_5(L)` would close the weak-MF
lane negatively, while proving weak MF would exhibit an explicit failure of
that stability.  This node states the implication cleanly so that the wall
has a name in the graph.

## Ideas

**A chain that would prove too much — FLAGGED, NOT ASSERTED.**  Two
statements reported from Dadarlat, arXiv:2007.12655, sit next to each other
in a way that deserves checking before anyone relies on either:

- MF implies weak quasidiagonality;
- Proposition 3.19, attributed to Ozawa--Thom: an infinite property-(T)
  group that is weakly quasidiagonal has an infinite residually finite
  quotient.

Chained, these give: *an infinite Kazhdan group with no infinite residually
finite quotient is not MF* — a published, torsion-free-compatible, entirely
unconditional non-MF criterion, needing no mark, no stability, and no
compression data.

**Treat this as probably wrong until checked.**  If it were right, non-MF
groups would have been available since the Ozawa--Thom result, whereas the
manuscript records that no countable group was known whose group C-star
algebra fails to be MF, and Bachner--Dogon--Lubotzky still called the MF
question open in April 2026.  The likely failure points, in order of
suspicion: the first statement may be false as summarized, or carry extra
hypotheses (a `gamma`-element, or a reduced-algebra qualifier); Proposition
3.19 may carry hypotheses lost in transcription; or infinite Kazhdan groups
with no infinite residually finite quotient may not be known to exist, which
would make the criterion vacuous rather than false.  The question is out to
cairn-scout, who has the primary text.  **Nothing in this repository should
depend on the chain until it comes back**, and if it does come back valid it
is a priority matter for the manuscript, not merely a new route.
