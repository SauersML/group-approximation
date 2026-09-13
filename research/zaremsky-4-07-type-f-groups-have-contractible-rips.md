---
rg: 2
id: zaremsky-4-07-type-f-groups-have-contractible-rips
kind: claim
title: "Zaremsky Problem 4.7 resolved: does every group of type F have a contractible Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is the question for Z^n with its standard word metric, answered yes by Virk; this asks about every group of type F and allows any finite generating set
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for proper actions of a hyperbolic group; this is Zaremsky's question for all groups of type F
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 7,
verbatim: "(Added 7/24/25): Relatedly, does every group of type F have a
contractible Rips complex?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-07-by-yes` requires
  `every-type-f-group-has-a-contractible-rips-complex`.
- **No**: `zaremsky-4-07-by-no` requires
  `some-type-f-group-has-no-contractible-rips-complex`.

Never write a `requires: []` route into this claim.

**Reading.** For a finitely generated group `G` with finite generating set `S`,
`d_S` is the word metric and the Rips complex `VR_r(G, d_S)` at scale `r` has the
finite subsets of diameter `≤ r` as simplices. A group of type F is a group with a
finite `K(G,1)`; such groups are torsion-free. The literal reading (W), used by both
answer claims: `G` has a contractible Rips complex if `VR_r(G, d_S)` is
contractible for SOME finite generating set `S` and SOME scale `r`. By
`rips-complex-of-a-group-is-a-flag-cayley-complex` this says exactly that `G` acts
freely, cocompactly and vertex-transitively on a contractible locally finite flag
simplicial complex. The natural strengthening (R): some finite generating set `S`
makes `(G, S)` of type R in the sense of Li–Sánchez Saldaña (arXiv:2608.24279v1,
Definition 1.1: `VR_r(G, d_S)` contractible for every `r ≥ r_0`). Li–Sánchez Saldaña
read the neighbouring Problem 4.6 in that form (their p. 2). A yes for (R) gives a
yes for (W); a no for (W) gives a no for (R). The question does not fix the
generating set; Li–Sánchez Saldaña note (p. 1) that they know no group with two
finite generating sets of which only one gives type R.

**Relations to the list.** Problem 4.6 asks the same for groups of type `F_∞` with
finite cohomological dimension. Groups of type F are of that kind, so a yes to 4.6
gives a yes here and a no here gives a no to 4.6. A yes here gives the conclusion
of Problem 4.4 for groups of type F under reading (W).

**Known cases** (as reported in the sources; each import gets its own citation
route once read verbatim):

- Hyperbolic groups, every finite generating set, all large scales: Rips; cited by
  Li–Sánchez Saldaña (p. 1) as Bridson–Haefliger, Proposition III.Γ.3.23. The repo's
  `hyperbolic-rips-complex-models-proper-actions` builds on the same complex.
- `Z^n` with the standard generators: Virk, arXiv:2405.09134, Theorem 5.1 (repo
  `rips-complexes-of-integer-lattices-are-contractible`); short proof by Zaremsky,
  arXiv:2410.11993.
- Two-dimensional RAAGs with the standard generators, and closure of type R under
  amalgamated products and HNN extensions over finite subgroups (with generating
  sets containing the edge group), and `Z^n × F` for finite `F`: Li–Sánchez Saldaña,
  arXiv:2608.24279v1, Theorems 1.3–1.6 (25 Aug 2026). `VR_2(A_Γ)` contractible for
  triangle-free `Γ`: Hulbert–Zaremsky, arXiv:2608.25614.
- Every RAAG, with the generating set of products of pairwise commuting generators:
  type R, reported by Li–Sánchez Saldaña (p. 3) from Chalopin–Chepoi–Genevois–Hirai–Osajda,
  *Helly groups*, Geom. Topol. 29 (2025), Lemma 5.20 and Theorem 4.1.
- Groups whose word metric satisfies Zaremsky's Link Criterion on `[N, ∞)`:
  `VR_t(G)` contractible for all `t ≥ N` (Zaremsky, arXiv:1812.10976v3, Theorem 6.5,
  Amer. J. Math.), with examples from combings.

## Attempts

- 2026-09-13 (z4-07-type-f-rips): reformulation landed as
  `rips-complex-of-a-group-is-a-flag-cayley-complex`. Positive side in progress: a
  domination argument for groups acting properly and coboundedly on injective metric
  spaces (Helly groups, hyperbolic groups, hierarchically hyperbolic groups), which
  would give reading (W) for a large class. Negative side: a counterexample must lie
  outside every class above; candidate test objects are torsion-free groups of type F
  without coarsely injective geometry, e.g. `BS(1,2)` and the integral Heisenberg
  group, whose Dehn functions are not quadratic.
