---
rg: 2
id: zaremsky-4-04-type-fn-groups-have-connected-rips-complex
kind: claim
title: "Zaremsky Problem 4.4 resolved: does every group of type F_n admit an (n-1)-connected Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is the question whether Z^n with its standard word metric has contractible Rips complexes at large scale; this asks, for every n, whether type F_n can always be witnessed by an (n-1)-connected Rips complex of the group for some generating set and scale
  hyperbolic-rips-complex-models-proper-actions: that is the classical theorem that large-scale Rips complexes of hyperbolic groups are finite models for proper actions; this is the question for arbitrary groups of type F_n and only (n-1)-connectivity
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 4,
verbatim: "If a group is of type F_n does it admit an (n − 1)-connected Rips
complex? For n = 2 the answer is yes, but for n > 2 we don't know."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-04-by-yes` requires
  `type-fn-groups-have-n-minus-1-connected-rips-complexes`.
- **No**: `zaremsky-4-04-by-no` requires
  `some-type-fn-group-has-no-n-minus-1-connected-rips-complex`.

Never write a `requires: []` route into this claim.

## Reading

- A *Rips complex* of a finitely generated group `G` is `R_t(G,S)` for a
  finite generating set `S` and a scale `t >= 0`: vertex set `G`, simplices
  the finite nonempty subsets of `d_S`-diameter at most `t`. `G` acts
  simplicially, freely on vertices, cocompactly, with finite simplex
  stabilizers.
- "Admit" is existential: some `S` and some `t`. A stronger variant (every
  finite generating set, every large enough scale) is not what is asked; for
  `n = 2` both hold.
- Converse direction, standard: an (n−1)-connected Rips complex forces type
  `F_n` (Brown's criterion for proper cocompact actions with finite
  stabilizers). So the question is whether type `F_n` is always witnessed by a
  Rips complex.
- Reformulation, established in `group-rips-complexes-are-cayley-graph-flag-complexes`:
  for a given `n` the question asks whether every group of type `F_n` has a
  finite generating set whose Cayley graph has an (n−1)-connected clique
  complex, i.e. acts freely, vertex-transitively and cocompactly on an
  (n−1)-connected flag simplicial complex.
- `n = 1` is trivial. `n = 2`, every finite generating set and every
  `t >= max(1, L/2)` with `L` the longest relator: established in
  `fp-groups-have-simply-connected-rips-complexes`.

## What is known (sources read 2026-09-13 unless marked)

- Essential connectivity. Zaremsky, arXiv:1812.10976, Lemma 6.3: for any word
  metric, `G` is of type `F_n` iff the filtration `{VR_t(G)}` is essentially
  (n−1)-connected (Brown's criterion). The open gap is actual versus essential
  connectivity.
- arXiv:1812.10976, Remark 6.6: after enlarging the generating set, `VR_1` is
  the flagification of a Cayley graph (the reformulation above). Theorem 6.5
  there: a word metric satisfying the Asymptotic Link Criterion gives
  contractible `VR_t(G)`. The paper remarks it does not know whether every
  group of type `F_*` has a contractible proper Rips complex.
- Contractible at large scale: hyperbolic groups (Rips;
  `hyperbolic-rips-complex-models-proper-actions`), groups with contracting
  combings (Alonso, as cited in arXiv:1812.10976), `Z^n` (Virk,
  arXiv:2405.09134; root 4.3).
- Hulbert–Zaremsky, arXiv:2608.25614. Theorem A: a local Morse criterion
  (`D_t(S)` (n−|S|−1)-connected for every word-length-constant `S`) implies
  `VR_t(G)` is (n−1)-connected. Theorem B: `VR_2(A_Γ)` is contractible for
  triangle-free `Γ`. Theorem C: a finite-presentability criterion. Question 1.1
  is the contractible version of this problem.
- Li–Sánchez Saldaña, arXiv:2608.24279: type R (contractible Rips complexes at
  all large scales) is closed under graphs of groups with finite edge groups
  (Theorems 1.3, 1.4) and holds for 2-dimensional RAAGs with standard
  generators (Theorem 1.5) and for `Z^n × F` (Theorem 1.6).
- Every RAAG has contractible Rips complexes for the clique-product
  generating set: Chalopin–Chepoi–Genevois–Hirai–Osajda, *Helly groups*,
  Theorem 4.1 and Lemma 5.20, as cited in both papers above; not re-read.
- This lane: closure under direct products
  (`connected-rips-complexes-pass-to-direct-products`), and level sets of
  CAT(0) cube complexes (`cube-level-set-clique-complexes-model-the-level-set`).
  The latter covers Bestvina–Brady groups once one citation check is done.
- In these sources the problem is open for `n > 2` as of 2026-09-13.

## Attempts

- 2026-09-13 (lane z4-04-fn-rips): landed the reformulation, the `n = 2` case
  and product closure. Level sets: when a group acts freely and transitively on
  the vertices of a level set of a CAT(0) cube complex, the Helly property of
  cubes and the nerve theorem show the Cayley clique complex is homotopy
  equivalent to the level set. This reaches Bestvina–Brady kernels, which are
  of type `F_n` but not `F_{n+1}`, but never infinite Kazhdan groups.
