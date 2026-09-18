---
rg: 2
id: legal-f-folded-fatgraphs-give-surface-subgroups
kind: claim
title: Legal f-folded fatgraphs over a train-track map give surface subgroups of the mapping torus, with no immersion hypothesis
distinct_from:
  automorphism-immersion-representatives-have-finite-order: that shows Calegari--Walker's immersion hypothesis on f never holds for a hyperbolic free-by-cyclic group; this replaces the hypothesis by legality, which does hold for train-track representatives of automorphisms.
  random-ascending-hnn-of-free-groups-contain-surface-subgroups: that uses the criterion with f an immersion (random endomorphisms); this criterion needs only a train-track map and reaches automorphisms.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for surface subgroups in every one-ended hyperbolic group; this is a certificate criterion for mapping tori of train-track maps.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/ffold.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp5.py
---

**ESTABLISHED.** Proof in `legal-f-folded-fatgraphs-give-surface-subgroups-proof`.

Let `R` be the rose with edge set `x_1, ..., x_n`, `F = pi_1(R)`, and let `f: R -> R`
be a simplicial-after-subdivision map inducing an automorphism `phi` of `F` such that

- **(TT)** every iterate `f^j(x_i)` (`j >= 1`) is a reduced edge path.

Every positive automorphism (all `phi(x_i)` positive words) satisfies (TT). Let `Df`
be the induced map on directions at the vertex, and call directions `d, d'` *in the
same gate* when `Df^j(d) = Df^j(d')` for some `j >= 0`. Gates do not change when `f`
is replaced by a power.

Let `g: X -> R` be an `f`-fatgraph (arXiv:1212.2618, `definition:f_fatgraph`, l.802--809)
satisfying

- **(L)** at every vertex of `X` the images of the directions lie in pairwise distinct
  gates;

together with conditions (2), (3), (4) of `definition:f_folded` (l.972--985):

- (2) every `f`-vertex is 2-valent;
- (3) no vertex carries more than one `f`-vertex;
- (4) `partial^- -> X` is an embedding.

**Then `S*_f(X) -> K` is `pi_1`-injective**, where `K` is the mapping torus of `f`.
Hence, if some component of `S*_f(X)` has negative Euler characteristic (for example if
`chi(X) < 0`), `F x|_phi Z` contains a closed surface group of genus `>= 2`.

**Relation to Calegari--Walker.**

1. If `f` is an immersion, every gate is a single direction. Then (L) is condition (1),
   and this is their `proposition:f_folded_injective` (l.990--1015).
2. If `phi` has infinite outer order, `f` is not an immersion
   (`automorphism-immersion-representatives-have-finite-order`). Since every `f(x_i)`
   is reduced by (TT), `Df` is then not injective, so some gate contains two
   directions. Their proposition does not apply, and this one can.
3. The criterion is not a case of their bounded-folding proposition (l.1266). For
   `phi = (a -> bbc, b -> bbcb, c -> cbba)`, `f(a)` is a prefix of `f(b)`. So folding
   `R_1 -> R` (l.1092--1100) identifies the whole loop `a` of `R_1` with a subpath of
   `b`. Its folding region is therefore not a union of trees mapping by proper homotopy
   equivalences (l.1036--1042), and `f` does not have bounded folding.

**What it buys.** Gromov's question for a hyperbolic free-by-cyclic group
`F_n x|_phi Z` with a positive (or train-track) representative is now implied by one
finite object: a legal `f^m`-folded fatgraph with `chi < 0` for some power `m`. That
object can be checked locally, and for boundaries made of copies of one word `w` it is
decided by the linear program `lp5.py`. The obstructions and the computations for such
certificates are in `positive-f-folded-fatgraphs-have-only-even-valence`.
