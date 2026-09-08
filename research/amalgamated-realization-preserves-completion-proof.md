---
rg: 2
id: amalgamated-realization-preserves-completion-proof
kind: route
title: Read the free-product kernel off the Bass-Serre star and collapse both spectral sequences
target: amalgamated-realization-preserves-completion
requires:
  - finite-block-coordinates-share-one-mf-image
artifacts:
  - non_mf_groups_exist.tex
---

## Proof

Normal form embeds `P` and `A`, the presentation is finite, and soficity
follows from amalgamation over `Z` [Collins-Dykema, Theorem 3.4].  `q` is a
retraction.

**(1)** Every MF homomorphism of `P` factors through `chi`, so an MF
homomorphism of `G_A` is determined by its restriction to `A`; that gives
the bijection, the radical formula, and non-MFness of `G_A`.

**(2)** The quotient of the Bass-Serre tree of the amalgam is a star: the
`A`-vertex has trivial stabilizer, the `P`-vertices are indexed by
`A/<a>` with stabilizers conjugate to `N`, and edge stabilizers are
trivial.  Hence `ker q ~= *_(A/<a>) N`.  Its MF images are trivial because
each factor's are; it is perfect and rationally acyclic because `N` is.

**Rational acyclicity of `N`.**  `B` is a free product of finite groups, so
its rational homology vanishes in positive degrees and `E ->> V` is a
rational homology isomorphism.  Write `L = Z[1/2]^3` for the translation
subgroup of `V`, so `V/L ~= SL_3(Z) x <t>`.  Then `H_j(L; Q) = /\^j Q^3` and
`t` acts by `2^j`; for `1 <= j <= 3` the map `2^j - 1` is invertible over
`Q`, so both invariants and coinvariants of `<t>` vanish and only the row
`j = 0` survives.  The positive-degree rational homology of `SL_3(Z)`
vanishes [Soule], so `H_*(V; Q) ~= H_*(Z; Q)` through the height map.  For
`N`, use the graph of groups with vertex groups `E_i` indexed by `Z`,
infinite cyclic edge groups `<d_i> = <r_(i+1)>`, and a line as underlying
graph.  In degree one the edge generator has height `0` in `E_i` and
height `1` in `E_(i+1)`, so the edge-to-vertex map is the shift on
`(+)_(i in Z) Q`, an isomorphism; in degree zero it is injective because
the graph is a tree.  Mayer-Vietoris gives `H_j(N; Q) = 0` for `j > 0`.

**(3)** Finite groups are MF, so (1) gives the isomorphism of profinite
completions.  Since `ker q` is rationally acyclic and acts trivially on
`q^* M`, both Lyndon-Hochschild-Serre spectral sequences collapse.

**(4)** If `A = <a>` then `G_A = P`.  Otherwise the amalgam is proper.
Take a nontrivial finite-order `z in B <= P`.  If `s^k = z s^l z^(-1)` then
`chi` gives `k = l`, and for `k != 0` the resulting `s^k z s^(-k) = z`
contradicts Britton's lemma, since `z` lies in neither edge group of `P`.
So `<s> ^ z<s>z^(-1) = 1`, and the amalgam criterion [Minasyan-Osin,
Corollary 2.2] gives acylindrical hyperbolicity; the embedded `P` excludes
the virtually cyclic alternative.  A finite normal subgroup fixes the whole
minimal tree and lies in an infinite cyclic edge group, so is trivial.  The
reduced-algebra conclusions follow from [DGO, Theorem 2.35],
[Gerasimova-Osin, Theorem 1.1], the faithful canonical trace, and the
embedded non-MF subgroup `P`.
