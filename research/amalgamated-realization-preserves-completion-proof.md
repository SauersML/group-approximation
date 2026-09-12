---
rg: 2
id: amalgamated-realization-preserves-completion-proof
kind: route
title: Read the free-product kernel off the Bass-Serre star and collapse both spectral sequences
target: amalgamated-realization-preserves-completion
requires:
  - sofic-cyclic-mf-quotient-with-full-radical
artifacts:
  - research/artifacts/sofic-cyclic-mf-quotient.md
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

## Proof

The cyclic seed and its HNN normal form are proved in
`research/artifacts/sofic-cyclic-mf-quotient.md`; its affine quotient
and finite-block kernel are constructed in Sections 3--4 of
`research/artifacts/finite-block-perfect-mf-radicals.md`.
The arguments for the new amalgam and for rational acyclicity are
given below. The classical source names used below have the following
precise references: Collins--Dykema, *Free products of sofic groups
with amalgamation over monotileably amenable groups*,
[Theorem 3.4](https://arxiv.org/html/1003.1675v4#S3);
Soulé, *The cohomology of SL_3(Z)*,
[Topology 17 (1978), 1--22](https://doi.org/10.1016/0040-9383(78)90009-5);
Minasyan--Osin, *Acylindrical hyperbolicity of groups acting on trees*,
[Corollary 2.2](https://arxiv.org/pdf/1310.6289);
Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and
rotating families in groups acting on hyperbolic spaces*,
[Theorem 2.35](https://doi.org/10.1090/memo/1156); and
Gerasimova--Osin, *On invertible elements in reduced C*-algebras of
acylindrically hyperbolic groups*,
[Theorem 1.1](https://arxiv.org/abs/1910.14524).

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
