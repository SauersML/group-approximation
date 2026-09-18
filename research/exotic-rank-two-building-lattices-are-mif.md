---
rg: 2
id: exotic-rank-two-building-lattices-are-mif
kind: claim
title: Type-preserving cocompact lattices on locally finite Ã₂ buildings, and free ones on C̃₂ buildings, exotic or not, are MIF, and hyperbolic automorphisms of C̃₂ buildings have open dense opposite geometry (Le Bars–Leibtag–Vigdorovich)
distinct_from:
  fp-simple-kac-moody-lattices-are-mif: that is Rybak's MIF theorem for Kac–Moody groups on twin buildings, via hyperbolic curtain models; this is MIF for lattices on Euclidean buildings of rank two, where no isometry is rank one, via opposition in the polygon at infinity.
  titz-witzel-kernels-are-mif: that is the application to the five simple Titz Mite–Witzel kernels; this is the general theorem it follows from.
  opposition-ping-pong-criterion-gives-mixed-identity-freeness: that is the graph's own opposition ping-pong lemma; the source proves MIF by a stronger ping-pong, transversal contractivity, and its opposite-geometry theorem is the premise the graph's route was missing.
---

**ESTABLISHED (literature import).** C. Le Bars, E. Leibtag and I. Vigdorovich, *Selflessness,
MIF and opposition in groups acting on exotic buildings*, arXiv:2609.17129v1 (15 Sep 2026). The
TeX source was read on MSI on 2026-09-18 (`lit-groups/x2609.17129/`). It is an unrefereed preprint.
**All credit is theirs**, including the application to the Titz Mite–Witzel lattices, which they
state themselves. No priority is claimed here.

## Statements (verbatim from the TeX)

1. **Theorem `Thm:MIF`.** "Let \(X\) be a locally finite affine building, and let
   \(\Gamma<\operatorname{Isom}(X)\) be a type-preserving cocompact lattice. Assume that either $X$
   if of type \(\widetilde A_2\), or that $X$ is of type \(\widetilde C_2\) and the action
   $\Gamma\actson X$ is free. Then $\Gamma$ is MIF."
2. **Their consequence.** "Theorem~\ref{Thm:MIF} establishes MIF for these
   \(\widetilde C_2\)-lattices and hence verifies the permutational Boone--Higman conjecture for
   them." "These" are the Titz Mite–Witzel lattices. The route is BFFHZ: a finitely presented
   simple MIF group satisfies PBH.
3. **Theorem `thm:gq-open-dense-opposite-geometry`.** "Let $X$ be a thick locally finite affine
   building of type $\tilde C_2$. Let $g\in\iso(X)$ be a type-preserving hyperbolic isometry. Then
   the opposite geometry \(\calO_{\calF}(g)=\{C\in\calF\mid gC\text{ is opposite }C\}\) is open and
   dense in $\calF$." Here `\calF` is the chamber set of the generalized quadrangle at infinity.

## What was checked at source (lane bh-major-product, 2026-09-18)

- **Item 3, read line by line.**
  - *Lemma `lem:gq-local-fixed-incidence`.* An open set of lines not sent to opposite lines
    consists of lines through fixed points. The argument is the girth-8 six-cycle argument, and it
    is complete as written.
  - *Lemma `lem:gq-common-neighbour-incidence`.* It uses Kramer's open-map lemmas (Kramer 1990,
    Lemmas 2.1.6–2.1.7), which were cited and not read.
  - *Proposition `prop:gq-fixed-incidence-hyperbolic`.* It uses `Fix_∂X(g) = ∂Min(g)` for
    hyperbolic `g`. That is elementary: for a ray `c` from `x ∈ Min(g)` to a fixed `ξ`,
    `t ↦ d(c(t), g c(t))` is convex and bounded, hence constant, so `c ⊆ Min(g)`. The regular case
    uses Caprace–Ciobotaru arXiv:1304.6210 Lemma 2.3 (not read). The singular case uses Tits
    geodesics of length `π` in a `C_2` apartment, and it checks.
  - *Lemma `lem:gq-no-isolated-schubert`.* It uses Kramer 1990 Prop. 2.2.6 and Thm. 2.1.3, and
    density of opposite chambers. The density is Ciobotaru–Le Bars arXiv:2601.13092,
    Cor. `cor opp dense`, which rests on Horbez–Huang–Lécureux Prop. 2.13 through a full-measure
    statement. It does **not** use the barycenter chain of Ciobotaru–Le Bars that bh-verify-euclid
    flagged as trust note T1.
- **Item 1.**
  - Proposition `prop:trans-contr_mif` (transversal contractivity ⇒ MIF) is a ping-pong, and it
    checks.
  - The `C̃₂` chain is Cor. `cor:gq-strong-nondomesticity` (item 3 plus freeness, since every
    isometry is semisimple by Parreau), then Theorem "strong non-domesticity implies transversal
    contractivity". It also cites Ciobotaru–Le Bars Prop. 6.1, Thm. 4.4 and Prop. 6.4 (cocompact
    lattices are of general type with full flag limit set).
  - The `C̃₂` case does not cite Ciobotaru–Le Bars Prop. 6.8 (topological freeness), which is the
    T1 chain. The `Ã₂` case does, at `thm A2 strong domestic`.
  - The transversal contractivity theorem itself was not re-derived.

## Consequence recorded for the graph

For a hyperbolic type-preserving `g`, a chamber fixed by `g` is not opposite itself. So
`Fix_𝓕(g) ⊆ 𝓕 ∖ 𝒪_𝓕(g)`, which has empty interior by item 3. Hence **every type-preserving action on a thick locally finite `C̃₂` building in which no nontrivial
element has a fixed point is topologically free on the chambers at infinity**. Every isometry is
semisimple (Parreau), so every nontrivial element is hyperbolic.
This comes directly from item 3, with no Ciobotaru–Le Bars barycenter input.

## Lesson for general BH

For a finitely presented simple group, PBH follows from MIF, and MIF follows from one geometric
fact: a boundary on which every nontrivial element has a nowhere-dense *domestic* set, meaning the
chambers it fails to send to opposite chambers. On trees and hyperbolic spaces this is north–south
dynamics. On rank-two buildings, where nothing is rank one, it is an incidence statement, the girth
of the polygon at infinity.

So the MIF route and the machine route (full groups, Cantor modules) are two independent
certificates. Every known finitely presented simple group now has at least one of them, and the
Titz Mite–Witzel kernels have both.

A counterexample to BFFHZ Question 3.4 would need a finitely presented simple group with neither:
- no machine;
- no boundary with nowhere-domestic elements.
