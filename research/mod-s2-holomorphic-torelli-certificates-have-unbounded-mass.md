---
rg: 2
id: mod-s2-holomorphic-torelli-certificates-have-unbounded-mass
kind: claim
title: A compact holomorphic curve in a deep-level Siegel threefold meets the Humbert product divisor at least 5 |Phi mod 3n| times, so holomorphic certificates cannot bound A_+
distinct_from:
  mod-s2-torelli-positive-relations-have-bounded-mass: that is the open uniform bound sup A_+ < infinity; this proves that one geometric class of certificates for it, compact holomorphic curves in A_2(Gamma'), has mass tending to infinity with the level, and leaves the bound open.
  mod-s2-torelli-characters-have-a-metaplectic-maslov-line: that computes F = 5m on the Maslov line and does not identify F with an intersection number; this proves mass = C . H_1 = 5 deg(lambda|C) for curve certificates and bounds it below by a monodromy index.
  mod-s2-maslov-line-is-optimal-for-torelli-characters: that shows optimality of the Maslov line for Torelli characters; this bounds from below the mass of holomorphically realized relation vectors.
  mod-s2-induced-torelli-characters-have-positive-relation-floors: that proves the per-level floor 1/(3 A_+); this is a lower bound on the mass of one class of positive relations at deep levels.
artifacts:
  - research/artifacts/van-der-geer-chi10-baily-borel-verified.md
---

**ESTABLISHED** (`mod-s2-holomorphic-torelli-certificates-unbounded-mass-proof`). Unreviewed.

## Setting

Notation of `mod-s2-induced-torelli-characters-have-positive-relation-floors`: `Gamma' <= Sp_4(Z)` of
finite index, `Z^r = H_1(I)_(Gamma')` with one coordinate per `Gamma'`-orbit `o` of symplectic splittings,
and the mass of `b in Z^r` is `chi(b) = sum_o b_o`.

- `H_2` is the Siegel upper half space of degree 2, and `A_2(Gamma') = Gamma' \ H_2`. For
  `Gamma' <= Gamma(3)` the group is torsion-free and acts freely, so `A_2(Gamma')` is a complex manifold
  with `pi_1 = Gamma'`.
- `H_1 subset A_2(Gamma')` is the reduced image of the `Sp_4(Z)`-orbit of the diagonal `{z = 0}`, the
  locus of products of elliptic curves. Translates of the diagonal correspond to unordered symplectic
  splittings `g(V_1 (+) V_2)`. So `H_1 = sum_o D_o`, with one part `D_o` (possibly reducible) for each
  coordinate of `Z^r`.
- `lambda` is the Hodge line bundle on `A_2(Gamma')`. Its sections of `lambda^k` are the modular forms of
  weight `k` for `Gamma'`.

A **holomorphic certificate** at `Gamma' <= Gamma(3)` is a nonconstant holomorphic map
`f : C~ -> A_2(Gamma')` with the following properties:
- `C~` is a compact connected Riemann surface;
- `f(C~)` is not contained in `H_1`.

Its **relation vector** is `b(f)_o = deg f^* D_o`. This is the number of points of `f^(-1)(D_o)`, counted
with local intersection multiplicity. So `b(f) >= 0` and `chi(b(f)) = deg f^* H_1`.

The **level-3 monodromy** of `f` is defined as follows.
- Let `g = p o f : C~ -> A_2(3)`, where `p : A_2(Gamma') -> A_2(3)` is the covering map, and let
  `C_3 = g(C~)`.
- Let `nu : C~_3 -> A_2(3)` be the normalization of `C_3`.
- Then `Phi(f) = nu_* pi_1(C~_3) <= Gamma(3)`, defined up to conjugacy in `Gamma(3)`.

## Statement

**(H1) Mass is a Hodge degree.** For every holomorphic certificate, `chi(b(f)) = 5 deg f^* lambda`, and
`deg f^* lambda >= 1`. In particular every compact curve in `A_2(Gamma')` meets `H_1`, and the mass of
every holomorphic certificate is a positive multiple of 5.

**(H2) Monodromy lower bound.** Let `n >= 1` and let `Gamma' <= Gamma(3n)` have finite index. For every
holomorphic certificate `f` at `Gamma'`,

    chi(b(f)) >= 5 [Phi(f) : Phi(f) cap Gamma(3n)] = 5 |Phi(f) mod 3n|,

and `Phi(f)` is an infinite group.

**(H3) Uniform divergence.** For every `D` there is `n_0(D)` with the following property. For every
`n >= n_0(D)` and every finite-index `Gamma' <= Gamma(3n)`, every holomorphic certificate at `Gamma'` has
mass `> 5D`.

(H1) and (H2) use no input about the Torelli group. The following remark ties certificates to `B`; it is
not needed for (H1)-(H3).

**Remark (certificates are relations; trust: Mess).** By Mess's description of genus-2 Torelli space as
`H_2` minus the orbit of the diagonal, the meridian around the translate for a splitting `sigma` is a
separating twist of splitting `sigma`. This description is not verified in the repo. Given it, the relation
`prod [a_j, b_j] prod gamma_i = 1` in `pi_1(C~ - f^(-1) H_1)`, pushed into `pi_1(A_2(Gamma') - H_1) = Lambda`,
shows `b(f) in B` up to a global sign. The sign is harmless, since `B` is a group. So every holomorphic
certificate is a positive relation in the sense of `mod-s2-torelli-positive-relations-have-bounded-mass`,
with mass `5 deg f^* lambda`.

## What this kills

**Class killed.** The class is every attempt to prove `sup A_+ < infinity` by exhibiting, at each level, a
compact holomorphic curve in the Siegel threefold. It includes:
- Shimura curves and other special curves;
- complete intersections of modular-form divisors avoiding the 1-dimensional Satake boundary;
- pullbacks of one fixed level-3 curve;
- holomorphic genus-2 Lefschetz fibrations over compact curves with only separating nodes. Their period map
  extends across compact-type fibres to a holomorphic curve in `A_2(Gamma')`. This extension is standard but
  is not proved here.

By (Mono), `sup A_+` is controlled by the cofinal levels `Gamma(3n)`, and by (H3) no certificate of this
class has mass `<= 5D` there once `n >= n_0(D)`.

**Named invariant.** The Hodge degree `deg f^* lambda = chi/5` together with the finite image
`|Phi(f) mod 3n|` of the level-3 monodromy.

**Where every member dies.** Every member dies at the covering degree `deg(C~ -> C~_3) >= |Phi(f) mod 3n|`
(step 3 of the proof). A curve at level `3n` covers its level-3 image with at least as many sheets as the
level-3 monodromy has residues mod `3n`. The monodromy is infinite because `H_2` is a bounded domain and has
no compact curves (step 4). Only finitely many monodromy classes occur in each degree, because curves of
bounded degree form a finite-type family (step 5).

**Consistency.** At level 3 the census point stars have mass 5
(`mod-s2-torelli-abelian-census-limit-is-positive`). Mass 5 is exactly the smallest value (H1) allows, i.e.
`deg lambda = 1`. Whether those stars are realized by `lambda`-lines in `A_2(3)*` (the Burkhardt quartic) is
not tested.

## What is left

`sup A_+ < infinity` can hold only through positive relations in `B` that are not realized by compact
holomorphic curves in any fixed complex structure. Concretely, via the dictionary in
`mod-s2-maslov-line-is-optimal-for-torelli-characters`, these are achiral or merely symplectic genus-2
Lefschetz fibrations over closed surfaces with the following properties:
- every vanishing cycle is separating;
- the monodromy lies in `Lambda = pi^(-1)(Gamma')`;
- the number of singular fibres is bounded independently of the level.

Symplectic Lefschetz fibrations need not be holomorphic, so (H3) says nothing about them. What (H3) does
say is that no such fibration of bounded size can be deformed to a holomorphic one at deep level.

The positive direction therefore needs a symplectic, non-Kahler construction. The negative direction (mass
growth, which refutes the uniform floor only together with the (TD) caveat of the bounded-mass node) would
need an extension of steps 1-3 from holomorphic curves to arbitrary 2-cycles.
- Step 1 (mass = `5 deg lambda`) uses that a holomorphic curve meets `H_1` positively.
- Step 3 (degree bounds the index) uses that a nonconstant holomorphic map of compact Riemann surfaces is a
  branched covering.
- Neither holds for a smooth surface meeting `H_1` with signs. No topological substitute is known here.
