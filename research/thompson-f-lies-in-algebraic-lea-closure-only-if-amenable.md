---
rg: 2
id: thompson-f-lies-in-algebraic-lea-closure-only-if-amenable
kind: claim
title: Groups without a copy of Thompson's F are closed under extensions, graphs of groups, graph products, products and local embeddability, so F lies in the algebraic closure of the LEA groups only if it is amenable
distinct_from:
  thompson-f-is-lea-only-if-amenable: that is the base case, one local embedding into one amenable group; this closes the class of F-free groups under every algebraic permanence operation, including arbitrary extensions and graphs of groups with arbitrary edge groups.
  lea-permanence-closure-fp-kazhdan-groups-are-residually-finite: that uses property (T) and FA to force residual finiteness of Kazhdan groups in a smaller closure; F has neither (T) nor FA, and here the tree step uses the absence of free subgroups and the normal-subgroup structure of F instead.
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that is for finitely presented simple nonsofic groups; F is not simple, its soficity is open, and its closure allows arbitrary extensions, which a simple group never needs.
  thompson-f-relator-system-stable-in-permutations: that is the open root; this shows that no soficity theorem of permanence shape can refute it without proving F amenable, and names the metric step where the argument stops.
---

**ESTABLISHED (unreviewed).** Let `F` be Thompson's group and `c = [x_0, x_1]`.

**The closure.** `𝒦` is the smallest class of groups that contains every LEA group (locally embeddable
into amenable groups) and is closed under:
- (K1) subgroups;
- (K2) directed unions;
- (K3) local embeddability into `𝒦`. This covers limits in the space of marked groups and algebraic
  ultraproducts;
- (K4) **arbitrary** extensions: `N ⊴ G` with `N` and `G/N` in `𝒦` gives `G` in `𝒦`;
- (K5) arbitrary direct products, restricted or unrestricted;
- (K6) fundamental groups of graphs of groups with vertex groups in `𝒦` and **arbitrary** edge groups;
- (K7) graph products of groups in `𝒦`.

Permutational wreath products, restricted or unrestricted, lie in `𝒦` by (K2), (K4) and (K5).

**Theorem.**
1. **F-free groups are closed.** The class `𝒫` of groups with no subgroup isomorphic to `F` is closed
   under (K1)–(K7), with no hypothesis on `F`.
2. **Dichotomy.** `F ∈ 𝒦` exactly when `F` is amenable.

**The four facts used.**
- Every nontrivial normal subgroup of `F` contains `F'` (Cannon--Floyd--Parry).
- `F'` contains a copy of `F`, for instance `F_[1/4,3/4]`.
- `F` is finitely presented.
- `F` has no nonabelian free subgroup (`thompson-f-has-no-free-subgroups`).

The mechanism is primality: `F ≤ G` and `N ⊴ G` force `F ↪ G/N` or `F ↪ N`. Every homomorphism from
`F` that does not kill `c` is injective, and every action of `F` on a tree has a copy of `F` fixing a
vertex.

**Consequences for the root.**
- **Class-killing obstruction.** `𝒦` contains every group that the standard soficity permanence
  theorems produce from LEA groups:
  - sofic-by-amenable extensions (Elek--Szabó);
  - amalgams and HNN extensions over amenable subgroups (Elek--Szabó, Păunescu, Dykema--Kerr--Pichot);
  - graph products (Ciobanu--Holt--Rees);
  - wreath products (Hayes--Sale);
  - weakly-sofic-by-residually-finite extensions (Glebsky);
  - Kun--Thom-type split extensions.

  So none of them, and no combination, proves `F` sofic unless it proves `F` amenable. Equivalently, no
  such host yields separating almost-solutions for `thompson-f-relator-system-stable-in-permutations`.
  A refutation of the root that avoids amenability needs an approximation that is metric at its core.
- **Where the argument stops.** In the metric ultraproduct `∏ Sym(n)/U`, a copy of `F` lifts only to
  almost-homomorphisms `F_2 → Sym(n)`. These have no kernel, so step "hom not killing `c` is injective"
  has nothing to act on. This is exactly the gap between `𝒦` and soficity.
- **Measured survivor.** Elek--Lippner: if some free pmp action of `F` has a sofic orbit relation, `F` is
  sofic. Relations of the form `R_1 *_(R_0) R_2`, with `R_1, R_2` sofic and `R_0` hyperfinite, are sofic
  (Dykema--Kerr--Pichot, Păunescu). The tree step has no measured analogue that excludes these. The
  measured Tits alternative produces a free subrelation, and every nonamenable relation contains one
  (Gaboriau--Lyons), so there is no contradiction to draw. The fixed price 1 of `F` (Tucker-Drob) is
  consistent with such splittings, since `C(R_1) + C(R_2) - C(R_0)` can equal 1.

**Scope.**
- The theorem uses only the four facts above. It applies verbatim to any finitely presented group
  without free subgroups whose nontrivial normal subgroups contain its derived subgroup, when that
  derived subgroup contains a copy of the group.
- Each step is a standard argument, and no novelty of technique is claimed. The contribution is the
  arbitrary-extension and arbitrary-edge closure for `F`, and the location of the survivors.
- It leaves `thompson-f-is-sofic` and the root OPEN.

Proof: `thompson-f-lies-in-algebraic-lea-closure-only-if-amenable-proof`.
