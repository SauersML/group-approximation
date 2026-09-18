---
rg: 2
id: rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh
kind: claim
title: A finitely generated relatively hyperbolic group with solvable word problem whose peripheral subgroups embed in finitely presented simple groups embeds in a finitely presented simple group
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that is the case with no (or hyperbolic) peripheral subgroups, proved by Belk--Bleak--Matucci--Zaremsky; this asks for arbitrary peripheral subgroups that are themselves in the Boone--Higman class.
  boone-higman-conjecture: that quantifies over all decidable finitely generated groups; this is one permanence property of the class, which the conjecture implies.
  bh-class-free-products-iff-joint-embedding-and-free-z: that characterizes free-product closure, which is the special case of this statement where G is a free product of its peripheral subgroups.
artifacts:
  - research/artifacts/gq-bh-bh-relhyp-attack.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem,
hyperbolic relative to finitely generated subgroups `P_1, ..., P_m`, each of which
embeds in a finitely presented simple group. Then `G` embeds in a finitely presented
simple group.

This is not an item of Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356, Problem 5.3
(checked against the arXiv HTML of v3). It is the natural relative version of their
hyperbolic theorem.

## What is known

- **Hyperbolic peripherals.** If every `P_i` is hyperbolic, `G` is hyperbolic
  (standard: Osin, Mem. AMS 179 (2006); not re-read), so
  `hyperbolic-groups-satisfy-boone-higman` applies.
- **Linear inputs.** Limit groups (BBMZ survey Theorem 5.1(5)) and fundamental
  groups of finite-volume hyperbolic manifolds are relatively hyperbolic and
  finitely generated linear, so `finitely-generated-linear-groups-satisfy-boone-higman`
  covers them. For finite-volume hyperbolic 3-manifolds this is also survey
  Theorem 5.1(8). So the statement adds nothing for these named families.
- **Free products in the permutational class.** Belk--Fournier-Facio--Hyde--Zaremsky,
  arXiv:2503.21882 (abstract), prove that the permutational Boone--Higman property
  is closed under free products. That settles the case `G = P_1 * ... * P_m` with
  all `P_i` in the permutational class.
- **Cusp extensions.** `cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh`:
  for torsion-free hyperbolic `H`, `h ≠ 1` and finitely generated `P` in the permutational
  class, `H *_{E(h)} (E(h) × P)` (hyperbolic relative to `E(h) × P`) embeds in a finitely
  presented simple group. This is the first case here that is neither hyperbolic, nor
  linear, nor a free product.
- **Cusp extensions, general.** `cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh`:
  for any finitely generated relatively hyperbolic `G ∈ B_A` (torsion allowed, for
  example any hyperbolic group), adding finitely many cusps `E(g_i) × K_i` along
  pairwise non-commensurable loxodromic elements, with `K_i ∈ B_A`, stays in `B_A`, and
  the result is hyperbolic relative to the old and new peripheral subgroups. The key
  input is `pbh-coset-condition-passes-to-finite-index-overgroups`: `E(g)` contains the
  centralizer `C(g)` with finite index.

## Consequences and reductions (landed)

- **At least as hard as free-product closure.**
  `rel-hyperbolic-bh-permanence-implies-free-product-closure`: this statement implies
  that the Boone--Higman class is closed under free products, hence joint
  embedding for finitely presented simple groups and `U * Z ∈ 𝓑`. Those are OPEN.
- **At least as hard as finite-edge amalgams.**
  `rel-hyperbolic-permanence-implies-finite-edge-amalgams`: this statement implies
  closure of the Boone--Higman class under amalgams and HNN extensions over finite
  subgroups. Its B_A form implies the open conjugacy step of
  `free-permutational-products-preserve-pbh`.
- **Finitely presented simple peripherals suffice.**
  `rel-hyperbolic-groups-embed-with-fp-simple-peripherals`: it is enough to prove
  the statement when every `P_i` is a finitely presented simple group (and then
  `G` may be taken finitely presented).

## Attempts

**Attempt 1 (bh-relhyp, 2026-09-18): germ extension over a relative boundary. Not
constructed.**
- *Why the BBMZ proof does not transfer directly.* Their embedding goes through a
  full contracting rational similarity group (their Theorems B, C, E), and they
  note (§1.3, with their Proposition 5.5) that every germ group of such a group is
  virtually cyclic. The hyperbolicity is used in their contracting lemma (Lemma
  4.19). A peripheral subgroup of `G` that is not virtually cyclic would have to act
  without contributing a large germ group at any point, and nothing in their
  construction arranges that. This part is a reading of their method, not a
  theorem.
- *The route that remains.* Belk--Hyde--Matucci, arXiv:2407.03149 (TeX read; label
  `cor:MainFinitenessCorollary`), allow a finite germ extension `E` of a base `B` to
  have germ groups larger than those of `B`: condition (3) there asks only that
  `(B)_p ⊴ (E)_p` with `(E)_p/(B)_p` of type `F_n`. After the reduction above the
  peripheral subgroups are finitely presented, so germ groups such as
  `(B)_p × S_i` are allowed. The missing input is:

  **(RB)** For `G` hyperbolic relative to finitely presented simple `S_1, ..., S_m`,
  find a Cantor space `X`, a faithful `G`-action on `X` and a base `B ≤ Homeo(X)`
  such that `G` lies in a finite germ extension `E` of `B` whose singular set is a
  finite union of `B`-orbits of points fixed by conjugates of the `S_i`, with germ
  groups `(E)_p ≅ (B)_p × S_i`. It must also satisfy hypotheses (1)--(2) of that
  corollary (`B` oligomorphic on the singular set, fixers of finite sets of type
  `F_2`) and the hypotheses of their simplicity theorem (label `thm:Simplicity`:
  `B` simple, locally moving, no global fixed point, same orbits as `E`).

  `B` cannot be `V` in general, since the non-parabolic part of `G` must act by
  elements that locally agree with `B`. The natural candidate is a relative
  version of BBMZ Theorem 4.1: a full contracting rational similarity group acting
  on a "relative horofunction boundary" of `G`, in which the parabolic points are
  exactly the singular points. No such construction is known here.
- *Calibration.* By `rel-hyperbolic-bh-permanence-implies-free-product-closure`,
  (RB) for `G = S * T` with `S, T` finitely presented simple would already prove
  free-product closure of the Boone--Higman class. So (RB) is a genuinely new
  input, not a formality.

**Attempt 2 (bh-relhyp, 2026-09-18): amalgams over centralizers. Partial success.**
Instead of a germ extension, work algebraically inside relative holomorphs.
`centralizer-amalgams-embed-in-relative-holomorphs` puts `G *_{C_G(F)} (C_G(F) × P)` in
`(G * Z) ⋊ Aut_G(G * Z)` for any group `G`; with `pbh-class-closed-under-relative-holomorphs`
this gives `pbh-class-closed-under-centralizer-amalgams`, and hence the cusp extensions
above. What remains for this claim: peripheral structures that are not obtained from a
hyperbolic group by amalgamating along centralizers (for example general Dehn-filling
preimages), peripherals in the Boone--Higman class but not the permutational one, and
hyperbolic groups with torsion (where `C_H(h)` can be a proper subgroup of `E(h)`). The
torsion case is now settled by `cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh`.

**Attempt 3 (bh-relhyp, 2026-09-18): graphs of groups over good edges.**
`pbh-graphs-of-groups-over-realized-good-edges` puts a finite graph of groups in `B_A` once
its vertex groups embed in one `B_A`-group in which each edge identification is a
conjugation and each edge image is good. For relatively hyperbolic inputs this covers
acylindrical graphs of groups whose edge maps are realized in this way (Dahmani, Theorem
0.1(1), gives the relative hyperbolicity). A general relatively hyperbolic group is not a
graph of groups over its peripheral structure, so the claim stays OPEN. What is missing
is a way to build, from `G` alone, an ambient `B_A`-group in which `G` is visible.

**Attempt 4 (bh-relhyp, 2026-09-18): Dehn filling. Not constructed.** Let `P` be residually
finite, and let `N ⊴ P` have finite index and avoid the finite set in
`relatively-hyperbolic-dehn-filling`. Then `Ḡ = G/<<N>>` is hyperbolic relative to the
finite group `P̄ = P/N`, so `Ḡ` is hyperbolic and lies in `B_A`. The group
`W = Ḡ *_{P̄} (P̄ × P)` is a free permutational product over a finite stabilizer, so it
lies in `B_A` (`free-permutational-products-preserve-pbh`).

If `G` embedded in `W` by `p ↦ (p̄, p)` on `P`, extended over the other generators, then
the B_A form of this claim would follow for residually finite peripherals. With the
naive extension `x ↦ x̄` the map is not a homomorphism. Take
`G = Z^2 *_{a = w} F(y, z)`, with `Z^2 = <a, b>` and `w = y z y^(-1) z`. The relator
`a = w` would force the lamp `a_{ω_0}` to be trivial. Correcting the images of `y` and
`z` by elements of the kernel `*_{Ḡ/P̄} P` leads to an equation in that free product,
and no solution was found.

The map cannot be a splitting in general. For `G = Z^2 * Z` and `N = (kZ)^2`, the group
`G` is torsion-free while `Ḡ` has torsion, so `G` is a non-split extension of `Ḡ`
(although this `G` does embed in `W`). The example `G` above is in `B_A` anyway, by
`pbh-graphs-of-groups-over-realized-good-edges` with `D = F_2 × Z`.

## Scope

Nothing here embeds any new group in a finitely presented simple group.
