---
rg: 2
id: zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved
kind: claim
title: "Zaremsky Problem 2.19(a) resolved: does every hyperbolic group embed in some Brin-Thompson group nV?"
---

Part (a) of `zaremsky-2-19-embeddings-into-brin-thompson-groups`, verbatim from
the list: "Does every hyperbolic group embed in one of these?", where "these"
are V, 2V, 3V, ...

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-19a-by-yes` requires
  `every-hyperbolic-group-embeds-in-some-brin-thompson-group`.
- **No**: `zaremsky-2-19a-by-no` requires
  `some-hyperbolic-group-embeds-in-no-brin-thompson-group`.

Never write a `requires: []` route into this claim.

## Reading

- A hyperbolic group is a finitely generated word-hyperbolic group.
- Since jV embeds in kV for j < k, a yes means that for each hyperbolic group
  `G` there is `n` with `G ≤ nV`. A no means that some hyperbolic group embeds
  in no nV.

## What is known

- Belk–Bleak–Matucci, arXiv:1602.08635:
  - Theorem 1.1: for any finite simple graph Γ the right-angled Artin group
    `A_Γ` embeds in nV, with `n = |V(Γ)| + |E^c(Γ)|`.
  - p. 2: any group that virtually embeds in nV embeds in nV.
  - Corollary 1.5: every virtually special group embeds in some nV. This
    includes all finitely generated Coxeter groups, many word-hyperbolic groups
    (among them all one-relator groups with torsion), all limit groups, and many
    3-manifold groups.
- Agol, *The virtual Haken conjecture*, Doc. Math. 18 (2013), Theorem 1.1: a
  hyperbolic group acting properly and cocompactly on a CAT(0) cube complex is
  virtually special. So every cubulated hyperbolic group embeds in some nV.

## Where an answer must come from

- **Yes.** An answer must handle the hyperbolic groups that virtually embed in
  no RAAG. Every infinite hyperbolic group with property (T) is one: RAAGs act
  properly on CAT(0) cube complexes, so they have the Haagerup property, and
  that property passes to subgroups and to finite-index overgroups.
- **No.** An answer needs an obstruction to embedding in every nV. The only
  candidate known to this lane is the Haagerup property of nV for infinitely
  many n (Problem 2.7, lane z2-07-nv-haagerup). It would exclude every infinite
  hyperbolic group with property (T).
  Conversely, a yes here, applied to one infinite hyperbolic (T) group, shows
  that nV fails the Haagerup property for every large n.
- **Non-obstructions.** Some properties of nV pass to subgroups but do not
  obstruct hyperbolic groups:
  - solvable word problem;
  - torsion local finiteness, if it holds (claimed by Kojima–Sheng, arXiv:2603.18410;
    for `n >= 2` the proof is invalid by
    `kojima-sheng-two-generator-torsion-criterion-fails-in-v` (a22c90a4a), and the
    statement is open, `brin-thompson-2v-is-torsion-locally-finite`, `brin-thompson-groups-contain-infinite-periodic-groups`);
  - abelian germ groups. The germ at x of an element of nV fixing x is
    determined by its vector of prefix-length changes in `Z^n`: an element with
    zero vector at a fixed point is the identity on the whole subcube containing
    it.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv, unreviewed): the cubulated case is
  settled by Belk–Bleak–Matucci plus Agol. The open core is the hyperbolic
  groups that virtually embed in no RAAG.
- 2026-09-13, same lane: the commensurated-set argument of
  `fw-subgroups-of-eventually-similar-groups-virtually-embed`, which makes FW
  subgroups of V finite, does not transfer to nV for n ≥ 2.
  - The set of subcubes is not commensurated. Take the rearrangement of
    `({0,1}^ω)^2` that fixes `C×[0]` and swaps `[0]×[1]` with `[1]×[1]` by
    changing the first digit of the first coordinate, where `C = {0,1}^ω`.
  - For every nonempty prefix `w`, it sends the subcube `[w]×C` to
    `[w]×[0] ∪ [w']×[1]` with `w' ≠ w`, which is not a subcube. So infinitely
    many subcubes leave the set.
  - Consequently there is no cheap proof that Kazhdan subgroups of nV are
    finite. That finiteness is the open (T) and Haagerup question of
    Problem 2.7.
