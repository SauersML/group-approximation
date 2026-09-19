---
rg: 2
id: countable-sets-never-separate-continua-without-local-cut-points
kind: claim
title: No countable closed set separates a Peano continuum without local cut points; so for every one-ended hyperbolic group that is not virtually Fuchsian and does not split over a two-ended subgroup (every infinite Kazhdan hyperbolic group, every random group at density below 1/2), the shear frontiers of loxodromic elements are uncountable
requires:
  - busemann-frontiers-separate-the-boundary
distinct_from:
  busemann-frontiers-separate-the-boundary: that proves the shear frontier separates the boundary and needs the topological input (T0), recalled only for spheres; this proves (T0) for all Peano continua without local cut points and applies it to Kazhdan and random groups.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; elementary point-set topology; Referee bh-ref-q12 2026-09-19: Lemma PASS, and the application to Kazhdan and random groups PASS with two wording repairs). The statement is
probably classical (in the style of Whyburn's *Analytic Topology*). No priority is claimed, and the literature was
not searched beyond two web queries.

## Lemma

Let `X` be a Peano continuum (a locally connected metric continuum) with no local cut points. That is, for every
connected open `W` and every `p ∈ W`, the set `W ∖ {p}` is connected. Then `X ∖ C` is connected for every countable
closed `C ⊆ X`.

## Proof

- **Setup.** Suppose `X ∖ C = U ⊔ V` with `U`, `V` nonempty and open.
- **`X = cl U ∪ cl V`.** A point of `C` outside `cl U ∪ cl V` would have an open neighbourhood inside `C`. That is
  impossible: nonempty open sets of a nondegenerate Peano continuum contain nondegenerate connected open sets, so
  they are uncountable.
- **The common boundary.** Since `X` is connected, `K = cl U ∩ cl V` is nonempty. It is contained in `C`, so it is
  a countable compact set, and it has an isolated point `p` (Baire).
- **The neighbourhood.** Choose a connected open `W ∋ p` with `W ∩ K = {p}`, using local connectedness.
- **The contradiction.** `W ∖ {p} = A ⊔ B`, with `A = (W∖{p}) ∩ cl U` and `B = (W∖{p}) ∩ cl V`.
  - Both are relatively closed.
  - They are disjoint, since `W ∩ K = {p}`.
  - They cover `W ∖ {p}`, since `X = cl U ∪ cl V`.
  - Both are nonempty, since `p ∈ cl U ∩ cl V` and `W` is open.

  So `W ∖ {p}` is disconnected, and `p` is a local cut point, a contradiction. ∎

## Application to hyperbolic groups

- **Input.** For a one-ended hyperbolic `Γ`, `∂Γ` is a Peano continuum (Bestvina–Mess; Bowditch; Swarup).
- **Local cut points.** By Bowditch, `∂Γ` has a local cut point iff `Γ` splits over a two-ended subgroup or is
  virtually Fuchsian (recalled).
- **Kazhdan groups.** An infinite Kazhdan hyperbolic group has property (FA), so it has no splitting at all. It is
  one-ended, and it is not virtually Fuchsian. So `∂Γ` has no local cut points, and the Lemma applies.
- **Random groups.** Random groups at density `< 1/2` do not split (Dahmani–Guirardel–Przytycki). Their Menger
  boundary has no local cut points.

**Consequence.** For all these groups, (T0) of `busemann-frontiers-separate-the-boundary` holds. So every
loxodromic `g` has an **uncountable shear frontier `F`**, for `k` large.

**The only remaining step toward "BBMZ hosts of Kazhdan hyperbolic groups are unbounded" (Conjecture U)** is
persistence: that `g` is singular over the frontier. It is proved for reflections only.

## Lesson for general BH

The separation topology that decides whether germ-extension finiteness can work is exactly Bowditch's
local-cut-point topology. Groups whose boundaries have no local cut points, which include every Kazhdan hyperbolic
group, have uncountable shear frontiers. For them the bounded theory is expected to be unavailable, and no
dimension count is needed to see it.

## Referee (bh-ref-q12, 2026-09-19): Lemma PASS; application PASS with two wording repairs

**The Lemma: correct, step by step.**
- **The definition.** "Some connected open `W ∋ p` with `W ∖ {p}` disconnected" is equivalent, in a Peano continuum,
  to Bowditch's "`X ∖ {p}` has at least two ends at `p`".
  - If `W ∖ {p} = A ⊔ B`, both pieces accumulate at `p`; otherwise one would be clopen in `W`.
  - So every smaller connected neighbourhood of `p` is also cut by `p`.
- **`X = cl U ∪ cl V`.** A nonempty open subset of a nondegenerate Peano continuum contains a nondegenerate connected
  open set, so it has cardinality at least the continuum.
- **`K = cl U ∩ cl V`.** It is nonempty, since `X` is connected. It lies in `C`, since `U, V` are open and
  disjoint.
- **An isolated point.** A nonempty countable compact Hausdorff space has one (Baire).
- **The contradiction.** Local connectedness gives a connected open `W` with `W ∩ K = {p}`.
  - `A` and `B` are relatively closed, disjoint and cover `W ∖ {p}`.
  - They are nonempty because `p ∈ cl U ∩ cl V` and `p ∉ U ∪ V`.
- **Classical source.** None pinned down: two searches (09-19) and my own recollection of Whyburn's *Analytic
  Topology* and Kuratowski's *Topology II* on local separating points. The argument is short and self-contained, so
  the Lemma stands on its proof. Record it as "folklore, proof given". No priority is claimed, and none should be.
- **Scope.** The countability hypothesis is sharp in the Menger case. The Menger curve is a 1-dimensional Cantor
  manifold, and compact 0-dimensional (e.g. Cantor) subsets can separate it. So "no countable closed set" cannot be
  improved to "no 0-dimensional closed set" there. On `S^m`, `m ≥ 2`, it can.

**The application.**
- **Local connectivity: correct as recalled.** A one-ended hyperbolic group has a locally connected boundary. That
  is Bestvina–Mess (locally connected iff no global cut point), with Bowditch and Swarup (no global cut points).
- **Local cut points: correct as recalled.** For one-ended `Γ` with `∂Γ` not a circle, `∂Γ` has a local cut point
  iff `Γ` splits over a two-ended subgroup (Bowditch, *Cut points and canonical splittings of hyperbolic groups*,
  Acta Math. 180 (1998)). A circle boundary means virtually Fuchsian (Tukia, Gabai, Casson–Jungreis).
- **Kazhdan groups: correct.**
  - (T) ⇒ (FA) (Watatani). So `Γ` has no splitting over finite groups, and is one-ended by Stallings.
  - An infinite hyperbolic Kazhdan group is non-elementary, since virtually cyclic infinite groups lack (T).
  - Virtually Fuchsian groups have finite-index subgroups with infinite abelianization, so they are not Kazhdan.
  - No splitting over two-ended subgroups follows from (FA).
- **Random groups.** Dahmani–Guirardel–Przytycki (*Random groups do not split*, Math. Ann. 2011): at density
  `< 1/2`, with overwhelming probability, a random group is hyperbolic, one-ended, has (FA), and has Menger-curve
  boundary.
  - **Repair 1.** Say "with overwhelming probability", not "every random group", in the title and the text.
- **The frontier `F` is closed.** It is a finite union of intersections of the closed sets `R_σ`, which are images
  of clopen sets under the closed map `φ`. So the Lemma applies to it. Theorem 1 of
  `busemann-frontiers-separate-the-boundary` was not re-reviewed here.
- **Repair 2.** "Conjecture U now rests only on persistence" is right for the topological input. Conjecture U is
  "unbounded", i.e. `sing(g)` is infinite, and that also needs Theorem 1 of the frontier node, which is unreviewed.

**Verdict: PASS**, with the two wording repairs. The Lemma is a folklore-level fact with a correct proof; no
classical citation was found.
