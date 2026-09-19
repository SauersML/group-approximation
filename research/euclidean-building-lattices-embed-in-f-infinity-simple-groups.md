---
rg: 2
id: euclidean-building-lattices-embed-in-f-infinity-simple-groups
kind: claim
title: Every discrete cocompact group of automorphisms of a locally finite thick irreducible Euclidean building of dimension at least 2, of any type, embeds in a simple group of type F_infinity, with no loops, rescaling or promise moves; this covers the Kazhdan non-residually-finite C̃₂ lattices
distinct_from:
  euclidean-building-lattices-lie-in-permutational-bh-class: that puts these lattices in B_A through Li's thm:deg after rescaling to two loops per colour and a skew product; this uses the unrescaled box category, gets finiteness from the Cuntz factor, and gets a simple F_infinity host directly.
  a2-lattices-embed-in-fp-simple-groups: that is the Ã₂ case, proved through primitive two-graphs and link arguments; this is every type, through the general host theorem.
  cubulated-groups-embed-in-f-infinity-simple-groups: that is the cubical application of the same host theorem, which needs promise moves (flags); here the coding resynchronizes without them.
---

**ESTABLISHED** through `euclidean-building-lattices-f-infinity-simple-host-proof` (lane proof,
not independently reviewed; no priority claimed). It inherits:
- the trust caveat on Ciobotaru–Le Bars (arXiv:2601.13092, unrefereed; minimality and
  topological freeness), from `euclidean-building-lattices-lie-in-permutational-bh-class`;
- the pending referee pass of the finite-unit Cuntz theorem in
  `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups`.

## Statement

Let `X` be a locally finite, thick, irreducible Euclidean building of dimension at least 2, and
`Γ ≤ Aut(X)` discrete and cocompact (torsion allowed). Then `Γ` embeds in a simple group `S` of
type `F_∞`. Every group commensurable with `Γ` also embeds in `S`.

**New cases.** The Ã₂ case is already on main (`a2-lattices-embed-in-fp-simple-groups`). New are
simple `F_∞` hosts for:
- exotic C̃₂ and G̃₂ lattices (Kantor, Essert, and the chamber-regular lattices of
  arXiv:2511.08312);
- the non-residually-finite Kazhdan C̃₂ lattices of Titz Mite–Witzel;
- all higher-rank types, uniformly.

Before this node these were known to lie in `B_A`, which gives finitely presented simple hosts.
Simple `F_∞` hosts had not been recorded for them.

## How the four conditions are met

The host is `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups` applied to the box
orbit category `ℭ_Γ` of `euclidean-building-lattices-lie-in-permutational-bh-class` (Step 1
there), **without** its rescaling Steps 3–4.

| Condition | Source |
|---|---|
| (C1) Li-Garside, finite units | `N^r`-degree category with (UFP*): cubes of degrees `{0,1}^r` form the Garside family, and the units are the tile stabilizers |
| (C2) resynchronization | parallel sectors share a subsector (Step 2 there). Chambers at infinity are generic, so no promise moves are needed |
| (C3) (Acyc) | **shadows shrink**: the uniform box measure gives the cylinder of a degree-`km` loop measure at most `2^{−k|m|}` |
| (C4) minimal, effective, Hausdorff | Ciobotaru–Le Bars (minimality, topological freeness), with right cancellation for Hausdorffness |

## Lesson for general BH

The cube-complex lesson "Kazhdan inputs need non-median codings with promise moves" is only
half right.
- **Non-median: yes.** The building's box category is a degree category. It has disjoint
  mcms but no joins, and that is all Li needs.
- **Promise moves: not for buildings.** A coding needs promises only when its boundary has
  non-generic points in the closure of generic ones: Roller points running beside a wall.
  Chambers at infinity form a closed space of generic points, and sector codings from two
  base points resynchronize after a common subsector.

So the rule is: **code the closed generic boundary if the geometry has one (buildings: the
chambers at infinity); add promises only when the natural boundary is not closed (cube
complexes: the Roller boundary).** In both cases the Cuntz factor removes every loop,
rescaling and phase condition from the finiteness side. What remains is minimality plus the
measure-theoretic fact that shadows shrink.
