---
rg: 2
id: f-infinity-groups-of-finite-cd-are-of-type-f
kind: claim
title: "Every group of type F_infinity with finite cohomological dimension is of type F"
---

If `G` is of type `F_∞` and `cd G < ∞`, then `G` has a finite `K(G,1)`.

Equivalent forms:

- every finitely presented group of type FP is of type FL;
- `σ(G) = 0 ∈ K̃_0(ZG)` for every finitely presented group of type FP
  (`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`);
- every finitely dominated aspherical CW complex is homotopy equivalent to a
  finite complex (Wall's criterion for finite domination).

It follows from Conjecture 1.3 of Lück–Reich (arXiv:math/0402405) by
`f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`.

## Attempts

- **Farrell–Jones classes.** Proved whenever `K̃_0(ZG) = 0`, which covers
  hyperbolic, virtually solvable, lattice and mapping-class-group examples and
  the closure of these classes (see
  `f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`). In general it
  dies: vanishing of `K̃_0(ZG)` for all torsion-free `G` is open. Only the single
  class `σ(G)` has to vanish, but no mechanism specific to that class is known.
- **Detecting factors.** By `g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class`,
  a type-F factor `H` with `χ(H) = ±1` detects `σ(G)`, e.g. `G × F_2` of type F
  forces `G` of type F. It dies here because `χ(Z) = 0`, so the factor `Z` in
  Problem 1.21 detects nothing.
- **Mather trick and splitting.** For a finitely dominated `K(G,1)` `X`, the
  product `X × S^1` is homotopy finite (Ferry–Ranicki, arXiv:math/0008070,
  Proposition 1.5, read 2026-09-13). Getting a finite `K(G,1)` back from a finite
  `K(G × Z, 1)` means splitting off the circle factor. As recalled, not
  re-derived, the fibering and splitting obstructions of Farrell and Siebenmann
  have a `K̃_0(ZG)` component equal to the Wall class of the infinite cyclic
  cover, which is `σ(G)`. The approach is circular.
- **Finite-index subgroups.** Restriction sends `σ(G)` to `σ(G')` for `G'` of finite
  index, but restriction on `K̃_0` need not be injective, so vanishing on `G'`
  proves nothing about `G`.
- Affirmative lanes: z1-21-type-f-proof (algebra), z4-06-rips-finf-fcd (Rips
  complexes: a contractible Rips complex gives type F for torsion-free groups).
