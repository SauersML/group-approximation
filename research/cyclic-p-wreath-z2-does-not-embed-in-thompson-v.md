---
rg: 2
id: cyclic-p-wreath-z2-does-not-embed-in-thompson-v
kind: claim
title: "For a prime p, the lamplighter C_p ≀ Z^2 is not a subgroup of Thompson's group V"
distinct_from:
  wreath-z-by-z2-does-not-embed-in-thompson-v: that is Corwin's theorem for the torsion-free base Z; this claim has the finite base C_p, and Corwin's argument is not available in the repo (the thesis PDF returned 403)
  z2-free-z-does-not-embed-in-thompson-v: that is about Z^2 * Z; this is a metabelian group with torsion lamps
---

**OPEN.**

**Claim.** Let `p` be a prime. The restricted wreath product `C_p ≀ Z^2` is isomorphic to no
subgroup of `V`.

**Why it matters.**
- By `upper-triangular-cloning-groups-contain-lamp-wreath-z2`, `C_p ≀ Z^2 ≤ T(B_*(F_q))` for
  `q = p^e`.
- So this claim would settle the Witzel–Zaremsky upper-triangular systems over finite fields for the
  `V`-embedding half of Zaremsky Problem 2.16, through the route
  `finite-field-upper-triangular-cloning-not-in-v-via-lamplighter`.
- Conversely, if `C_p ≀ Z^2` embeds in `V`, then no subgroup obstruction of this kind is available for
  `T(B_*(F_q))`.

## Attempts

- 2026-09-17 (swarm-0917-w5-pull-z-1). These are not a proof.
  - *Hyperbolic–Schwarz–Zaremsky input.* By HSZ Corollary 1.7, every `Z^2 ≤ V` has a nontrivial
    element fixing any given point of the Cantor set. This does not by itself stop the lamps
    from moving freely.
  - *Demonstrative subgroups.* A demonstrative `Z^2` cannot occur, because by BFGHM the only
    finitely generated demonstrative subgroups of `V` are virtually cyclic. So the usual
    construction of `A ≀ Q` in `V` is not available. Some other construction would still be
    needed to rule out an embedding.
  - *Corwin's method.* Corwin's method for `Z ≀ Z^2` was not read, since the thesis PDF returned 403.
    It is unknown whether it uses torsion-freeness of the base.
  - *Period growth.* Period growth gives nothing, because the element orders in `C_p ≀ Z^2` are
    bounded by `p`.
