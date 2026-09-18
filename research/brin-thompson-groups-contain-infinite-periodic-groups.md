---
rg: 2
id: brin-thompson-groups-contain-infinite-periodic-groups
kind: claim
title: For some n ≥ 2, the Brin–Thompson group nV contains an infinite finitely generated periodic group
distinct_from:
  almost-automorphism-torsion-subgroups-are-rf: that excludes infinite finite-exponent groups from V, V_d and Röver–Nekrashevych groups, and makes their finitely generated torsion subgroups residually finite; this asks whether nV for n ≥ 2 is torsion locally finite, where the pumping argument fails.
  brin-thompson-torsion-has-clopen-fixed-sets: that proves the germ, dihedral-freeness and finiteness-criterion constraints that any periodic subgroup of nV must satisfy; this is the existence question itself.
  fp-simple-groups-can-contain-infinite-finite-exponent-groups: that asks for BOUNDED exponent in some finitely presented simple group; this asks for unbounded-exponent periodic groups in the specific finitely presented simple groups nV, a necessary first step for nV as a Burnside host.
---

**OPEN.** There are `n ≥ 2` and an infinite finitely generated periodic subgroup of Brin's `nV`.

## Why it matters

- `V = 1V` is torsion locally finite (Röver, J. Algebra 220 (1999); stated as Theorem 1.3 of
  Burillo–Cleary–Röver, arXiv:1402.3860v2, TeX read on MSI 2026-09-18). A positive answer here would
  separate `nV`, `n ≥ 2`, from `V` in this respect.
- `nV` is simple and finitely presented (Brin), so it is one of the few remaining natural hosts for
  `free-burnside-groups-satisfy-boone-higman` (`almost-automorphism-torsion-subgroups-are-rf` closes the
  one-dimensional Thompson-type hosts). A negative answer (nV torsion locally finite) would close these
  too, and `brin-thompson-torsion-has-clopen-fixed-sets` item 4 says exactly what it would take.
- A Sheng preprint (arXiv:2209.11982) claimed torsion obstructions for `nV` "similar to V"; it was
  withdrawn ("a flaw in one of the proofs"), so no result is imported from it.
- Kojima–Sheng, arXiv:2603.18410v3 (current, 23 May 2026), Theorem 1.1, claims the negative answer:
  "nV is torsion locally finite for n ≥ 1". Its proof rests on the two-generator criterion
  `Cor:TwoGenerator`, which is false already in `V`
  (`kojima-sheng-two-generator-torsion-criterion-fails-in-v`). So nothing is imported from it and the
  question stays OPEN (lane bh-free-50, 2026-09-18).

## Constraints already proved

By `brin-thompson-torsion-has-clopen-fixed-sets`, a periodic `H ≤ nV` acts with trivial germs at fixed
points, its level cocycle is an orbitwise coboundary, and no dihedral subgroup of `nV` acts minimally
and non-freely. So Nekrashevych's fragmentations (arXiv:1601.01033) cannot be built from a dihedral
subgroup of `nV` directly; a periodic group can only enter `nV` in a "germ-resolved" form.

## Route

`nv-periodic-groups-via-schreier-subshift-factors`: it suffices that some element of `nV` factors, on a
clopen invariant set, onto an infinite minimal subshift whose topological full group contains an
infinite finitely generated periodic group, for example a Grigorchuk subshift (Matte Bon,
arXiv:1408.0762, abstract: "every Grigorchuk group G_ω embeds in (the commutator subgroup of) the
topological full group of a minimal subshift").

## Attempts

1. **Attempt 1 (2026-09-18, bh-free-01).** Direct dihedral route: dead by item 3 of
   `brin-thompson-torsion-has-clopen-fixed-sets`. Factor route: open. For the first Grigorchuk group, the subshift is a
   Toeplitz subshift over the 2-adic odometer, and its letter at time `k` is a function of the 2-adic
   valuation of the phase modulo 3 (the period of its defining sequence). So the factor map requires an element of `nV` that factors onto the
   2-adic odometer and makes "valuation mod 3" locally readable, including along the singular fiber.
   Two observations recorded, no construction:
   - The binary hierarchy is exactly where `bs12-embeds-in-brin-thompson-2v` stalls (hidden carry
     sweeps, 30841be4c). SMART's hierarchy is ternary (`smart-level-zero-return-map-factors-onto-3-adic-odometer`),
     so the ternary analogue is the natural first target. Nekrashevych's Theorem 1.1 applies to the
     dihedral action `a(x) = -x`, `b(x) = 1 - x` on `Z_3` (fixed point `0`, fragment `a` over three
     families of annuli `3^k Z_3 \ 3^(k+1) Z_3` with the group `{000, 110, 101, 011}`), giving a periodic
     group whose orbital graphs are lines. Its Schreier subshift is a Toeplitz subshift over the 3-adic
     odometer. That its topological full group contains the periodic group is expected by Matte Bon's
     method but is not proved here.
   - The remaining gap is then a machine-design problem: an element of `nV` factoring onto that ternary
     Toeplitz subshift, with the fragmentation piece index locally readable. Periodicity of the lift is
     automatic by `aperiodic-full-groups-lift-along-factor-maps` (the lift is an isomorphism onto its
     image), so no control of garbage configurations beyond the factor map is needed.
2. **Attempt 2 (2026-09-18, bh-free-01): the factor route reduced to a single-element property, and SMART
   ruled out.**
   - `graded-renormalization-gives-ternary-toeplitz-factor` (ESTABLISHED, lane proof): a height-3
     self-renormalization `Ψ` of `g` that cycles a clopen 3-colouring gives a factor onto the ternary
     valuation Toeplitz subshift, hence (route `nv-periodic-groups-via-graded-renormalization`) Nekrashevych's
     ternary fragmentation in `nV`. `Ψ` need not be brick-local. Its Lemma A: any Toeplitz factor forces a
     non-open odometer factor at the holes.
   - `smart-renormalization-admits-no-graded-basins` (ESTABLISHED, lane proof): SMART's landed renormalization
     and all its finite skew-product lifts have no such colouring (the zero-insertion attractor is approached
     from all depth classes).
   - Open input: `some-nv-element-has-a-graded-height-3-renormalization`. Handed to bh-free-50.
