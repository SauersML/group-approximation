---
rg: 2
id: hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity
kind: claim
title: For every hyperbolic post-critically finite rational map f, and more generally every expanding partial self-covering of a compact space with type F_infinity fundamental group, the Nekrashevych group V_f = V_d(IMG f) has type F_infinity
distinct_from:
  wreath-recursion-thompson-groups-inherit-fn: that is the general transfer theorem; this is its application to iterated monodromy groups, where the cover is the fundamental group.
  contracting-rover-nekrashevych-groups-are-f-infinity: that asks for all contracting G; this settles the IMG subclass that Nekrashevych singled out (arXiv:1312.5654, TeX l.171–175), whatever the activity growth.
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that needs polynomial activity; this needs none.
---

**ESTABLISHED** (lane proof `bh-free-06`; it applies `wreath-recursion-thompson-groups-inherit-fn`
to imports read at source; not independently reviewed). No priority claimed. Not found in
Belk–Hyde–Matucci arXiv:2407.03149 (bounded automata only), Skipper–Zaremsky arXiv:1709.06524, or
Li arXiv:2110.04505.

## Statement

1. Let `f : M_1 → M` be an expanding partial self-covering of degree `d`, where `M` is compact,
   path-connected and semi-locally simply connected, and `M_1 ⊆ M`. If `π_1(M)` has type `F_n`,
   then `V_f ≅ V_{d}(IMG f)` has type `F_n`, and so has every `V_{d,r}(IMG f)`.
2. In particular, let `f` be a **hyperbolic post-critically finite rational function**, meaning
   that every cycle in `P_f` contains a critical point. Then `V_f` has type `F_∞`.

## Proof

1. The `π_1(M)`-biset `Φ_f`, with connecting paths as transversal, is a wreath recursion
   `π_1(M) → π_1(M) ≀ S_d`. Its faithful quotient is `IMG(f)`.
   - Nekrashevych arXiv:1312.5654, Prop. `pr:expandingpi1` (TeX l.1710): "If `g ∈ π_1(M)` has
     trivial image in `IMG(f)`, then there exists `n` such that `g` acts trivially from the left
     on `Φ_f^{⊗n}`." So the kernel is `∪K_n`, i.e. the recursion has dying kernel.
   - Theorem part 2 of `wreath-recursion-thompson-groups-inherit-fn` gives type `F_n`.
   - `V_Φ ≅ V_f = V_{IMG f}` by his Corollary at TeX l.1729.
2. Nekrashevych, ibid. §"Example: Hyperbolic rational functions" (TeX l.1767 ff.), constructs the
   space. Remove disjoint open discs around the points of `P_f`, bounded by equipotentials. The
   complement `M` contains the Julia set, satisfies `f^{−1}(M) ⊂ M`, and carries a metric in which
   `f` is expanding.
   - `M` is a compact planar surface with `|P_f| >= 2` boundary circles.
   - So `π_1(M)` is free of rank `|P_f| − 1`, which has type `F_∞`. `∎`

## Scope

**New cases.**
- Belk–Hyde–Matucci cover the bounded automaton groups. These are exactly the contracting groups
  with finitely ramified limit spaces (their intro, citing Bondarenko–Nekrashevych).
- For hyperbolic PCF `f` the limit space of `IMG f` is the Julia set.
- So every hyperbolic PCF rational map whose Julia set is not finitely ramified is a new case.
  - The standard example is `f(z) = z^2 − 1/(16 z^2)`, of degree 4. Its Sierpiński-carpet Julia
    set is recalled from Devaney, not re-read.
  - Its post-critical set was checked by hand here: critical points `c` with `c^4 = −1/16` map as
    `c ↦ ±i/2 ↦ 0 ↦ ∞`, which is fixed, and `0, ∞` are critical. So `P_f = {±i/2, 0, ∞}`, the
    only cycle `{∞}` is critical, and `π_1(M) = F_3`.
- Whether `rover-nekrashevych-polynomial-activity-tower-sigma-full` also covers such maps depends
  on their activity growth, which is not checked here.

**Not covered here.**
- Sub-hyperbolic maps, with strictly preperiodic critical points. Their natural cover is an
  orbifold group, which has type `F_∞`. But the dying-kernel property needs an orbifold version of
  `pr:expandingpi1`, which was not checked. **Update (09-19):** now supplied, for every PCF rational map, by
  `pcf-rational-nekrashevych-groups-are-f-infinity` (proof claimed, OPEN until refereed).
- Expanding maps of spaces whose `π_1` is not `F_∞`.

## Lesson for general BH

**For groups of dynamical origin, the fundamental group of the phase space is the right label
group: it is F_∞ when the space is aspherical, even though the iterated monodromy group itself is
typically infinitely presented.**
- Every host construction that consumes Röver–Nekrashevych groups of IMGs inherits `F_∞` for
  free. Examples are the fp simple commutator subgroups and Boone–Higman envelopes of the
  self-similar groups of rational maps.
- The general pattern: replace a self-similar input by a nice cover with dying kernel.
