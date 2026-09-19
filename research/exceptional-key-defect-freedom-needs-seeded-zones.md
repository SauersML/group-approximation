---
rg: 2
id: exceptional-key-defect-freedom-needs-seeded-zones
kind: claim
title: Profile E for aligned plane lifts needs head-seeded computation zones, since unseeded irreversible zones free every plane at infinite level; with seeded zones a single freedom bit keyed to one input orbit gives clustered, Z^2-unbounded, relatively rigid freedom, and the aligned case reduces to whether that design is minimal
distinct_from:
  aligned-plane-lifts-share-infinite-level-degeneracy: that reduces the aligned conjecture to realizability of profile E; this runs the deciding test as far as it goes. It kills the unseeded designs, gives a candidate realization, and isolates the one remaining question (minimality of the candidate, or a size theorem for floating loci).
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `aligned-plane-lifts-share-infinite-level-degeneracy`, `plane-local-freedom-kills-rigidity-of-plane-lifts`.

**Status.**
- Part 1 is ESTABLISHED: a kill, lane proof, unreviewed. It is design-level in one item,
  marked.
- Parts 2 and 3 are a design-level candidate construction, not proved.
- Part 4 is OPEN.
- The aligned case is **not decided** by this pass.

Terms and setting are those of `aligned-plane-lifts-share-infinite-level-degeneracy`: an
aligned (`Λ_0`-constant skeleton), DR-regular, minimal plane lift `X` of a non-SFT minimal free
`Y`, with plane-local floating data.

## Part 1. Unseeded zones kill profile E

An *infinite zone* is a computation zone of a macrotile of infinite level, at a degenerate
skeleton point. It has no bottom row: its space-time diagram is any bi-infinite trajectory
permitted by the local rules.

**Proposition 1.** Suppose that, at some degenerate skeleton point `σ` and for every input
`y`, the infinite zone of *every* plane admits at least two contents. Then `X` is not
`D`-rigid for any `D`.

*Proof.* Every plane is free at `(σ, y)`, so two free planes lie at distance `> 2D`. Theorem 1
of `plane-local-freedom-kills-rigidity-of-plane-lifts` applies. ∎

**When the hypothesis holds (design-level).** It holds whenever the zone machine can start
anywhere. In an unseeded zone, the head and the tape at any time are constrained only by the
local rules.
- An irreversible machine has configurations with several predecessors, and these give
  several pasts.
- Even a reversible machine leaves the configuration at time `0` free, since no input row
  fixes it.
- This freedom does not depend on the plane's table. It is the "irreversible machine is
  ambiguous toward the past" clash of
  `cross-layer-separable-modifications-kill-quantum-rigidity`, now **across planes**.

**Requirement (R1): seeded zones.**
- The head enters a zone only through a seed tile at the zone's own corner, which is fixed by
  the skeleton.
- A zone without a corner therefore contains no head. Its tape is static and consists of wire
  copies of the zone's inputs, which are determined by the skeleton and tables.
- So infinite zones become determined. Finite zones keep their seeded, deterministic
  computation, as in (L4) of the crossing-wire layout.
- Head-free regions also occur inside large finite zones, since computation takes time
  `poly log N_k ≪ N_k`. So (R1) should not by itself obstruct minimality (not checked).

## Part 2. With seeded zones, all remaining freedom must be designed in

Under (R1), DR-regularity and determined tables, every datum at infinite chains is a function
of the skeleton and the letters, except for what the design deliberately leaves free.

Theorem 3(iii) of `strongly-proximal-geometries-are-disjoint-from-measured-inputs` then
*forbids* leaving nothing free. So some deliberate freedom is required, and profile E asks for
it to be clustered.

## Part 3. A candidate: one freedom bit keyed to one input orbit (design-level)

**Data.**
- Fix a point `y* ∈ Y` and let `Q_k(T)` mean "the level-`k` table `T` equals `y*|_{F_k}`".
  These are clopen conditions, nested, and they decrease to `{y*}`.
- Each level-`k` identity on the chain carries one extra bit `b_k`.

**Rules (local).**
- If `¬Q_k(T_k)`, then `b_k = 0`.
- If `Q_k(T_k)` and `Q_{k+1}(T_{k+1})`, then `b_k = b_{k+1}`, by father–child delegation.
- If `Q_k(T_k)` and `¬Q_{k+1}(T_{k+1})`, then `b_k = 0`.
- At a finite chain, the top identity sets `b_J` from its position. Keyed slots of level `J`
  may display `b_J = 1` exactly at the key `y*|_{F_J}`, using a map `i` that singles out one
  key. That is legal because keys are distinct inside windows.

**What it gives (sketch).**
- **Freedom only on one orbit.** Along an infinite chain in plane `λ`, the bits at large
  levels are all equal. They are free (0 or 1) iff `Q_k(T^λ_k)` holds for all large `k`, i.e.
  iff `λ^{-1}·y = y*`. Otherwise they are forced to `0`.
- **At most one free plane.** For each `y`, the free planes are `{λ : λ^{-1}y = y*}`. `Y` is
  free, so this set has at most one element: the freedom is clustered.
- **Unbounded in `Z^2`.** The bit is carried by identities of every level along the chain, so
  the modification is infinite. The finite-modification kill therefore does not apply.
- **Relatively rigid.** At the defect, the fibre is one bit, copied between levels by exact
  delegation identities. So a relative family is a single projection, and it commutes.
- **Theorem 3(iii) is respected.** `(τ, φ)` fails to be injective exactly over
  (degenerate skeletons) x `Λ_0·y*`. Theorem 3 needs injectivity everywhere, so it does not
  apply.
- **Minimality, where the sketch could fail.** Every finite-level shadow of a free chain with
  bit `1` must occur at finite chains. The singleton-key slots provide these shadows at the
  syndetic planes with key `y*|_{F_k}`, which is consistent with the `b = b_{k+1}` rule. What is
  not checked is that no *other* pattern is created that fails to recur, for example at the
  boundary between the defect plane's chain and its neighbours.

## Part 4. What decides the aligned case (OPEN)

Either answer settles it:
- **(A) Realization.** Carry out Part 3 inside a crossing-wire keyed-slot lift with (R1), and
  prove minimality. With Theorems A and B of `e2-for-plane-lifts-is-clustered-floating-freedom`
  and the one-bit defect, this would give a minimal, rigid aligned lift. That would **refute**
  the conjecture of bh-g1-simulation.
- **(B) A size theorem for floating loci.** Show that for a minimal SFT plane lift the
  non-injectivity locus of `(τ, φ)` cannot project to a single `Λ_0`-orbit of `Y`. It would
  then have to meet far planes, and the conjecture would follow for aligned lifts.
  - *Attempted here, not obtained.* The natural route is to show that the continuous inverse of
    `(τ, φ)`, defined off the locus, is uniformly continuous, so that it extends to a section
    and Theorem 3 applies.
  - It fails precisely because the single fibre over `y*` is a limit of different fibre points
    along different sequences. So a small locus is not excluded by this method.

## Lesson for general BH

In aligned lifts, freedom has two sources, and only one of them is under the designer's
control.
- **Unseeded zones** make every plane free at infinite level, and that kills rigidity outright.
  So E2-compatible designs must *seed* their computations at the skeleton's corners.
- **Designed freedom.** Once zones are seeded, all freedom is designed in, and Theorem 3(iii)
  only asks that *some* exist. One bit keyed to one input orbit is the smallest candidate.
  Whether so small a floating locus is compatible with minimality is the single question that
  now decides whether the aligned `Z^2` route can pass E2.
