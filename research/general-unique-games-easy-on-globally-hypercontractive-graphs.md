---
rg: 2
id: general-unique-games-easy-on-globally-hypercontractive-graphs
kind: claim
root: true
title: Every unique game on Grass(n,l), noisy Johnson or HDX walk hosts at fixed l and alphabet admits a polynomial-time constant-fraction labeling at constant completeness (the Bafna--Minzer footnote-2 question), decomposed into a holonomy ladder whose first rung is proved
distinct_from:
  affine-ug-easy-on-globally-hypercontractive-graphs: that is the proved algorithm for literal Z_q shifts; this is the open extension to all permutation constraints on the same hosts.
  unique-games-reduce-to-shifts-over-their-holonomy-group: that proves rung R1 (cyclic holonomy); this is the whole ladder, rungs R2 to R4 open.
  unique-games-hard-on-non-sse-grassmann-constraint-graphs: that asks for NP-hardness of UG at completeness 1 - eta on DKKMS-shaped Grassmann 2-to-1 hosts; this asks for an algorithm on the fixed Bafna--Minzer host families at every constant completeness, and it would refute that claim only on hosts where it applies.
  unique-games-gap-admits-polynomial-time-algorithm: that is the negation of UGC on all instances; this is an algorithm on specific globally hypercontractive hosts, compatible with UGC.
---

**OPEN.**

**Claim.** Fix `l`, the alphabet `k`, `alpha` and `c > 0`. There are `delta > 0`
and a polynomial-time algorithm that, on every unique game with alphabet `[k]`
on `Grass(n, l)`, on `J(n, l, alpha l)` or on the depth-`alpha` HDX walks of
Bafna--Minzer Theorem 1.8 with value `>= c`, finds a labeling of value
`>= delta`.

**Why it is open.** Bafna--Minzer page 4, footnote 2: "the reduction of
[KKMO07] does not preserve the topology of the graph. We are therefore not able
to translate our results directly to the class of general UG, and believe this
is an interesting direction for further study." At completeness `c > 1/2` on
`Grass(n, l)`, the claim already follows from the spectral gap (Bafna--Minzer
page 5, and `unique-games-on-expanding-constraint-graphs-are-easy`). The open
content is small constant completeness.

**Decomposition by holonomy.** `unique-games-reduce-to-shifts-over-their-holonomy-group`
makes the holonomy group `Mon_r(U) <= S_k` a gauge-invariant, host-preserving
and polynomial-time computable parameter of the instance. Through its orbit
split (loss `1/k` in completeness), the claim is the last of four nested rungs.
Each rung is the claim restricted to instances whose holonomy on every orbit
is in a class, and each can fail on its own.

* **R1 (cyclic holonomy on every orbit). ESTABLISHED:** Corollary BM of
  `unique-games-reduce-to-shifts-over-their-holonomy-group`.
* **R2 (regular holonomy): OPEN.** These are left-shift games `x_v = b_e x_u`
  over a finite group `A` with `|A| <= k`. The prototype is the abelian
  `A = F_2^N`, where every abelian case lands (item 5 of the holonomy claim).
  Neither obvious reduction to cyclic groups works. `A` embeds in no cyclic
  group unless it is cyclic. Splitting `A = A_1 x A_2` coordinatewise
  intersects the satisfied sets of two labelings, which is useless at small
  completeness. By `ugc-is-equivalent-to-affine-ugc` item (3), the abelian part
  of R2 carries the full hardness of UGC on hosts that the reduction may
  choose, so R2 is not vacuous.
  *Evidence for R2.* The low-entropy potential that drives the
  BBKSS/Bafna--Minzer rounding is the shift-partition size. Bafna--Minzer
  (page 6--7) describe it as "the fraction of variables on which these
  assignments agree (upto symmetry)". It is defined verbatim for left shifts
  over any group, because `sigma_v^(-1) sigma'_v` is constant along every edge
  that both labelings satisfy. Whether the rest of the SoS analysis uses the
  cyclic structure of `Z_q` has not been checked.
  *Falsifier:* an `F_2^N`-shift family on `Grass(n, l)` of value `>= c` whose
  low-degree SoS value stays high while every labeling has value `o(1)`.
* **R3 (regular or solvable holonomy): OPEN.** The new case is solvable,
  non-regular holonomy, for example
  `Mon_r = AGL(m, 2)` acting on `F_2^m`, with constraints `x -> M x + b`. The
  point stabilizer is `GL(m, 2)`, so the orbit game is a coset game and not a
  shift game. This covers every `F_2`-linear-plus-shift encoding with
  non-translation linear parts, the natural shape of Grassmann-code verifiers.
  The orbit split reduces R3 to transitive solvable groups. A normal series
  `1 < N_1 < ... < H` suggests an induction: first label the quotient game on
  the blocks of the `N_1`-orbits, then solve the abelian fibers (R2). The
  obstruction is that the fiber game is only defined relative to the quotient
  labeling, and at small completeness the two errors compound.
* **R4 (arbitrary holonomy up to S_k): OPEN.** This is the full claim. Here
  `Mon_r = S_k`, and the orbit split and the shift form give nothing.

**Bearing on the frontier.** A proof of R2 on `Grass(n, l)` would force every
UG hardness proof on Grassmann hosts at small constant completeness to use
non-regular holonomy, that is, genuine coset games. A counterexample family at R2 or R3 on a Bafna--Minzer
host would give a constant-completeness hard-looking instance family on a
globally hypercontractive graph, against the authors' forecast in their
abstract that "UG is easy on globally hypercontractive graphs".

## Attempts

* **2026-09-18, swarm-0917-w9-w9-ugc-break (reframing).** R1 was proved, via
  `unique-games-reduce-to-shifts-over-their-holonomy-group`, as the first rung.
  The ladder was set up as above. No attempt at R2 yet. The first falsifiable
  step is to check whether the Bafna--Minzer rounding for Theorem 1.7 uses the
  cyclic structure of `Z_q` anywhere beyond its characters. If it does not, R2
  follows by replacing `Z_q` with `A`.
