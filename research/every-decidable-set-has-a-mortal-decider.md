---
rg: 2
id: every-decidable-set-has-a-mortal-decider
kind: claim
title: Every decidable set is decided by a Turing machine that halts from every finite configuration (arbitrary state, tape and head position), by fuelled iterative deepening under a sweep discipline
distinct_from:
  modular-machine-with-noncomputable-halting: that supplies a machine whose halting set is non-computable; this supplies, for a computable set, a machine with no infinite run at all, which is what locally forced halting marks need.
  modular-machine-halting-invariance: that is invariance of halting under one step, true for every machine; this is termination from every configuration, true only for machines built for it.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-18; lane proof at the level of machine design, not
reviewed). It is presumably folklore; no priority is claimed. Background, recalled and not re-read: **Hooper** (1966)
proved the immortality problem undecidable. So mortality is not detectable in general, but it can be built in, as
here.

## Statement

Let `S ⊆ Σ*` be decidable. There is a deterministic Turing machine `D` with:
- **Mortality:** from **every** finite configuration (any state, any tape with finitely many non-blank cells, any
  head position), `D` halts after finitely many steps;
- **Correctness:** started in its initial state on input `w`, `D` halts in its accepting state iff `w ∈ S`.

## Proof

**The given decider.** Let `A` be a decider for `S`, halting from its start configuration on every `w ∈ Σ*` after
`T_A(w)` steps.

**Tracks.** `D` works on a tape with five tracks between two end markers:
- the input `w'`, never written by `D`;
- a round counter `k`;
- a fuel counter `f`;
- `A`'s work tape with one head mark;
- a status field.

**Sweep discipline.** Every state of `D` belongs to one *routine*. A routine moves the head monotonically in one
direction until it reads an end marker. It **halts rejecting** if it reads a blank or a symbol not allowed on its
track. From any configuration a routine therefore stops after finitely many steps, because the non-blank region is
finite.

**The routines.** `D`'s control graph is built from bounded routines:
- (V) validate the format: two end markers, well-formed binary counters, exactly one head mark;
- (C) copy `w'` onto the work track, place `A`'s head, and set `f := k`;
- (S) simulate one step of `A` and decrement `f`;
- (I) increment `k`.

**The program.** Start with (V) and `k := 0`. Then loop:
- **outer loop:** (I), then (C);
- **inner loop:** repeat (S) while `f > 0` and `A` has not halted;
- if `A` halted, halt with `A`'s answer; otherwise return to the outer loop.

From the initial state on `w`, `D` runs `A` on `w` with fuel `1, 2, 3, …`. So it answers exactly as `A` does, after
round `T_A(w)`.

**Mortality.** Start from an arbitrary finite configuration.
- The current routine stops, or `D` halts.
- **Inner loop.** Each pass decreases the finite fuel `f`, or `D` halts on a malformed track. So the inner loop runs
  finitely often.
- **Outer loop.** `D` never writes `w'`, and (V) has validated it, so `w'` is a genuine input word. Each round
  restarts `A` cleanly on `w'`, with fuel equal to the current `k`, and `k` strictly increases. So once
  `k ≥ T_A(w')`, `A` halts inside the round. This holds whatever finite value `k` started with.
- **Garbage never runs `A`.** The only runs of `A` are from its start configuration on a genuine input. Arbitrary
  work-track contents are only ever advanced under finite fuel. ∎

## Use: locally forced halting marks

**The coding.** In a relative-seed coding of a machine group, a *halting mark* `z(p) ∈ {0, 1}` sits on every
configuration `p`.
- It is transported exactly along steps: `z(p) = z(step p)`, via the stable-letter edges.
- It is pinned at terminal configurations: `1` at the accepting configuration, and `0` at every other stuck one.

**What forcing needs.** The mark is locally forced iff every run reaches a terminal configuration. On an infinite
run, both constant values are locally consistent. So the machine must be **mortal on all configurations**, not only
total on genuine inputs, and this lemma provides such a machine for every decidable set.

**This is where decidability of `WP(G)` enters the seed tower.** Its dual is
`relative-seeds-glue-graphs-of-groups-into-class-c`, item 3: a forced mark decides membership.

**Consequence for `aanderaa-cohen-tower-subgroups-are-decidable` (213e9e339).** For a mortal machine, the halting
set over **all** configurations is decidable: run from `p`, which terminates, and read the end state. This supplies
the open hypothesis "`H_0(M)` recursive over all configurations for a machine compiled from a decider". It needs
one condition: the modular-machine compilation must preserve mortality (next paragraph).

**What must still be checked.** The Aanderaa–Cohen / Simpson simulation of a Turing machine by a modular machine must
send mortal machines to mortal modular machines. That requires every modular configuration `(α, β)` to decode to a
Turing configuration, and every modular step to be a bounded number of Turing steps. This is recorded as a check
for the seed-tower team; see `board/seed-tower.md`.

## Scope correction (2026-09-18, after `modular-machine-mortality-at-infinity-is-uniform`, d03fdfb06)

**What mortality forces.** It forces the halting marks on the **genuine** sheet, the configurations anchored at a
seed origin. That is (S1) and nothing more.
- **Seedless limit points.** These run the `m`-adic extension of the machine. By compactness that extension
  terminates everywhere iff the running time is bounded, which is false whenever the halting set is infinite.
- **What is left free.** At infinity, exact transport plus pinned endpoints leaves one free projection per
  unterminated component.
- **What this does not settle.** Rigidity (RS3) and exact orbit closure (RS2)/(S3). They need a separate coupling
  layer (gate 4, bh-free-56 with bh-star-a).
- **A remark withdrawn.** "Rogue runs also terminate", made on the seed-tower board, is withdrawn.

## Lesson for general BH

The compactness wall between "halts" (Σ₁) and "is forced" is crossed by building termination into the machine,
not by detecting it.
- **Mortal deciders exist for every decidable set** (fuelled iterative deepening), and none exist for undecidable
  ones.
- **So rigid seeds can carry exactly the decidable membership problems,** matching the necessity that a forced
  point is a membership oracle.
- **Their natural complexity class** is that of the fuelled machine: there is no fixed cap beyond that. This is the
  positive direction of CAP's machine side.
