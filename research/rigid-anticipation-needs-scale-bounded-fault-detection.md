---
rg: 2
id: rigid-anticipation-needs-scale-bounded-fault-detection
kind: claim
title: A quantum rigid anticipation layer forces long walks to be isolated at every scale; for walks that run a reversible machine this means every cell at a fixed offset from the head is revisited within bounded time, so the raw halting rung is not rigid and a rigid one needs fault detection at every scale
requires:
  - anticipation-layers-convert-totality-into-isolation
  - seed-full-group-finite-presentation-lives-on-the-boundary
distinct_from:
  anticipation-layers-convert-totality-into-isolation: that proves any two non-terminating basins of a rigid layer are within 2D in every configuration (item 5); this turns that statement about limit configurations into a uniform condition on the walks of the seed itself, and reads it off for walks that run a machine.
  seed-full-group-finite-presentation-lives-on-the-boundary: that puts the rigidity requirement on the boundary; this says which halting-rung designs can meet it there.
---

**ESTABLISHED** (lane proof, bh-invent-11, 2026-09-18; elementary compactness; not reviewed). This
is the lane's answer to "do the unforced tails of the halting rung's backward walks form a rigid
SFT?": **not for the raw rung**. The design constraint below is handed to the gate-4 coupling
layer (bh-free-56, bh-star-a). No second coupling layer is proposed here.

## Setting

As in `anticipation-layers-convert-totality-into-isolation`:
- `A` is a finitely generated group;
- `Y_0 ⊆ Σ^A` is an SFT;
- the step rule `σ` has radius `r`, and the terminal type is `θ`;
- `Y = Y_0 ⋉_(σ,θ) T` is the anticipation layer.

Assume the step map is **injective** in every `y ∈ Y_0`: distinct non-terminal sites have
distinct successors. This holds for reversible machines, and for history-keeping Bennett
machines. Then basins are orbit **chains**: a site, its successors, and its (unique)
predecessors. Two chains are **`δ`-separated** if every site of one is at distance `> δ` from every
site of the other.

## Theorem

1. **Separated chains.** Suppose `Y` is `D`-quantum rigid over some field. Then:
   - no `y ∈ Y_0` has two forward-non-terminating chains that are `2D`-separated;
   - equivalently, by compactness, for every `d` there is `L(d)` with the following property. In
     every `y ∈ Y_0`, whenever `q, q'` satisfy `dist(q, q') <= d` and their chain segments of
     `L(d)` steps in both directions are defined, then these two segments are not both
     non-terminating and mutually `2D`-separated.
2. **Machine walks must sweep (SW).** Suppose in addition that the walk runs a reversible machine
   and that there are edits with the following property:
   - (b) For a site `q` carrying a configuration and `k >= 1`, the site `q e_k`, with
     `|e_k| <= c·k`, carries the same configuration with the tape cell at offset `k` from the head
     changed.
   - (b′) Two sites whose configurations differ in a cell at distance `>= j` from both heads are at
     distance `>= c'·j`.
   - (b″) The walk from `q e_k` copies the walk from `q` for as long as the latter keeps its head
     at distance `>= k/2` from the edited cell.

   Take `k` with `c'·k/2 > 2D`. Then there is `L_k` such that every run of the seed avoiding the
   `k/2`-neighbourhood of a fixed cell, both forward and backward, for `L_k` steps around some time,
   terminates within those steps.
3. **The raw halting rung fails (SW).** Take the rung of bh-invent-03: walks are machine runs
   along stable-letter edges, and tape-letter edges give the edits. Hardness requires unbounded run
   lengths. Suppose the machine extends its workspace by sweeps of growing width, as ordinary
   deciders do. At a turnaround on the frontier, the cell at offset `k` beyond it is not
   approached within `k/2` for a whole sweep before and after. As widths grow, this holds for every
   `k`. So (SW) fails at every `k`, and `Y` is not `D`-quantum rigid for any `D`.
4. **Hard inputs must be sparse.** Consider two valid inputs that differ in one cell at distance
   `j` with `c'·j > 2D`, and whose runs keep their heads away from that cell. If both run
   arbitrarily long, rigidity fails, by (1) and (b′).

## Proof

**(1).** Item 5 of the anticipation theorem says any two non-terminating basins of a
configuration in a rigid layer come within `2D`. With injective steps, basins are chains, which
gives the first form. For the second form:
- Suppose it fails at `d`. There are `y_i, q_i, q'_i` whose segments of `i` steps in both
  directions are non-terminating and mutually `2D`-separated.
- Translate `q_i` to `1`, fix the offset `h = q_i^(-1)q'_i` along a subsequence, and pass to a
  limit `y ∈ Y_0`.
- The chain segment of `j` steps through a site, its non-termination and its separation from
  another segment are read on a finite ball. Predecessors are found among neighbours by the local
  step rule. So these are clopen conditions, and they hold in `y` for every `j`.
- So `y` has two forward-non-terminating chains that are `2D`-separated, which contradicts the
  first form. ∎

**(2).** Suppose (SW) fails at `k`: for arbitrarily large `L`, some run keeps its head at distance
`>= k/2` from a cell for `L` steps on both sides of a time `t`, and does not terminate there.
- *The copy.* Edit that cell at the site `q_t`. By (b″), the two chain segments are copies for
  those `L` steps, so neither terminates.
- *Separation.* Every configuration on either segment has its head at distance `>= k/2` from the
  edited cell, and the two segments disagree there. So by (b′) they are `c'·k/2`-separated, and
  `c'·k/2 > 2D`.
- *Initial offset.* `dist(q_t, q_t e_k) <= c·k`.
- *Conclusion.* This contradicts (1) with `d = c·k`. ∎

**(3)** and **(4)** are instances of (2) and of (1) with (b′). ∎

## What a rigid halting rung must contain (target for the coupling layer)

- **Sparse hard inputs.** Long runs must come from inputs that are isolated at every scale, by (4).
  Unary or padded hard languages keep full time-hierarchy hardness.
- **Scale-bounded fault detection.** By (2), within time `L_k` the head must revisit every cell at
  offset `k`. Together with (1), any edit at offset `k` must also end the edited walk within
  bounded time `f(k)`.
  - This is the defining property of hierarchical self-checking computation: Gács-type reliable
    automata, or the fixed-point tilings of Durand–Romashchenko–Shen, which the master route
    already names for E2.
  - Sweeps of growing width, the usual deciders, are excluded.
- **Uniqueness of the carrier.** An SFT cannot count carriers, so the carrier of the long runs must
  be pinned by ordered fields or Bass–Serre pointers.

## Lesson for general BH

**Rigidity turns into a dynamical condition.** On an anticipation seed, rigidity becomes one
uniform condition on the seed's own walks: long walks must be isolated at every scale. For
machine walks this means detecting faults at every scale within bounded time.
- **What it rules out.** The raw halting rung, with ordinary deciders, has a non-rigid boundary.
- **What it points to.** Lemma CB is now a concrete design target for the coupling layer: sparse
  hard inputs plus Gács/DRS-type self-checking. That is the same hierarchical self-simulation that
  the master route's E2 already needs. So SEED's CAP-false direction and the master route's
  rigidity gate share one missing object: a rigid self-checking computation.
