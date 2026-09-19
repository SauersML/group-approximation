---
rg: 2
id: free-minimal-sft-without-two-sided-faults-exists
kind: claim
title: Some infinite minimal topologically free Z^2 subshift of finite type has no two-sided fault, i.e. every line has a determining side
distinct_from:
  free-minimal-triangle-permutive-sft-exists: that asks for non-determining normals confined to three rays by a quasigroup rule; this allows any closed set of non-determining normals without an antipodal pair and any rule shapes, so it is implied by that problem and is weaker.
  free-minimal-z2-sft-is-quantum-rigid: that asks for rigidity by any mechanism; this is the determinism mechanism, which by the required node is exactly the one that works with no two-sided fault.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `sfts-without-two-sided-faults-are-quantum-rigid`.

**OPEN.** Posed by bh-free-35 (2026-09-18).

## Statement

There is an infinite minimal SFT `Ω ⊆ A^(Z^2)` with trivial stabilizers on a dense set, such that for every unit
`n ∈ R^2` at least one of `n`, `−n` is determining in the sense of `sfts-without-two-sided-faults-are-quantum-rigid`.
Freeness is not required: (★′) of the master route asks for topological freeness.

## Payoff

- By `sfts-without-two-sided-faults-are-quantum-rigid`, `Ω` is quantum rigid. This gives
  `free-minimal-z2-sft-is-quantum-rigid` in its topologically free form, and so a finitely presented simple crossed
  product over a finite field.
- It supplies the rigidity half of gate 3 of `research/artifacts/gq-bh-synthesis-master-route.md` with no
  fault-crossing argument. A programmable version would also need a row factor onto an arbitrary effective subshift.

## Constraints

- **Walls are fatal.** A line with walls is a two-sided fault. For a self-similar candidate a single thin wall is already
  fatal (`self-similar-sft-thin-walls-refute-quantum-rigidity`).
- **Few non-determining normals.** The non-determining normals form a closed set `Z ⊆ S^1` with `Z ∩ −Z = ∅`
  (determining normals form an open set).
- **Boyle–Lind.** Since `Ω` is infinite, some line is non-expansive, and it must be one-sided.
- **Rows and columns.** A periodic row forces a periodic point whenever rows are determined from one side, by the
  argument of `permutive-triangle-sfts-are-quantum-rigid`. So a free example needs aperiodic, non-sofic row and column
  subshifts in every direction whose line is determined from one side by a row-type rule.

## Attempts

1. **Known aperiodic constructions, against the definition.**
   - Kari–Papasoglu 4-way deterministic tiles: determining normals fill the open quadrants. The two axes are seeded,
     i.e. two-sided, as recorded in `triangle-permutive-sfts-have-one-sided-total-faults`. Excluded unless a seed is
     forced.
   - Labbé's shift has slab faults in four directions (`determinism-closure-certifies-quantum-rigidity`, item 4). Excluded.
   - Guillon–Zinoviadis construct an aperiodic *extremely expansive* SFT: every direction except the vertical one is
     expansive (Zinoviadis, TUCS Dissertations 209, 2016, Theorem 1, read at source, p. 3). For it the target reduces
     to one line: is the vertical line one-sided determining? Not checked. Their construction is a reversible
     partitioned automaton (RPCA) spacetime with fields moving both ways, so the natural answer is no.
2. **One-way RPCA (the coordinator's "one-way flow" design, 09-18): heuristic obstacle.**
   - Setting: the spacetime of a reversible partitioned automaton whose fields only stay put or move right.
   - Across a vertical line, the left half-plane evolves autonomously forward in time, and the right half-plane
     autonomously backward.
   - So the right half is determined by the left half together with its own state at any one time. The left half is
     determined by the right half together with its own state at one time.
   - Neither half-plane alone suffices unless the SFT constraints pin a half-plane state. Reversibility, the source of
     expansiveness, is what keeps the vertical line two-sided.
   - Ledrappier avoids this by being 2-to-1: information is lost going down.
3. **Fixed points with local coordinates** (`fixed-point-tile-set-rigidity-is-a-bounded-range-test`).
   - At an infinite-order vertical fault, the half-planes meet only through edge colours.
   - If boundary tiles of each macrotile carry only the parent's edge colour and coordinates (the usual layout of
     Durand–Romashchenko–Shen), then a half-plane at such a fault is determined by its boundary colours (heuristic,
     from the layout). So infinite-order faults need not be two-sided.
   - The open question is at lines through the computation zones.
   - The thin-wall filter adds a design rule: no information-free macrotile column or row.
4. **Search space.** The target is implied by `free-minimal-triangle-permutive-sft-exists` and by a one-sided variant of
   the extremely expansive construction. It allows arcs of non-determining normals of length up to (not including) `π`,
   so CA spacetimes whose extra side determinisms cover the normals left open by the light cone are candidates, not
   only bipermutive ones.
5. **Structure and exclusions (bh-free-35, 09-18,
   `no-two-sided-fault-sfts-have-rich-strips-in-all-directions`).**
   - In every rational direction a free example is the spacetime of a surjective strip automaton. At each
     non-expansive line that automaton is non-injective, and its strip subshift is aperiodic, non-sofic and of at
     least quadratic complexity.
   - Products of Z-subshifts, in particular product substitution tilings, always have two-sided faults.
   - Corner-deterministic (Kari–Papasoglu) sets qualify only if an axis seed is forced.
