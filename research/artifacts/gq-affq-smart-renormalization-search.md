# SMART height-3 renormalization: a tape-deletion φ is the wrong class (lane gq-affq, 2026-09-18)

**Question.** Is there a brick-local `φ` and a clopen `A` with `U^3 = φ^{-1} U φ` on
`A = A ⊔ UA ⊔ U^2A`, where `U ∈ 2V` is SMART induced on its genuine level-0 moves
(`smart-induced-on-genuine-moves-has-exact-tripling`)? By
`renormalizable-thompson-elements-give-baumslag-solitar` such a `φ` gives `BS(1,3) ≤ 3V`.

**Answer of this note.** No bounded-radius **tape-deletion** rule works, for two independent
reasons, one structural and one measured. The renormalization, if it exists, must act in the
odometer coordinate (gq-nv-obstruct's `Z/2 × Z_3` factor), not on SMART's tape. Nothing here is
sent to referees: this refutes one class of witness and redirects, it establishes no embedding.

Compute: MSI only (`/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/`), single core, python3,
seeds fixed. SMART table from Callard–Salo arXiv:2208.00685v3 `distortion-1-smart.tex`
(transcription checked reversible in `experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py`).

## 1. What was searched

`S` is the first-return map of SMART's moving-tape map to `Y` = genuine level-0 moves. A
candidate `φ` was taken to be a **local deletion rule**: read the radius-`r` window at the head,
delete one cell at offset `j ∈ [-2,2]`, shift the head by `hs ∈ [-2,2]`, set a phase-2 shape.
Constraint propagation kept only window→edit assignments consistent with `φ(S^3 y) = S(φ(y))`,
checking configuration equality within radius `R_EQ`. Scripts: `smart_core.py`, `smart_phi.py`.

## 2. Runs

| run | radius `r` | `R_EQ` | training | result |
|---|---|---|---|---|
| phi_r2 | 2 | 40 | 600 | 204 windows, all nonempty; validation ok 3524, **bad 0**; preimages {1: 284, 0: 16} of 300 |
| phi_r3 | 3 | 40 | 1200 | 886 windows, all nonempty, but undersampled (validation stops at 150 unseen windows) |
| phi_r2_deep | 2 | 150 | 2500 | **all 216 windows collapse to the empty candidate set** |

The phase of the substitution `b→bdp, d→dbq, p→bqp, q→dpq` is readable from a radius-1 window of
the induced system: at radius ≥ 1 the phase-parse is unambiguous over thousands of windows (E1 of
`smart_renorm.py`). So the `Z/3` reading is confirmed, matching
`smart-level-zero-return-map-factors-onto-3-adic-odometer`.

## 3. Why the radius-2 "pass" is an illusion

At `R_EQ = 40` a deletion rule validates perfectly, and at `R_EQ = 150` no rule survives. The
gap is not undersampling. Deleting a `0` inside a block of `0`s is invisible **only up to the
block boundary**, because zeros are interchangeable. The zero-blocks that SMART crosses have
length equal to the level `k`, and the level of a configuration is unbounded. So the radius at
which a tape deletion keeps `φ(S^3 y) = S(φ(y))` valid grows with the level, and **no fixed
radius works**. `R_EQ = 40` sits inside the level-`k` block for the sampled high-level
configurations; `R_EQ = 150` crosses out of it. (`R_EQ = 150` also exceeds the materialised
window `W = 120`, so that single run is not by itself decisive; the structural reason in §4 is.)

## 4. The structural reason: a deletion is not brick-local

A brick-local map of `2V` changes only a bounded prefix of each Cantor coordinate. In the
conveyor-belt encoding of the moving-tape model (Callard–Salo §3.1) the two coordinates are the
tape read outward from the head, left and right. A bounded prefix change rewrites finitely many
cells near the head and leaves every other cell **fixed at its position**. A cell deletion
re-indexes every cell on one side of the head, moving infinitely many of them. So a deletion is
not a bounded prefix change, hence not brick-local, hence not an admissible `φ`. The naive
odometer renormalization `φ(0w) = w` has exactly this defect; it is why the binary odometer is
not in `V`, and the same defect appears here one dimension up.

## 5. Where the renormalization must live

The working renormalizations on main are digit operations in a counter coordinate:
`s_n^{n+1} = s_{n-1}` in `rationals-embed-in-brin-thompson-group-2v-proof` rewrites the leading
mixed-radix digits, a bounded prefix change of the second coordinate. So a height-3
renormalization of `U`, if it exists, should be sought as a bounded prefix operation on the
odometer coordinate that `smart-level-zero-return-map-factors-onto-3-adic-odometer` exhibits
(the `Z/2 × Z_3` factor), not as an edit of SMART's tape. Consuming one `3`-adic digit there is
bounded; consuming it on the tape is not. That coordinate is gq-nv-obstruct's; the split is
recorded on the boards.

## 6. Scripts

`smart_core.py` implements the 8-state table, the moving-tape step, `Y`, the first-return `S`,
and lazy random tapes. `smart_phi.py` builds the phase table, learns the deletion rule by
constraint propagation over training orbits, validates `φ(S^3 y) = S(φ(y))`, and counts
preimages. Both are in `/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/` with outputs
`phi_r2.out`, `phi_r3.out`, `phi_r2_deep.out`, `run1.out`.
