---
rg: 2
id: census-entry-4012-has-no-power-two-legal-folded-fatgraph
kind: claim
title: Census entry 4012 has no legal f^2-folded fatgraph over the rose for any boundary, by an exact Farkas vector for the mixed-memory relaxation (2, a2b1c1)
distinct_from:
  census-entry-4887-has-no-power-two-legal-folded-fatgraph: that is entry 4887 (524 types); this is entry 4012 (540 types), where plain column generation on the same relaxation had stalled at phase-1 value 0.1247 for four rounds.
  power-two-word-free-census-of-power-one-silent-classes: that leaves 4012 among the open LP-negative entries at power two; this decides it negatively, for every boundary.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion; this shows the criterion at power two cannot certify entry 4012.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4012_rm2_rpa2b1c1.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4012.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute_m2_4012.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/cg_memory.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vchain4.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/go4012.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/gowarm.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/prune.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/rcprune.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4012_rm2_rpa2b1c1_rounds.log
---

**ESTABLISHED (computer-certified).** Proof in `census-entry-4012-has-no-power-two-legal-folded-fatgraph-proof`.

**Statement.** Let `phi` be census entry 4012 of `m2_class_representatives.txt`,

`phi : a -> ab, b -> bbac, c -> abb`,

and let `f` be its rose map. Then no legal `f^2`-folded fatgraph over the rose exists, whatever its boundary
`partial^-`. In particular entry 4012 has no power-two certificate of
`legal-f-folded-fatgraphs-give-surface-subgroups`. So power two is silent on it, as power one is.

**What was known.** `power-two-word-free-census-of-power-one-silent-classes` lists 4012 as open.

- The full memory-2 LP was undecided under column generation (`cg_memory_r2_4012_m2_killed.log`).
- On the mixed-memory relaxation `(r_-, r_+) = (2, a2b1c1)` of
  `census-entry-4887-has-no-power-two-legal-folded-fatgraph`, four rounds of plain column generation held the
  phase-1 value at 0.1247. No master dual reached a positive dart-shifted value.

**Method.** The LP is the same mixed-memory relaxation as for 4887, built for 4012:

- `d^-` darts remember 2 letters;
- `d^+` darts in the block of `a` remember 2 letters, and those in the blocks of `b` and `c` remember 1;
- `a` has the shortest `f^2`-block (6 letters, against 13 for `b` and 10 for `c`);
- there are 540 types and 114 windows.

The projection argument (Steps 2 and 3 of `census-entry-4887-has-no-power-two-legal-folded-fatgraph-proof`) does
not depend on the entry. So an infeasibility proof for this LP is an exact obstruction.

**What unblocked it.** Column generation restarted with two changes:

- the Wentges smoothing centre was warm-started from the previous round's master dual, with that master's pair rows
  rebuilt;
- all of that round's columns were reloaded, not a pruned subset.

The dart-shifted value went from -0.62 to +0.043 in four iterations. Pruned restarts had lost the centre and fell
back to about -8.

**Certificate.** `farkas_vmem_m2_4012_rm2_rpa2b1c1.json` is an integer vector `z` on the type rows and pair rows
(`D = 10^6`), taken from that master dual.

- After the exact dart shift, 216 darts are shifted, by at most 48586.
- Every polygon of the mixed LP has charge `<= 0`, and every window has charge `<= 0`.
- The normalisation row has `z'_norm = 43609 > 0`.
- Two independent exact checks confirm it: `farkas_vmem.py` (max-plus) and `farkas_vmem_brute.py`, which
  enumerates every typed polygon in Python integers.

**Consequence.** Together with `census-entry-4887-has-no-power-two-legal-folded-fatgraph`, the open LP-negative
entries at power two drop to 11: 61, 108, 198, 228, 464, 1632, 1633, 1635, 1744, 2298 and 4485.
