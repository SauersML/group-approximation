---
rg: 2
id: census-entry-4887-has-no-power-two-legal-folded-fatgraph
kind: claim
title: Census entry 4887 has no legal f^2-folded fatgraph over the rose for any boundary, by an exact Farkas vector for a mixed-memory relaxation of the memory-two polygon LP
distinct_from:
  power-two-word-free-census-of-power-one-silent-classes: that leaves 4887 among 13 open LP-negative entries, with the full memory-two LP undecided after eleven column-generation rounds; this decides 4887 negatively, for every boundary.
  legal-folded-certificates-at-power-one-census: that decides power one on the census with the memory-zero LP; this is power two, on an entry where the memory-zero and memory-one LPs are feasible with chi = -1/2.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion; this shows the criterion at power two cannot certify entry 4887.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/sp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vchain2.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4887_rm2_rpa2b1c1.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4887.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute_m2_4887.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rpa2b1c1_round0.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rpa2b1c1_round1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rp1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm3_rp1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/sp_vmem_m2_4887_masks.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_vmem_certificates.log
---

**ESTABLISHED (computer-certified).** Proof in `census-entry-4887-has-no-power-two-legal-folded-fatgraph-proof`.

**Statement.** Let `phi` be census entry 4887 of `m2_class_representatives.txt`,

`phi : a -> ab, b -> bbca, c -> aab`,

and let `f` be its rose map. Then no legal `f^2`-folded fatgraph over the rose exists, whatever its boundary
`partial^-`. In particular entry 4887 has no power-two certificate of
`legal-f-folded-fatgraphs-give-surface-subgroups`. So power two is silent on it, as power one is.

**What was known.** `power-two-word-free-census-of-power-one-silent-classes` lists 4887 as open.

- The memory-0 and memory-1 word-free LPs are feasible on 4887, with optimum `chi = -1/2`.
- Every power-two certificate must use all three letters.
- The full memory-2 LP (1164 types, 114 windows) was undecided. Plain column generation levelled off at a phase-1
  value near 0.162 and never reached a dual with a positive dart-shifted value.

**Method: abstraction refinement.** The memory `r` of the LP is split three ways:

- the memory `r_-` of `d^-` darts;
- the memory `r_+` of `d^+` darts;
- for `d^+` darts, a memory that depends on the letter `x_j` whose block `f(x_j)^{-1}` the dart sits in.

The flow variables stay on windows of `R + 1` letters, with `R = max(r_-, r_+)`. A dart type then counts a
sum of window variables. Every legal fatgraph still projects to a feasible point, so the mixed LP is a
relaxation of the memory-`R` LP, and an infeasibility proof for it is an exact obstruction.

The coarsenings that fail are recorded in the proof as dead ends:

- `(r_-, r_+) = (2, 1)` is feasible with `chi = -1/2`, and so is `(3, 1)`.
- The mixed memory with `r_- = 2` and `r_+ = (a: 2, b: 1, c: 1)` is infeasible. It has 524 types and 114 windows,
  2.2 times fewer types than the full memory-2 LP.
- That choice of `r_+` gives memory 2 to `a`, the letter with the shortest `f^2`-block.

**Certificate.** `farkas_vmem_m2_4887_rm2_rpa2b1c1.json` is an integer vector `z` on the type rows and pair
rows (`D = 10^6`), taken from one column-generation dual.

- After the exact dart shift, 176 darts are shifted, by at most 29714.
- Every polygon of the mixed LP has charge `<= 0`, and every window has charge `<= 0`.
- The normalisation row has `z'_norm = 65944 > 0`.
- Two independent exact checks confirm it. `farkas_vmem.py` uses max-plus products. `farkas_vmem_brute.py`
  enumerates every typed polygon in Python integers.

**Consequence.** The open LP-negative entries at power two drop from 13 to 12: 61, 108, 198, 228, 464, 1632, 1633,
1635, 1744, 2298, 4012 and 4485. On 4887 a surface subgroup, if one exists, is invisible to legal folded
fatgraphs at powers 1 and 2. It would need power 3 or higher, or another method.
