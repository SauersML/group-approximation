---
rg: 2
id: census-entry-4012-has-no-power-two-legal-folded-fatgraph-proof
kind: route
title: Build the mixed-memory (2, a2b1c1) polygon LP for entry 4012, reuse the entry-independent projection of the 4887 proof, and refute the LP by an exact dart-shifted Farkas vector found by warm-centred column generation
target: census-entry-4012-has-no-power-two-legal-folded-fatgraph
requires:
  - census-entry-4887-has-no-power-two-legal-folded-fatgraph
  - power-two-word-free-census-of-power-one-silent-classes
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - positive-f-folded-fatgraphs-have-only-even-valence
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4012_rm2_rpa2b1c1.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4012.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute_m2_4012.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/cg_memory.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vchain4.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/go4012.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/gowarm.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/entries.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/prune.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/rcprune.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4012_rm2_rpa2b1c1_rounds.log
---

**Notation.** This route uses the notation of `census-entry-4887-has-no-power-two-legal-folded-fatgraph-proof`
(the "4887 proof" below). Here `phi` is entry 4012 of `m2_class_representatives.txt`:

- `phi : a -> ab, b -> bbac, c -> abb`;
- `phi^2 : a -> abbbac, b -> bbacbbacababb, c -> abbbacbbac`;
- the blocks `R(a), R(b), R(c)` have 6, 13 and 10 letters;
- the gate bound of `positive-f-folded-fatgraphs-have-only-even-valence` gives `maxval = 4`, as for 4887.

`lp_vmem.setup` prints these values.

**Step 1: reduction to power one for `phi^2`.** This is Step 1 of the 4887 proof. It uses only Steps 1 and 2 of
`power-two-word-free-census-of-power-one-silent-classes-proof`, which hold for every entry of the census, 4012
included. So a legal `f^2`-folded fatgraph is a legal `g`-folded fatgraph with `[partial^-] = 0`, where `g` is the
rose map of `phi^2`.

**Step 2: the LP.** Take the mixed-memory LP of Step 2 of the 4887 proof, with the same memories:

- `r_-(x) = 2` for every letter;
- `r_+(a) = r_+(A) = 2`;
- `r_+(x) = 1` for `x` in `{b, B, c, C}`.

Build it from the legal turns and blocks of 4012. `lp_vmem.build` gives 540 types and 114 windows, with type
rows, pair rows, circulation rows, homology rows and normalisation, all defined as in the 4887 proof.

**Step 3: projection.** Step 3 of the 4887 proof shows that every legal `g`-folded fatgraph projects to a feasible
point of this LP. It uses only three facts:

- the words of `partial^-` are cyclically legal;
- the `partial^+` circle of `w = x_1 ... x_L` reads `R(x_L) ... R(x_1)`;
- the vertex conditions 1 to 4 and the bound `k <= maxval` depend only on data the types keep.

None of these depends on the entry, so parts (a) to (e) apply word for word.

The code note of that step already covers 4012: it records that the old and corrected successor tests give the
same successor sets on 4012. The certificate below was checked under the corrected code, `(u_{last}, v_{last})`.

**Step 4: the Farkas lemma.** This is Step 4 of the 4887 proof. Suppose an integer vector `z` on the rows has
three properties:

- every typed polygon has charge `<= 0`;
- every window has charge `<= 0`;
- `z_norm > 0`.

Then the LP is infeasible. By Steps 1 and 3, no legal `f^2`-folded fatgraph exists for entry 4012, whatever its
boundary.

**Step 5: the vector and its checks.** `farkas_vmem_m2_4012_rm2_rpa2b1c1.json` stores integers `zrows` and
`zpairs` at `D = 10^6`, in the row layout of `lp_vmem.build(TY, [])`. It has the same format as the 4887
certificate, and both checkers are those of Step 5 of the 4887 proof.

The checkers first recompute the exact dart shift, `R_d = max(0, max over polygons P through d of ceil(charge(P)/|P|))`.
They set `z'_d = z_d - R_d` and `z'_norm = -max_w (other window charge)`. Then they re-check every inequality:

- **`farkas_vmem.py`** (exact max-plus over all cyclic typed sequences of length 2 to 4, a superset of the
  polygons) writes `farkas_vmem_m2_4012.log`.
- **`farkas_vmem_brute.py`** (every typed polygon enumerated one at a time, in Python integers) writes
  `farkas_vmem_brute_m2_4012.log`. The enumeration found 7,845,762 polygons, the same count in both passes.

Both checkers give the same numbers:

- 216 shifted darts, with maximum shift 48586;
- maximum polygon charge 0;
- maximum window charge 0;
- `z'_norm = 43609`, that is `0.043609 D`.

Their verdicts are `FARKAS VERIFIED` and `BRUTE FARKAS VERIFIED`. To rerun them:

- `python3 farkas_vmem.py farkas_vmem_m2_4012_rm2_rpa2b1c1.json`
- `python3 farkas_vmem_brute.py farkas_vmem_m2_4012_rm2_rpa2b1c1.json`

**Step 6: how the vector was found.** This step is not load-bearing: Steps 3 to 5 are the proof.
`vcg_m2_4012_rm2_rpa2b1c1_rounds.log` concatenates rounds 2 to 5 of `vcg.py` on this LP. Each section header
says how that round was started. Rounds 0 and 1 are w7-074's. Each round is one `timeout 1200` process.

- **Rounds 2 to 4.** Plain Wentges-smoothed column generation (`CG_ALPHA = 0.3`) left the phase-1 value between
  0.1249 and 0.1310. The best float dart bounds were -1.99 (round 2) and -0.18 (round 3). The exact dart-shifted
  values of the rounded duals were -1.94 and -0.166. Round 4 reloaded a pruned column set (`prune.py`) and fell
  back to -2.14.
- **The problem.** Each restart began from a cold centre. With the columns pruned, the IPM duals are poor, and
  smoothing towards them loses the progress made.
- **Round 5 (`go4012.sh`).** It makes two changes:
  - it warm-starts the smoothing centre from the round-3 master dual (`CG_CENTER` in `cg_memory.py`), rebuilding
    that master's pair rows;
  - it reloads all round-3 columns, unpruned.

  The centre's dart-shifted value was -0.6199 at the start. At iteration 4 the dart bound reached +0.043, and the
  run stopped with `phase 1 Lagrangian bound > 0`. That iteration's master dual, rounded at `D = 10^6`, is the
  certificate. It was checked exactly as in Step 5.

`gowarm.sh ENTRY RP ROUND N` is the same restart for any entry. It reads `entries.json`, which maps each entry
to its `phi0`. `rcprune.py` keeps the columns of reduced cost `<= eps` at a dump's dual; it is used in later
rounds.

**Dead ends recorded.** These are float runs, not claims. They are in the same log.

- A stronger smoothing weight (`CG_ALPHA = 0.85`, warm centre, pruned columns) made no progress and was killed.
- A hard box step around the centre (`CG_BOX = 0.05`) made the master unbounded.
- A soft box (`CG_BOX_U = 1`) ran but made no progress, and was killed.

**Scope.**

- The float solver only proposes `z`. The inequalities of Step 4 are checked exactly, twice, by different
  enumerations.
- The claim is about legal `f^2`-folded fatgraphs over the rose for entry 4012. It says nothing about powers
  `m >= 3`, or about surface subgroups found by other methods.
