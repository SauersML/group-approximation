---
rg: 2
id: thompson-f-p22-x0-graded-sieve-census-proof
kind: route
title: Split each unsolved census pair into x_0-levels and look its extreme components up in the same census
target: thompson-f-p22-x0-graded-sieve-certifies-no-pair
requires:
  - thompson-f-ore-x0-components-meet-no-later
  - thompson-f-p22-over-f2-exhaustive-degree-seven-census
artifacts:
  - research/artifacts/ideas-f-hyperbolic-2026-09-13.md
  - research/artifacts/ideas-f-hyperbolic-2026-09-13-data/sieve_output.txt
---
**Step 1 (components stay in the census).** Each monomial of `S_(3,5)` has a definite level, so every
component of an element of `F_2[S_(3,5)]` is again an element of `F_2[S_(3,5)]`. A component pair is therefore
either two equal elements (`δ = 0`) or a pair of `P_(2,2)`, whose `δ` is recorded by
`thompson-f-p22-over-f2-exhaustive-degree-seven-census`: `δ > 7` exactly when the pair is on its unsolved list.

**Step 2 (computation).** The script `experiments/thompson-f/ore/ore_graded_sieve.py` (md5
`1053de496a6565804cb7bde2284947c5`) was run on MSI with `/usr/bin/python3.12`. It imports `guba_set` from
`experiments/thompson-f/ore/ore_linalg.py` (md5 `65070f09cffdb770f7b191f282c78c3a`), the census program. It
reads the census list `research/artifacts/thompson-f-ore-over-f2-2026-09-13-data/s35_unsolved_after_k7.json.gz`
(md5 `657b3222f07b6af157a54f07432112d6`).
- **Checks inside the script:**
  - the monomial order is the census order `x_0^2, x_0x_1, x_0x_2, x_0x_3, x_1^2, x_1x_2, x_1x_3, x_2^2, x_2x_3`;
  - the list has `94329` pairs.
- **What it computes, for every listed pair `(a, b)` of bitmasks:**
  - the level components and `top`/`bot`;
  - whether `a` and `b` are single-level;
  - the status of each component pair: `equal`, on the list (`unsolved`) or not (`solved`).
- **Output**, verbatim in `research/artifacts/ideas-f-hyperbolic-2026-09-13-data/sieve_output.txt`:
  - `SIEVE {'mixed|equal|equal': 166, 'mixed|equal|solved': 26376, 'mixed|solved|equal': 292, 'mixed|solved|solved': 67495}`;
  - `CORE_levels {}`, meaning no single-level pair is on the list;
  - `L1_vs_L0_nonmonomial_pairs {'solved': 124}`.

**Step 3 (conclusion).**
- **Item 1** is `CORE_levels {}`: no listed pair has both elements single-level. The item 2 counts, all of kind `mixed`, add to `94329`.
- **Item 2** is the `SIEVE` line; no component pair has status `unsolved`.
- **Item 3** follows from `thompson-f-ore-x0-components-meet-no-later`: a component pair gives the lower bound `δ(a, b) >= δ(component pair)`, and every such value is `<= 7`.
