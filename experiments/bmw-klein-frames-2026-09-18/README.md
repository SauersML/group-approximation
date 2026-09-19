# Conjugate-frame Klein chains and flat Klein bottles (2026-09-18)

This experiment supports `research/bmw-klein-frame-chain-certificates.md`.

Census files are in `experiments/bmw-census-left-orders-2026-09-17/` (`census_X.json`, with candidate
lists `out_X.jsonl`). The two checkers are the ones from
`experiments/bmw-klein-chains-transposed-2026-09-17/`: `verify_klein2.py`, which rewrites with the
squares and logs full traces, and `crosscheck2.py`, which uses an independent normal-form algorithm.

## Scripts

- `kframe.py`: the conjugate-frame search. Every node is kept as `c W c^-1` with `W` a cyclically
  reduced pure word. K-moves conjugate a pure inverter of a rotation of `W` by a prefix of `W`, and
  power moves go from `c r^e c^-1` to `c r^f c^-1`. A strongly connected component with a K edge gives a
  certificate. Conjugators are never enumerated as a ball: each one is the product of prefixes along the
  chain, i.e. an element fixing a vertex of one tree (Theorem 4 of
  `bmw-census-klein-power-chain-certificates-proof`).
  ```
  kframe.py census.json classes|cand L S NB [--cand out_X.jsonl] [--skip chains.json] [--cap N]
            [--shift] [--out chains_X.json] [--log kf_TAG_X.jsonl] [--sb SB]
  ```
  - `L` is the maximum length of a pure inverter.
  - `S` is the maximum length of a seed.
  - `NB` is the maximum normal-form length of a node.
  - The log is resumable.
- `run_frames.sh L S NB CAP TAG [flags]`: runs `kframe.py` over every candidate without a chain. `CHK`
  names the directory holding `out_X.jsonl` and the earlier `chains_X.json`. Each run has
  `timeout 1200`.
- `kbottle.py census.json class P [--swap]`: every pure pair `A B A^-1 = B^-1` with `|A| = p` fixed and
  `|B|` unbounded, for each even `p ≤ P`. It is a meet-in-the-middle BFS over pairs of sections of `A`,
  and it is complete for each `p`.
- `kbottleB.py census.json class Q [--swap]`: the same with `|B| = q` fixed and `|A|` unbounded. The
  states are (section of `A` in `B`, last letter of `A`, parity of `|A|`). Reachability runs on the
  condensation with bitsets, so the result is exact for every `|A|`.
- Calibration on `41_30` #55: `kbottleB` finds `B ∈ {01, 02, 10, 20}` at `q = 2`, and `2323`, `3232`
  with `--swap` at `q = 4`. This matches that class's known chain.

## Commands

```
CHK=<dir with out_X.jsonl and main's chains_X.json> ./run_frames.sh 6 6 16 30000 p1
for c in 26; do for s in "" --swap; do nice -n 10 timeout 1200 python3 kbottle.py \
  $C/census_31_30.json $c 16 $s; done; done >> kbottle_31_30_26.jsonl        # likewise 31_31 #12
for s in "" --swap; do nice -n 10 timeout 1200 python3 kbottleB.py $C/census_31_30.json 26 14 $s; \
  done >> kbottleB_31_30_26.jsonl                                              # likewise 31_31 #12
python3 verify_klein2.py $C/census_X.json chains_X.json;  python3 crosscheck2.py $C/census_X.json chains_X.json
```

## Results

- `chains_41_30.json`: #80 and #113, 8 elements with 4 (K) steps. The elements are mixed words such as
  `v02|h0320`, so no pure search finds them.
- `chains_52_30.json`: #158, 10 elements with 4 (K) and 4 (R) steps. The elements are pure words of
  length up to 16.
- `verify_X.log`: both checkers accept every chain.
- `kf_p1_X.jsonl`: one record per class searched, with its seeds, nodes, edges, cap flag and chain.
  Most classes exhaust their graph within `NB = 16` without a cycle. Classes with 0 seeds have no pure
  inverting pair with inverter length at most 6.
- `kbottle_31_30_26.jsonl`, `kbottle_31_31_12.jsonl`: no pure inverting pair with `|A| ≤ 16`, in either
  orientation. Every search is complete and uncapped. The state counts are 18, 104, 344, 2680, 11944,
  43016, 236232 and 1010312.
- `kbottleB_31_30_26.jsonl`, `kbottleB_31_31_12.jsonl`: no pure inverting pair with `|B| ≤ 14`, in
  either orientation, for any `|A|`.
