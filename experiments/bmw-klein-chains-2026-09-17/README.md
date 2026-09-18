# Klein chains in BMW parity kernels (w6-107c, 2026-09-18)

**Criterion.** In a left-ordered group, `a b a^{-1} = b^{-1}` with `b ≠ 1` implies `|b| < |a|`, where
`|g| = max(g, g^{-1})`. So a directed cycle `x_1 → x_2 → ⋯ → x_m → x_1`, in which each `x_{i+1}` inverts
`x_i`, refutes left-orderability.

The proofs are in:
- `research/bmw-40-40-193-281-332-klein-chain-proof.md`: the three `40_40` survivors, by hand;
- `research/bmw-census-sat-free-klein-chain-certificates-proof.md`: 33 census classes.

No SAT solver is involved anywhere. All commands below run from this directory.

## Certificates

**Chain files.** Each gives the four elements `x_1..x_4` per class, as normal forms `v…|h…`.
- `chains_40_40.json`: `40_40` #193, #281 and #332.
- `chains_census_40_30.json`: `40_30` #55.
- `chains_census_50_30.json`: `50_30` #55, #240, #241, #242, #243, #258 and #430.
- `chains_census_40_40.json`: 25 classes of `40_40`, including all five `R8s2` letter-ball SAT
  survivors, #176, #193, #256, #281 and #332.

**Checker.** `verify_klein.py` is independent of the search and reads only the census file. It checks:
1. the square map is a bijection, `pA = pB = 0`, and the rewriting system `{xx → 1, hv → v'h'}` is
   locally confluent, so normal forms are unique;
2. each `x_i` is a nonempty normal form with even `v`- and `h`-length, so it lies in `Γ^+`;
3. `x_{i+1} x_i x_{i+1}^{-1} x_i` reduces to `1`.

With `--trace` it prints every rewriting step.

**Logs.** Each log starts with the command that produced it.
- `verify_klein.log`: `python3 verify_klein.py ../bmw-census-left-orders-2026-09-17/census_40_40.json chains_40_40.json --trace`
- `verify_census_X.log`: the same command with `census_X.json` and `chains_census_X.json`, for
  `X = 40_30, 50_30, 40_40`.

All 33 classes pass.

## Search

The search does not enter the proofs.

**`kpure.py census.json L out.jsonl classes`** scans pure words: the `v`-words and `h`-words of even
length at most `L`.
- It builds the graph of inverting pairs between a `v`-word and an `h`-word by pushing words through
  each other, then finds a directed cycle.
- Two words of the same family never form an inverting pair, because the even words of a free product
  of `Z/2`'s form a free group.
- It needs only the census file.

**`kscan.py census.json L out.jsonl [classes]`** is the earlier scan over all normal forms of letter
length at most `L`. It needs `lo_census.py` from `../bmw-census-left-orders-2026-09-17/` on
`PYTHONPATH`.

**Candidates.** `candidates_X.txt` lists the census classes in which some automaton image is not
certified finite (`finH` or `finV` is `null` in `out_X.jsonl`). There are 2, 27, 190 and 301 of them
for `X = 30_30, 40_30, 50_30, 40_40`.

**Runs.**

```sh
nice -n 10 timeout 1200 python3 kpure.py ../bmw-census-left-orders-2026-09-17/census_X.json 6 kpure_X_L6.jsonl $(cat candidates_X.txt)
```

The command was run in chunks of 60 classes. Each output record gives the class, `L`, the number of
inverting pairs and the cycle, if one was found.

| file | contents |
|---|---|
| `kpure_X_L6.jsonl` | chains at `L = 6`: 0 of 2 (`30_30`), 1 of 27 (`40_30`), 7 of 190 (`50_30`) and 24 of 301 (`40_40`) |
| `kp_176.jsonl` | `40_40` #176 at `L = 6` (no cycle) and `L = 8` (cycle, one word of length 8) |
| `kp_5030.jsonl` | `50_30` #258 at `L = 6` (cycle) and #470 at `L = 6, 8` (no cycle, 366952 pairs at `L = 8`) |
| `kscan_40_40_L4.jsonl` | `kscan.py` at `L = 4` on all 824 classes of `40_40` |

**Not covered.**
- Patterns with transposed letter pairs (`pA > 0` or `pB > 0`) are not supported by either scanner.
- `50_30` #470 is open for this method.
