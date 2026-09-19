# The (8, 10) middle piece: deleting the top shell T by (K) moves

This directory completes the (K) phase of `../README.md`. The claim is `z8-rips-contractible-at-scale-10`, and its
proof route is `z8-rips-contractible-at-scale-10-proof`. The d-prefix `../certs/d-prefix-8-10.txt.gz` takes `Lmax_8`
to `O`, and the d-tail `../certs/d-tail-8-10.txt.gz` takes `O ∖ T` to `{e_8}`. Both are replayed in `../results.txt`.
This directory supplies the piece from `O` to `O ∖ T`.

## Files

- `chains/k-middle-8-10.txt.gz`: 18,816 lines `K u | w`, in chain order A, B, E, F, C, D.
- `chains/blocks-8-10.txt.gz`: every point of `T` with its block letter (`A`, `B`, `C`, `D`, `E`, `F`). Here `B` is
  only the part of `TB` that chain B deleted, and `E`, `F` are the two halves of the 1,120 points it left.
- `chains/stage-index.txt`: one row per stage, giving the chain, the stage, the first and last line in
  `k-middle-8-10.txt.gz`, the search program, the size and sha256 of the sorted start set, and the replay verdict.
- `kzs3.cpp`: the block-restricted search used for chains E and F from their second stage (the proof route, §2).
- `kzv7.cpp`: the verifier (the proof route, §3).
- `vpiece7.sh`: replays one stage with `kzv7` in budgeted pieces and compares the end set.
- `mkord.sh`: writes a stage's start set in the order of `O` (the verifier's scan order).
- `v7queue.sh`: a worker that takes stages from a queue file and runs `mkord.sh` and `vpiece7.sh`.
- `segchain3.sh`: runs a `kzs3` chain stage by stage until its block is empty.
- `assemble.sh`: builds the three files in `chains/` from the stage files and checks the blocks, the joins, the
  end set `O ∖ T` and that the blocks partition `T`.
- `finish.sh`: once a chain's block is empty, keeps its `K` lines and checks its end set is `start ∖ block`.
- `results.txt`: every run, with sha256 of inputs and outputs.

## Rebuilding and checking

Build with `g++ -O3 -march=native -o kzv7 kzv7.cpp` (AVX-512BW is needed), and the same for `kzs3`.

To check the middle piece, first make `O` from `../sets/O-8-10.txt.gz`. Then split `k-middle-8-10.txt.gz` by the
line ranges of `stage-index.txt`. Replay each stage from its start set, which is `O` minus the `u` of all earlier
lines, in the order of `O`:
`./kzv7 8 10 start.txt stage.txt end.txt 1000`. Exit code 3 means the time budget paused the run (`vpiece7.sh` does
the chaining), and 0 means every line checked. The run prints `ACCEPT` when every line checks.

The replay of one stage as a whole is equivalent to the replay of the concatenation, because all moves only delete
points and every condition refers only to the current set.

## Join rule

A chain's (K) lines are all at points of its own block, so a finished chain ends at exactly `start ∖ block`
(`finish.sh` checks this). So each chain's end set is the start set of the next: see the table in the proof route,
§1. The joins `A13 = B0`, `E0 = B13`, `B13 ∖ TE ∖ TF = C0`, `C13 = D0` and `D10 = O ∖ T` were checked as sets.

## Stalls

No chain stalled: every stage deleted points. After 13 stages of `kzs2` (1,000 s each), the chain for `TB` still had
1,120 points of `TB` left, while it deleted between 166 and 397 points per stage. So the rest was split into `TE` and
`TF` and run as two chains in parallel. `kzs3` was written to try only (K) moves at the listed points. `kzs2`
attempts (D) at every point, so `kzs3` is about seven times faster.
