# AK(3): the capped component at cap 26 (lane w8-082, 2026-09-18)

This supports `ak3-rank2-capped-component-at-total-length-26` and its route
`ak3-rank2-capped-component-at-total-length-26-proof`.

## Files

- `capbfs.c` is breadth-first exhaustion of S_CAP with checkpoints, so that the run fits
  1200 s slots. It includes `thzsearch.c` of `experiments/ak3-thick-z-pair-search-2026-09-17`
  verbatim. It adds a PRIM test on every new state and a length histogram.
  - Build: `gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o capbfs capbfs.c`.
  - Usage: `capbfs RANK CAP MAXSTATES r1 r2 CKPT`, then `capbfs resume CKPT`.
  - Exit codes: 7 means the slot ended and a checkpoint was written; 0 means exhausted, with
    the dump in `CKPT.txt`; 1 means the state limit was reached; 5 means a PRIM goal.
- `run.sh RANK CAP MAXSTATES NAME` drives a run in slots under `nice -n 10 timeout 1200`.
  Its header lists the four runs.
- `thkcheck.c` runs the Neuwirth THICK test (`thick2` through thzsearch's `thick_pair`) on
  a range of dump lines, after the planarity prefilter of `tunnel.c`.
  - Build: `gcc -O2 -I. -o thkcheck thkcheck.c`, with `thzsearch.c`, `thick2.c` and
    `tunnel.c` alongside.
  - `thkrun.sh K NW` is worker K of NW over chunks of `new26.txt`, the S_26 dump minus the
    S_24 dump.
- `decomp.py` compares the rank-2 and rank-3 dumps at caps 24 and 26.
- `alex.py` gives the histogram of the Alexander polynomials (Δ_1, Δ_2) of the one-relator
  quotients ⟨x, y | r_i⟩ over a dump.

## Logs

- `calib.log` has two calibrations.
  - A cap-24 run in three slots gives 261720 states, and its dump is byte-identical to
    thzsearch's S_24.
  - thzsearch at cap 26, stopped during level 9, has 735028 states after level 8, as
    `capbfs` does.
- `rank2-cap26.log` is S_26 in rank 2. It is exhausted at level 46 with 1690039 states,
  1690038 PRIM tests and no goal. The log ends with the length histogram.
- `rank2-cap28.log` is S_28 in rank 2: exhausted at level 68 with 11535176 states,
  11535175 PRIM tests and no goal. The container restarted during one slot, and a comment
  line marks the resume.
- `cmp28.log` is the output of `cmp28.py c26.ck.txt c28.ck.txt`: S_26 ⊂ S_28, and the
  histogram and examples of S_28 minus S_26.
- `rank3-cap26.log` is S³_26: exhausted at level 46 with 1914058 states, 1914057 PRIM tests
  and no goal.
- `rank3-cap24.log` is S³_24: 280213 states, the known count.
- `rank3-decomp.log` is the output of `decomp.py`.
  - The z-free part of S³_C equals S_C, for C = 24 and C = 26.
  - No state with z uses only two generators.
  - The new states of S³_26 with z number 205526, all of length 25 or 26.
- `thick-cap26.log` has one line per chunk: exit code, time, and the counts of states,
  thick2 calls, undecided calls and goals. It has 120 chunks, all exit 0, covering all 1428319
  states with 0 undecided and no goal.
- `alex-s24.log` is the head of the Alexander histogram over S_24, plus the 17 states
  with Δ_1 = Δ_2 = 1.

## Reproduce

```
THZ_DUMP=s24r2.txt thzsearch 2 24 4000000 xxxYYYY xyxYXY dump   # S_24 as "r1 r2" lines
./run.sh 2 26 33000000 c26                               # c26.ck.txt = S_26
./run.sh 2 28 33000000 c28; python3 cmp28.py c26.ck.txt c28.ck.txt
./run.sh 3 26 20000000 r3c26; ./run.sh 3 24 4000000 r3c24
python3 decomp.py s24r2.txt c26.ck.txt r3c24.ck.txt r3c26.ck.txt
python3 -c "s=set(open('s24r2.txt')); open('new26.txt','w').writelines(l for l in open('c26.ck.txt') if l not in s)"
CH=12000 ./thkrun.sh 0 2 & CH=12000 ./thkrun.sh 1 2
python3 alex.py < s24r2.txt
```

The dumps (46 MB for S_26, 52 MB for S³_26, 337 MB for S_28) are not kept.

Memory: 33M state slots take about 930 MB. The S_26 run used 1.69M of them, and the S³_26 run 1.91M of 20M.
