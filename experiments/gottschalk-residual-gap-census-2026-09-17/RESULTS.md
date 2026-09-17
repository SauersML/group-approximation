# Residual-gap census of forward tables up to shape 4x4

Supports `research/strict-pairs-need-a-memory-with-five-elements.md` and its proof route.

A forward table `T` (a rook-independent partition of `S x M`, with `1` in both memories) is **resolved** when
finite permutation quotients of its table group `P(T)` separate every pair of reverse cells `x_m x_s` that
are distinct in `P(T)`. It is **NOTCLOSED** when the relators derive an equality of forward cells that `T`
does not contain, or one inside a row or column, so `T` is never the exact forward table of any group. A
**gap table** is one that is neither. Only gap tables can host strict automaton pairs, over any alphabet.

## Result

No gap table exists at shapes `3x3`, `3x4`, `4x3`, or `4x4`. The `2x2` and `2xk` shapes are covered by padding
(an infinite group always has unread addresses, so smaller memories pad to `4x4`).

| shape | raw partitions | orbits | prefilter: collision | prefilter: not closed | survivors | RESOLVED | NOTCLOSED | gap |
|---|---|---|---|---|---|---|---|---|
| 3x3 | 588 | 109 | 0 | 35 | 74 | 74 | 0 | 0 |
| 3x4 | 30,240 | 2,591 | 731 | 951 | 909 | 837 | 72 | 0 |
| 4x3 | 30,240 | 2,591 | 731 | 951 | 909 | 837 | 72 | 0 |
| 4x4 | 17,427,192 | 246,595 | 167,350 | 57,993 | 21,252 | 14,014 | 7,238 | 0 |

The orbits are taken under `Sym(S minus 1) x Sym(M minus 1)`, together with inversion (transpose) when `|S| = |M|`;
that is 72 symmetries at `4x4`. The enumerator takes 25.6 s at `4x4`.

### How the 14,014 resolved `4x4` tables were resolved

| stage | tables | witnesses |
|---|---|---|
| pass 1 (`gapcensus.py reps`, Knuth-Bendix 200 ms, Sims1 degree <= 5, regular representation when finite of order <= 20000) | 13,828 | 1,731 use a regular representation (largest degree 896) |
| pass 2 (`pass2.py`: quotients kill a subset of generators and impose `g^n = 1` with `n <= 12`, regular representation when order <= 5000, then Sims1 degree <= 7 for 60 s) | 177 | |
| pass 3 (`pass3.py`: Tietze elimination, then Sims1 degree <= 10 for 300 s) | 9 | |

Pass 1 output by chunk (survivor index ranges):

| chunk | RESOLVED | NOTCLOSED | CANDIDATE | seconds |
|---|---|---|---|---|
| 0-5000 | 2,987 | 1,999 | 14 | 254.8 |
| 5000-10000 | 3,056 | 1,904 | 40 | 352.8 |
| 10000-15000 | 3,332 | 1,610 | 58 | 422.9 |
| 15000-20000 | 3,407 | 1,541 | 52 | 472.2 |
| 20000-21252 | 1,046 | 184 | 22 | 145.0 |

Pass 2 resolved 177 of the 186 candidates. After Tietze elimination, the 9 it left over (ids 9851, 9925, 9962,
10377, 12397, 12764, 12967, 16672, 16681) are two-generator one-relator groups with a relator of length 8, for
example `<a, b | b a^-1 b a b a^-1 b^-1 a>`. Their separating quotients need degree 8, and pass 3 found them.

## Cross-checks

- `verify.py 4 4 census_4x4.jsonl.gz` prints `verified 14014 failed 0`. The checker is pure Python and
  independent of libsemigroups. For each resolved record, every witness is a tuple of permutations satisfying
  every relator, and the witnesses split the reverse cells into exactly the recorded classes. The same check
  passes on `census_3x3`, `census_3x4`, and `census_4x3`.
- **Prefilter soundness, sample at `4x4`.** `enumtables 4 4 rejected` emits every rejected orbit whose orbit index
  is divisible by 97, giving 2,339 tables. `gapcensus.py reps 4 4 rejected_sample_4x4.txt 2 500` classifies all
  2,339 as NOTCLOSED by Knuth-Bendix (`rejected_sample_4x4.jsonl.gz`).
- **Prefilter calibration at `3x4`.** An earlier, separately canonicalized Python enumeration resolved 837 orbits.
  All of them survive the prefilter.

## Trust boundary

- NOTCLOSED verdicts and the reverse-class merges rest on the soundness of the rewriting rules derived by
  libsemigroups' Knuth-Bendix. Every derived rule is a consequence of the relators, whether or not completion
  finished.
- Rejections by the prefilter rest on rules R1/R2 in `enumtables.c`, which hold in every group, and on the
  implementation, which was cross-checked as above.
- Separations are certified independently by `verify.py`.

## What this rules out

Every strict pair `sigma tau = id` with `tau` not surjective and `|M| <= 4`, `|S| <= 4`, over every group and every
finite alphabet.

## Files

- `enumtables.c` is the orderly enumerator with the difference-closure prefilter.
- `gapcensus.py` is pass 1.
- `pass2.py` and `pass3.py` are passes 2 and 3.
- `merge.py` gives the final record per id.
- `verify.py` is the independent checker.
- `census_3x3.jsonl.gz`, `census_3x4.jsonl.gz`, `census_4x3.jsonl.gz`, and `census_4x4.jsonl.gz` hold the final records, with the relators, reverse classes, and witnesses.
- `reps_4x4.txt.gz` lists the 21,252 survivors (restricted growth strings, row-major).
- `rejected_sample_4x4.jsonl.gz` is the prefilter sample.

## Reproduction

Run from this directory. Requirements: `libsemigroups_pybind11` and `gcc`. Everything is single-threaded.

```
gcc -O2 -o enumtables enumtables.c
./enumtables 4 4 > reps_4x4.txt
for k in 0 1 2 3 4; do a=$((5000*k)); b=$((5000*(k+1)));
  nice -n 10 timeout 1200 python3 gapcensus.py reps 4 4 reps_4x4.txt 5 200 r44_$k.jsonl $a $b; done
for k in 0 1 2 3 4; do
  nice -n 10 timeout 1200 python3 pass2.py 4 4 r44_$k.jsonl p2_$k.jsonl 7 2000 60
  nice -n 10 timeout 1200 python3 pass3.py 4 4 p2_$k.jsonl p3_$k.jsonl 10 300; done
python3 merge.py census44.jsonl r44_*.jsonl -- p2_*.jsonl -- p3_*.jsonl   # 21252 {'RESOLVED': 14014, 'NOTCLOSED': 7238}
python3 verify.py 4 4 census44.jsonl                                      # verified 14014 failed 0
./enumtables 4 4 rejected > rejected_sample_4x4.txt
nice -n 10 timeout 1200 python3 gapcensus.py reps 4 4 rejected_sample_4x4.txt 2 500 rej44.jsonl   # all NOTCLOSED
for s in "3 3" "3 4" "4 3"; do set -- $s; ./enumtables $1 $2 > reps_$1x$2.txt;
  python3 gapcensus.py reps $1 $2 reps_$1x$2.txt 5 200 r$1x$2.jsonl; python3 verify.py $1 $2 r$1x$2.jsonl; done
```
