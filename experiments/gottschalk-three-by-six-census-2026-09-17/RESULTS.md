# Census of forward tables at shape 3x6, with soficity certificates

Supports `research/injective-ca-with-memories-three-and-six-are-surjective.md` and its proof route.

A forward table `T` of shape `3x6` is a rook-independent partition of `S x M`, with `1` in both memories. Its table
group is `P(T)`. `3x6` is a minimal gap shape (`gap-tables-first-appear-at-three-by-six-and-four-by-five`): some
tables there have `P(T) = BS(2,3)` and a reverse pair that no finite quotient separates. So the finite-quotient census
of `strict-pairs-need-a-memory-with-five-elements` cannot finish this shape by itself. This census adds a third
verdict: **SOFIC**, where `P(T)` is certified sofic, so no strict pair lives on `T`.

## Result

Every one of the 68,844 closure survivors at `3x6` is NOTCLOSED, RESOLVED or SOFIC. No CANDIDATE remains.

| state | tables |
|---|---|
| NOTCLOSED | 13,231 |
| RESOLVED | 54,722 |
| SOFIC | 891 |
| CANDIDATE | 0 |
| total | 68,844 |

`verify.py 3 6 census_3x6.jsonl.gz` prints `verified 54722 failed 0`, and `verify_sofic.py 3 6 census_3x6.jsonl.gz`
prints `verified 891 failed 0`.

Certificate mix of the 891 SOFIC records. Each reduced presentation is a free group of rank 0, 1 or 2 (529, 337 and 25
records) times exactly one factor with relators.

| factor certificate | records |
|---|---|
| cyclic | 359 |
| partially-positive one-relator | 274 |
| peelable-extreme one-relator | 258 |

Of these, 87 factors are Baumslag-Solitar relators `t b^p t^-1 b^q`: 40 with `{|p|,|q|} = {1,2}`, 7 with `{1,3}`, 9 with `{1,4}`, and 31 with `{2,3}`. The last 31 are not residually finite.

## Pipeline and counts

The 1,279 pass-1 CANDIDATEs were decided in stages. Every table that one stage leaves CANDIDATE goes to the next.

| stage | decided | left |
|---|---|---|
| pass 1 (`gapcensus.py`) | 54,334 RESOLVED, 13,231 NOTCLOSED | 1,279 |
| `soficcert.py` | 891 SOFIC | 388 |
| `pass2.py 7 2000 20` | 360 RESOLVED | 28 |
| `finitewitness.py 30 20000` | 9 RESOLVED | |
| `pass3.py 10 300` | 18 RESOLVED | |
| `witness65499.py` | 1 RESOLVED | 0 |

The finite-witness and pass-3 stages together decide 27 tables. In chunks 0-9, pass 3 ran before the finite-witness
stage (12 by pass 3, then 1 by finite witness: survivor 35570,
`P(T) = <a, b | b^3, a b^-1 a^-2 b a b^-1>`, quotient `P(T)/<<a^8>>` of order 216, degree 27). In chunks 10-17, the
finite-witness stage ran first (8 decided), then pass 3 (6 decided).

**Survivor 65499** is the only table that every automatic stage left CANDIDATE. After the logged Tietze moves,
`P(T) = <x2, x3, x7 | u x2 u x2 u, u x2^-1 u^-1 x2^-2>` with `u = x7 x3^-1`. The Nielsen change `x7 -> u x3` shows
`P(T) = Z * Z/9`, with `x2 = u^3` (the derivation is in the docstring of `witness65499.py`). The automatic stages
missed it for two reasons. Killing a power of one remaining generator leaves an infinite free product, and pass 3
(Sims1 up to degree 10) found no separating action. A random degree-12 representation `u -> 9-cycle`,
`x3 -> random` separates all 18 reverse cells on the first trial. `verify.py` checks it like any other witness, so
the hand derivation is not trusted.

Pass 1 by chunk (survivor index ranges, `gapcensus.py reps 3 6 reps_3x6.txt 5 200`):

| chunk | survivor ids | RESOLVED | NOTCLOSED | CANDIDATE | seconds |
|---|---|---|---|---|---|
| 000 | 0-3999 | 3550 | 424 | 26 | 304 |
| 001 | 4000-7999 | 3104 | 810 | 86 | 253 |
| 002 | 8000-11999 | 2701 | 1215 | 84 | 334 |
| 003 | 12000-15999 | 2937 | 994 | 69 | 468 |
| 004 | 16000-19999 | 2774 | 1137 | 89 | 568 |
| 005 | 20000-23999 | 2871 | 1063 | 66 | 381 |
| 006 | 24000-27999 | 2907 | 1017 | 76 | 618 |
| 007 | 28000-31999 | 3197 | 736 | 67 | 487 |
| 008 | 32000-35999 | 3287 | 609 | 104 | 907 |
| 009 | 36000-39999 | 3421 | 491 | 88 | 721 |
| 010 | 40000-43999 | 3326 | 606 | 68 | 603 |
| 011 | 44000-47999 | 3027 | 919 | 54 | 483 |
| 012 | 48000-51999 | 3102 | 859 | 39 | 507 |
| 013 | 52000-55999 | 3362 | 572 | 66 | 585 |
| 014 | 56000-59999 | 3463 | 470 | 67 | 735 |
| 015 | 60000-63999 | 3195 | 697 | 108 | 491 |
| 016 | 64000-67999 | 3302 | 587 | 111 | 741 |
| 017 | 68000-68843 | 808 | 25 | 11 | 137 |

Wall-clock times are on a shared machine at load average about 20.

## Files

- `pass1.sh`: the resumable chunked driver of pass 1. It uses `gapcensus.py` of
  `experiments/gottschalk-residual-gap-census-2026-09-17` unchanged.
- `soficcert.py`: the soficity certificates. It performs:
  - logged Tietze elimination;
  - free splitting into components;
  - per-component certificates: cyclic, partially-positive one-relator
    (`partially-positive-one-relator-groups-are-sofic`), or two-generator one-relator with a peelable extreme letter
    after Nielsen moves (`peelable-extreme-one-relator-groups-are-sofic`). Baumslag-Solitar relators are also labelled
    `bs`.
- `verify_sofic.py`: the independent checker of SOFIC records (pure Python, no imports from the census code). It
  replays the Tietze log, the splitting and every factor certificate.
- `finitewitness.py`: candidate finite quotients `P(T)/<<g^n>>` from GAP, on the Tietze-reduced presentation. They are
  pulled back to the original generators and replayed by `verify.py`.
- `witness65499.py`: the separation witness for survivor 65499, whose table group is `Z * Z/9`.
- `census_3x6.jsonl.gz`: one final record per survivor (`id` = line index in the survivor list of
  `enumtables6 3 6 prune`).

## Reproduction

```
cc -O2 -o enumtables6 ../gottschalk-baumslag-solitar-gap-tables-2026-09-17/enumtables6.c
./enumtables6 3 6 prune > reps_3x6.txt      # 68,844 lines
bash pass1.sh reps_3x6.txt work              # r36_000 .. r36_017
C=../gottschalk-residual-gap-census-2026-09-17
for k in 000 ... 017; do
  python3 soficcert.py 3 6 work/r36_$k.jsonl work/sc_$k.jsonl
  PYTHONPATH=$C python3 $C/pass2.py 3 6 work/sc_$k.jsonl work/p2_$k.jsonl 7 2000 20
  python3 finitewitness.py 3 6 work/sc_$k.jsonl work/p2_$k.jsonl work/fw_$k.jsonl 30 20000
  PYTHONPATH=$C python3 $C/pass3.py 3 6 work/fw_$k.jsonl work/p3_$k.jsonl 10 300   # when a CANDIDATE is left
done
python3 witness65499.py work/sc_016.jsonl work/p3_016.jsonl work/w65499.jsonl 12 1 20000
# merge in stage order, see below
PYTHONPATH=$C python3 $C/verify.py 3 6 census_3x6.jsonl.gz
python3 verify_sofic.py 3 6 census_3x6.jsonl.gz
```

**Merge order.** `merge.py` keeps the last record per id, so the files must be given in the order the stages ran.
The census was built with

```
python3 $C/merge.py census_3x6.jsonl work/r36_0*.jsonl -- work/sc_0_9.jsonl work/sc_01*.jsonl \
  -- work/p2_0_9.jsonl work/p2_01*.jsonl -- work/p3_0_9.jsonl -- work/fw_0_9.jsonl work/fw_01*.jsonl \
  -- work/p3_010.jsonl work/p3_015.jsonl work/p3_016.jsonl -- work/w65499.jsonl
```

In this command, `sc_0_9`, `p2_0_9`, `p3_0_9` and `fw_0_9` are the chunk 0-9 outputs, concatenated. `w65499.jsonl` is
the output of `witness65499.py work/sc_016.jsonl work/p3_016.jsonl work/w65499.jsonl 12 1 20000`. The work files are
not committed. `census_3x6.jsonl.gz` is the result.
