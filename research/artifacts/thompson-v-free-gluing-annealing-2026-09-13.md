# Thompson V: annealing free S4/S3 gluings against a planted control

Date: 2026-09-13. Lane `solve-v-collapse`. All computation ran on MSI (agsmall, one core per task).
Code and raw result lines are in `experiments/thompson-v-models/`:
- `vanneal.c`, `vanneal.sbatch`, `results_vanneal_710071.txt`;
- `vglue.c`, `vglue.sbatch`, `gen_ctrl.py`, `rel_V.txt`, `rel_CTRL.txt`, `results_vglue_712174.txt`;
- `amalgam_orders.py`.

This follows `thompson-v-model-probes-2026-09-12.md` and `thompson-v-hs-probe-calibration-2026-09-12.md`.
There, plain annealers never found planted permutation models at `n = 120, 240`, so their plateaus
carry no information.

## 1. Presentation and search space

- **Presentation.** This uses Bleak--Quick (2.4), with `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)`.
  - By `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, `V = (S4 *_<a> S3) / <<r5, r6, r7, r8>>`.
  - `amalgam_orders.py` gives orders 24 and 6 by coset enumeration.
  - As a sanity check, the ten words `(2.4)`, `c^2` and `(ac)^3` fix 4000 random strings.
- **Search space.** By `thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words`, `V` is sofic
  exactly when free gluings exist whose long-word defect tends to `0`. Such gluings of size `L` are
  `(a_0, b_0, nu^-1 c_0 nu)` with `nu` in `C(a_0) = C2 wr S_(L/2)`.
- **Equivalent test words.** (2.3) and (2.4) share their first four relators and have the same
  normal closure. So on free gluings, the four long words and the four remaining relations of (2.3)
  (one splitting relation, three commutation relations) have mutually bounded defects.

## 2. Round 1: plain annealer over (a, b, c) (`vanneal.c`, job 710071)

**Setup.**
- `a` and `c` are fixed-point-free involutions and `b` is fixed-point-free of order 3, with
  `6 | k`.
- A move conjugates one generator by a random transposition.
- The cost is the mean fraction of points moved by `(ab)^4`, `c^-1(ac)^2 a`, `r5`, `r6`, `r7`, `r8`.
- Each run takes `4 * 10^6` steps with geometric cooling from 0.05 to 0.0005, over 6 seeds.

| k | best mean defect | `(ab)^4`, `c^-1(ac)^2a` at best | `r5..r8` at best |
| --- | --- | --- | --- |
| 12 | 0.458 (all seeds) | 0, 0 | 0.33, 0.75, 0.83, 0.83 |
| 24 | 0.431 (all seeds) | 0, 0.33 | 0, 0.75, 0.50, 1.00 |
| 48 | 0.455--0.587 | 0, at most 0.17 | 0.33--0.96 |
| 96 | 0.606--0.628 | 0, 0 | 0.88--0.98 |
| 192 | 0.635--0.647 | 0, 0 | 0.92--0.99 |
| 384 | 0.868--0.898 | 0.85--0.90, 0.39--0.56 | 0.98--1.00 |

- **Under-run at the top.** At `k = 384` the annealer does not even satisfy `(ab)^4`.
- **No trend.** From `k = 96` on, `r5..r8` sit near the level of random permutations.

## 3. Round 2: exact free gluings (`vglue.c`, job 712174)

**Setup.**
- `24 | k`. `a` is the pairing `x <-> x xor 1`, and `b`, `c` are free `S4`- and `S3`-structures.
- The start is a random `nu in C(a_0)`. A move conjugates `c` by a pair flip, a pair swap or a
  crossed pair swap, each an involution commuting with `a`.
- `a^2, b^3, (ab)^4, c^2, (ac)^3` hold exactly, and `a, b, c` are fixed-point-free. Each run checks
  both (`short_bad=0 fpf=1` in every log line).
- The cost is the mean fraction of points moved by the four words of the relator file. Each run
  takes `3 * 10^6` steps from 0.05 to 0.0005, over 3 seeds.

**Planted control** (`gen_ctrl.py`, seed 1).
- In `S5`, `a = (0 1)`, `b = (1 2 3)`, `c = (0 4)` generate `S5`, with `<a,b> = S4` and
  `<a,c> = S3` meeting in `<a>`.
- The control words are four reduced words `u w^-1` of lengths 26, 28, 26, 37, the lengths of
  `r5..r8`. In each, `u` and `w` are random words with equal value in `S5`, so the word is trivial
  in `S5`.
- A free `S5`-set of size `120m` is an exact free gluing for the control. The `V` words are
  nontrivial in `S5`.

| k | V: best mean defect | CTRL: best mean defect | random start, both sets |
| --- | --- | --- | --- |
| 48 | 0.849--0.880 | 0.000, 0.000, 0.667 | 0.94--0.98 |
| 120 | 0.927--0.931 | 0.823--0.888 | 0.97--1.00 |
| 240 | 0.950--0.963 | 0.901--0.923 | 0.98--1.00 |
| 480 | 0.988 (all seeds) | 0.980--0.981 | 0.99--1.00 |
| 960 | 0.995 | 0.993 | 1.00 |

- **Calibrated only at k = 48.** Two of three control runs found exact gluings of size 48. These
  are not the planted `S5` models, since 120 does not divide 48: the control group has other finite
  actions. No run found the planted model at `k = 120` or `240`.
- **Beyond that the plateau is uninformative.** From `k = 120` on, both sets approach the random
  level together, and the annealer misses existing exact models there.
- **The one forced gap.** At `k = 48`, V's best stays above the control's. Nothing more can be read
  from this: `V` is infinite and simple, so no free gluing satisfies all four words exactly.
- **Stronger than the plain parametrization.** It solves a control exactly at `k = 48` and keeps
  the short relators exact at every `k`.

## 4. What this shows

- **No signal toward soficity.** No free gluing with small long-word defect appears at `k <= 960`.
- **No evidence for collapse.** The only calibrated size is 48, where a positive defect is forced.
- **Next useful computation.** A search that solves the planted control at `k = 120` and `240` from
  random starts, for example constructive coset-table filling, or tempering with incremental cost
  updates. Only then can a `V` plateau be read.

## 5. Exact gap

- **Nonsoficity.** `V` is nonsofic exactly when there is `epsilon_0 > 0` such that, for all `L` and
  all `nu in C2 wr S_(L/2)`, one of `r5..r8` moves at least `epsilon_0 L` points of
  `(a_0, b_0, nu^-1 c_0 nu)`.
- **Soficity.** `V` is sofic exactly when there are `nu` with all four defects `o(L)`.
- **Rounding and gluing on the finite subgroups is complete, and it carries no obstruction.** It
  removes `S4` and `S3` exactly, and every remaining difficulty sits in the four words. No
  lower-bound mechanism for them is recorded:
  - there is no infinite Kazhdan subgroup to use;
  - spatial and Følner ansätze are fenced;
  - the Loeb support calculus gives no contradiction (`thompson-v-not-sofic`, Attempts).
