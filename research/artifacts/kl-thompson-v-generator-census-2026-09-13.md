# Kervaire--Laudenbach census over Thompson's V: generator words of variable length 6 and 7 (2026-09-13)

Lane `hl-kl-counterexample`. The goal was a certified violation of
`kervaire-laudenbach-nonsingular-conjecture`. The coefficient group is
Thompson's group V, where a violation would also certify non-hyperlinearity
(`thompson-v-not-hyperlinear-from-kl-violation`). No violation was found.

- The collapse test is exact when it succeeds and says nothing when it
  overflows, so overflow is never read as injectivity.
- Injectivity is claimed only for words carrying an exact certificate
  (Section 4).

## 1. Census

A word is a cyclic sequence of syllables `g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1))`.

- **Exponents:** every `e_i = +-1`, since powers are split.
- **Coefficients:** `g_i` in `{1, a, b, B, c}`, where `a = (00 01)`, `b = (01 10 11)`,
  `c = (1 00)` are the Bleak--Quick generators and `B = b^(-1)`.
- **Cyclic reduction:** `g_i != 1` whenever `e_(i-1) != e_i`.
- **Length and degree:** variable length `n in {6, 7}`, degree `m = sum e_i` with `0 < m < n`.
  One-sign words are covered by Levin's positive-equation theorem, and
  `t -> t^(-1)` handles `m < 0`.
- **Classes:** words are identified up to rotation and `w -> sigma(w^(-1))`, where
  `sigma : t <-> t^(-1)`. Both preserve injectivity through an automorphism of `V * <t>` fixing V.

Script: `experiments/kl-thompson-v-census/census2.py`, md5 `6e13dc01071bcfcbc4618ecb85f09b66`.
MSI job 731537.

**Filters applied in the census (exact):**

1. **FINITE.** The coefficient support lies in `<a,b>` (order 24), `<a,c>` (order 6)
   or `<b,c>` (order 60). The orders were computed by closure in `vgroup.py`.
   - A failure localizes to the coefficient subgroup
     (`kl-failure-localizes-to-the-coefficient-subgroup`).
   - Finite groups are hyperlinear (`kervaire-laudenbach-holds-for-hyperlinear`).
2. **R4.** At least four light same-sign corners
   (`kl-four-same-sign-corner-words-inject`, item 1).

| n | m | classes | FINITE | R4 | kept |
|---|---|---|---|---|---|
| 6 | 2 | 10006 | 4382 | 756 | 4868 |
| 6 | 4 | 5050 | 2332 | 744 | 1974 |
| 7 | 1 | 83606 | 27872 | 960 | 54774 |
| 7 | 3 | 57390 | 19802 | 960 | 36628 |
| 7 | 5 | 25150 | 9290 | 960 | 14900 |
| total | | 181202 | 63678 | 4380 | 113144 |

## 2. Collapse test

- **Criterion.** V is infinite and simple, so by
  `kl-simple-failure-leaves-only-the-cyclic-quotient` V dies in
  `V_w = (V * <t>)/<<w>>` iff `V_w = <t>`, i.e. iff `[V_w : <t>] = 1`.
- **Method.** Todd--Coxeter coset enumeration (GAP 4.13.1,
  `CosetTableFromGensAndRels`) over `<t>`, using:
  - the nine Bleak--Quick relators, verified exactly for the generators by `vgroup.py`;
  - plus `w`.
- **Reading the output.** A closing enumeration of index 1 is a certificate of violation.
  An overflow at the coset budget certifies nothing.

**Calibration** (MSI jobs 730440 and 731540):

| control | word | expected | result |
|---|---|---|---|
| C1 | `taTB` (degree 0) | 1 | 1 |
| C2 | `taTcBc` (degree 0) | 1 | 1 |
| C6 | `tabTc` (needs long relators) | 1 | 1 |
| C7 | `tababTB` | 1 | 1 |
| C8 | `tbcTa` | recorded | 1 |
| C3 | `atbTatBt`, coefficients in `S4` | overflow | overflow |
| C4 | `atcTatct`, coefficients in `S3` | overflow | overflow |
| C5, C9 | `atbTctatBTctcT` | overflow | overflow at 100000 and 200000 |

- **Production run.** Job array 731591: 40 tasks, coset budget 200000, all 113144 kept words.
- **Result:** none of the `113144` enumerations collapsed V. All `40` tasks `COMPLETED` with `DONE`, and every word overflowed at `200000` cosets. Per-word time: min `272` ms, median `298` ms, p99 `2158` ms, max `2774` ms, total `43276` s. See `experiments/kl-thompson-v-census/collapse_summary.txt`; the concatenated results have md5 `eef38dc09b7e91c566cc4e55ac3b5c34`.

## 3. What the collapse run does not show

Overflow at 200000 cosets is consistent with violations that only close
at larger budgets, and with every kind of injective word. The run supports
no claim about the census beyond "no collapse certificate within budget".

## 4. Exact injectivity certificates

Script: `experiments/kl-thompson-v-census/certify.py`, md5 `abd5af532788e5316b312e9101dd8707`.

- **POWER.** `n = 6` and `w = u^k` (`k >= 2`), with `u` of variable length at most 3 and nonzero
  degree. `V -> V_u` is injective by `kl-length-at-most-five-equations-are-solvable`, and
  it factors through `V -> V_w`.
- **CORNER3.** `r = 3` and conditions (D4), (A2) of `kl-four-same-sign-corner-words-inject`
  item 2, checked exactly in V.
  - Every reduced closed path is tested in both product orders.
  - Loop labels are compared with a path label and with its inverse.

  So the test is at least as strict as the weight proof requires: D4 is used only on
  all-light 4-cycles, and A2 only on light length-two labels, a set closed under inversion.
- **RETRACT.** There is `t_0 in V` with `w^delta(t_0) = 1` exactly, where `delta = delta_k`
  is the diagonal embedding of V over a complete prefix code of size `k`.
  - The homomorphism `V * <t> -> V`, `g -> delta(g)`, `t -> t_0` kills `w`.
  - It restricts to the injective `delta` on V, so `V -> V_w` is injective.
  - No theorem is needed beyond this retraction argument.

**Candidate radius.** On a fixed sample of 400 kept words (every 283rd line of
`survivors67.txt`), the pilot results were identical at all three radii:

| radius | ball size | candidates for k = 1, 2, 3, 4 | CORNER3 | RETRACT | loop time |
|---|---|---|---|---|---|
| 4 | 98 | 98, 166, 522, 648 | 57 | 8 | 5.1 s |
| 6 | 532 | 532, 890, 2742, 3216 | 57 | 8 | 26.8 s |
| 8 | 2770 | 2770, 4504, 13134, 15336 | 57 | 8 | 112.4 s |

(MSI jobs 736321, 736322, 736360.) Production used radius 6, as job array 736359
over all theorem-uncertified words.

**Totals.**
- `theorems_out.txt`: md5 `86bb744f28a0d35e1fde19ebfd70b53f`, MSI job 736336.
- `retract_all.txt`: md5 `2141d00907090ce99fbce636440c5a1a`, job array 736359, every task ended `DONE`.

| certificate | classes |
|---|---|
| FINITE (census) | 63678 |
| R4 (census) | 4380 |
| POWER | 6 |
| CORNER3 | 15204 |
| RETRACT | 2164 |
| **certified** | **85432** |
| FRONTIER | 95770 |

- **CORNER3** covers only `n = 7` words with `r = 3`: `7236` at `m = 1`, `5616` at `m = 3`, `2352` at `m = 5`.
- **RETRACT splits by `k`:** `2152` at `k = 1` and `12` at `k = 3`.
- **Trivial retractions:** `1280` of the certificates use `t_0 = 1`, i.e. the coefficient product is
  already trivial in V.
- **Re-verification.** Every RETRACT certificate was re-verified by `verify_retract.py`
  (md5 `06d854475cb394e4154ace8bb28418d5`), which checks complete prefix codes and the exact
  product. Output: `verified 2164 RETRACT certificates`.
- **Tamper check.** One `t`-letter flipped in one certificate makes the verifier fail with exit 1.
- **Data:** `experiments/kl-thompson-v-census/retract_certificates.txt`
  (md5 `dde049fe675f43091829cc5ffe9feac0`, 2164 lines).

RETRACT certificates by class:

| n | m | r=0 | r=1 | r=2 | r=3 |
|---|---|---|---|---|---|
| 6 | 2 | 23 | 2 | 106 | - |
| 6 | 4 | 6 | 2 | 42 | - |
| 7 | 1 | 16 | 392 | 18 | 556 |
| 7 | 3 | 14 | 289 | 50 | 392 |
| 7 | 5 | 11 | 77 | 30 | 138 |

## 5. Frontier

Frontier words by class, `frontier_final.txt`, md5 `f080ad7195d2b0bd76ac7ebb4feffb58`, 95770 lines:

| n | m | r=0 | r=1 | r=2 | r=3 | total |
|---|---|---|---|---|---|---|
| 6 | 2 | 629 | 218 | 3884 | - | 4731 |
| 6 | 4 | 164 | 214 | 1546 | - | 1924 |
| 7 | 1 | 1492 | 25542 | 2626 | 16896 | 46556 |
| 7 | 3 | 1180 | 13533 | 2594 | 12960 | 30267 |
| 7 | 5 | 539 | 4165 | 2614 | 4974 | 12292 |

**Reproducing the list.** The list is not landed, because it is 1.9 MB. It is reproduced
deterministically by:

```text
census2.py 6,7 survivors67.txt
certify.py survivors67.txt theorems_out.txt -1 1
certify.py <FRONTIER lines> <out> 6 1,2,3,4
```

Keep the `FRONTIER` lines of the last output. `survivors67.txt` has md5 `57b19f07f9f077fcd90d22c18b0e9f53`.

**Where the frontier is.**
- `n = 7`, `r = 1`: one light corner and three heavy ones.
- `n = 7`, `r = 3` failing (D4) or (A2): products of two generators have orders 3, 4 or 5,
  so short light cycles with trivial label are common.
- `n = 6`, `r = 2`.

**Unused length-six theorems.** None of these was implemented here:
- `kl-length-six-one-coincidence-words-inject` and `kl-length-six-four-sign-change-words-inject`
  need an infinite-order product of two labels, which never occurs with generator labels;
- the torsion-residue theorems (`kl-three-equal-residue-shapes-inject-for-every-loop-order`,
  `kl-involution-loop-residue-with-interior-light-label-injects`,
  `kl-even-syllable-words-reduce-to-shorter-equations`) need the normalization `t -> t u^(-1)`,
  which was not implemented.

So some `n = 6` frontier words may already be covered on main.

## 6. Provenance

- **Reused unchanged from an earlier lane.** `klcx.g` (md5 `99e3e3a43a4819dca465d0a1bf18efaf`),
  `vgroup.py` (md5 `5a57c59b59c97fe27ba02d9774f1d135`), `calib.g` and calibration job 730440 were
  written by `solve-kl-counterexample-search`. That lane died before landing; the files come from
  `/scratch.global/sauer354/solve-kl-counterexample-search/`, and its GAP 4.13.1 build is the one
  used here.
- **Written by this lane:** census version 2, calibration 2, certification, verification, and all
  production runs.

## 7. Trust surface

- **Bleak--Quick presentation of V.** As quoted on main in
  `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`. The generators satisfy the nine relators
  exactly (`vgroup.py`), but completeness of the presentation is imported.
- **GAP coset enumeration.** Enters only a positive collapse verdict, and none occurred.
- **Theorems used by POWER and CORNER3.** Status from `cairn why`: `kl-four-same-sign-corner-words-inject`, `kl-length-at-most-five-equations-are-solvable`, `kl-failure-localizes-to-the-coefficient-subgroup` and `kervaire-laudenbach-holds-for-hyperlinear` all read ESTABLISHED with every leaf ✓ (`cairn why`, MSI clone at 5b5d26714).
- **RETRACT certificates.** Each `t_0` is re-verified by exact tree-pair multiplication.
  The point test only prunes candidates.
