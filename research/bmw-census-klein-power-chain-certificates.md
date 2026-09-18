---
rg: 2
id: bmw-census-klein-power-chain-certificates
kind: claim
title: Solver-free Klein-power chain certificates refute left orders on the parity kernels of 50_30 #470, of 167 census classes with transposed letter pairs, and of three reducible Promislow-type classes
distinct_from:
  bmw-census-sat-free-klein-chain-certificates: that gives four-term chains of pure Klein relations for 33 all-involution classes and finds none for 50_30 #470; this adds power steps, certifies #470, and treats the patterns with transposed letters that it leaves out
  bmw-degree-44-53-parity-kernels-not-left-orderable: that is the census theorem, proved by positive-cone SAT refutations (for #470 the radius-8 instance with one factor of length at most 4, 11045771 clauses); this gives solver-free certificates for #470 and for the listed classes
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that is the SAT census of degrees (3,3), (4,3) and torsion-free (4,4); this gives solver-free certificates for the listed transposed-letter classes of those degrees
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the open statement for 40_40 #193, #281, #332; this does not touch those three classes, whose parity kernels already have pure Klein chains
artifacts:
  - experiments/bmw-klein-chains-transposed-2026-09-17/README.md
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_klein2.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/crosscheck2.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpure2.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/collect.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/run_P6.sh
  - experiments/bmw-klein-chains-transposed-2026-09-17/resume_P6.sh
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_41_30.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_41_31.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_41_40.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_41_41.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_42_30.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_42_31.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_42_40.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_42_41.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_42_42.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_50_30_470.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_50_31.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_51_30.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_51_31.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_52_30.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/chains_52_31.json
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_41_30.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_41_31.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_41_40.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_41_41.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_42_30.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_42_31.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_42_40.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_42_41.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_42_42.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_50_30_470.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_50_31.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_51_30.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_51_31.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_52_30.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_52_31.log
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_31_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_31_30_L8.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_31_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_31_31_L8.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_41_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_41_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_41_40_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_41_41_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_42_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_42_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_42_40_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_42_41_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_42_42_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_50_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_51_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_51_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_52_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_52_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_red_41_40_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_red_41_41_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_red_51_30_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp2_red_51_31_L6.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/kpp_470.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_31_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_31_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_31_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_31_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_41_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_41_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_41_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_41_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_41_40.json
  - experiments/bmw-census-left-orders-2026-09-17/out_41_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_41_41.json
  - experiments/bmw-census-left-orders-2026-09-17/out_41_41.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_42_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_42_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_42_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_42_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_42_40.json
  - experiments/bmw-census-left-orders-2026-09-17/out_42_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_42_41.json
  - experiments/bmw-census-left-orders-2026-09-17/out_42_41.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_42_42.json
  - experiments/bmw-census-left-orders-2026-09-17/out_42_42.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_50_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_50_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_50_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_50_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_51_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_51_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_51_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_51_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_52_30.json
  - experiments/bmw-census-left-orders-2026-09-17/out_52_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/census_52_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_52_31.jsonl
---

**ESTABLISHED (computer-certified: explicit group identities, each checked by rewriting with the census
squares; full traces logged, and re-checked by a second normal-form algorithm; no SAT solver).** Proof:
`bmw-census-klein-power-chain-certificates-proof`.

**Setting.** A class `c` of `census_{m}{pA}_{n}{pB}.json` in
`experiments/bmw-census-left-orders-2026-09-17/` has `m` horizontal letters and `n` vertical letters.
- `pA` of the horizontal letters pairs are transposed, `h^{-1} = h_{iA[h]}`; the rest are involutions.
  Likewise `pB` and `iB` for the vertical letters.
- For each pair `(h, v)` there is one square `h v = v' h'`.
- `Γ_c` is the group with these generators and relations. Its parity kernel `Γ_c^+` (even `v`-length and
  even `h`-length) has index 4 and is torsion-free.

**Claim.** For each class listed below, `Γ_c^+` contains nontrivial elements `x_0, …, x_{k-1}` such that,
for every `i` (mod `k`), one of the following holds, and (K) holds for at least one `i`:
- **(K)** `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}`;
- **(R)** `x_i = r^e` and `x_{i+1} = r^f` for some `r ∈ Γ_c^+` and `1 ≤ |e| < |f|`.

Consequently `Γ_c^+` is not left-orderable, and hence neither is `Γ_c`.

In a left order with `|g| = max(g, g^{-1})`, (K) forces `|x_i| < |x_{i+1}|` and (R) forces
`|x_i| ≤ |x_{i+1}|`, so the cycle gives `|x_0| < |x_0|`.

**`50_30` #470.** The chain has six elements, with `u = v_0 v_1` and `t = h_0 h_1 h_0`:

| `i` | `x_i` | step to `x_{i+1}` |
|---|---|---|
| 0 | `v_2 u v_2 = v_2v_0v_1v_2` | (R), root `x_0`: `x_1 = x_0^2` |
| 1 | `v_2v_0v_1v_0v_1v_2` | (K) |
| 2 | `t h_2 h_4 t` | (K) |
| 3 | `v_0v_2v_0v_1v_2v_0` | (R), root `x_3`: `x_4 = x_3^2` |
| 4 | `v_0v_2v_0v_1v_0v_1v_2v_0` | (K) |
| 5 | `t h_3 h_2 t` | (K) |

- This is the first certificate for #470 that uses no SAT solver.
- All six words are pure (a word in one family), of length at most 8.
- The proof checks the four (K) identities by hand.
- #470 has no chain of pure (K) steps alone up to length 8, so the power steps are needed.
- The mechanism is Promislow-type: `x_2` inverts `x_1 = x_0^2` but not `x_0`.

**Transposed-letter patterns.** The table lists the classes with a certificate. "Scanned" counts the
candidate classes, which are the classes not certified reducible (`finH` or `finV` is `null` in
`out_X.jsonl`).

| pattern | degree | classes with a certificate | certified / scanned |
|---|---|---|---|
| `31_30` | (3,3) | — | 0 / 1 |
| `31_31` | (3,3) | — | 0 / 1 |
| `41_30` | (4,3) | #55, #138, #159 | 3 / 12 |
| `41_31` | (4,3) | #99 | 1 / 7 |
| `41_40` | (4,4) | #150, #165, #182, #226, #366, #381, #398, #470, #471, #472, #473, #474, #475, #476, #478, #487, #527, #572, #579, #590, #591, #593, #601, #609, #628, #642, #782, #797, #814, #856, #857, #859, #867, #875, #933, #976, #980, #981, #1000, #1013, #1085, #1087, #1106, #1107, #1109, #1118, #1161, #1162, #1163, #1164, #1165, #1166, #1167, #1168, #1186, #1193 | 56 / 222 |
| `41_41` | (4,4) | #422, #423, #424, #425, #427, #446, #447, #468, #469, #494 | 10 / 60 |
| `42_30` | (4,3) | #61 | 1 / 2 |
| `42_31` | (4,3) | #69 | 1 / 2 |
| `42_40` | (4,4) | #157, #159, #288, #290, #291, #292, #345, #348, #378, #385, #508 | 11 / 52 |
| `42_41` | (4,4) | #448, #449, #452, #453, #463, #464, #466, #468, #497 | 9 / 46 |
| `42_42` | (4,4) | #102 | 1 / 8 |
| `50_31` | (5,3) | #45, #82, #149, #150, #222, #230, #233, #247 | 8 / 43 |
| `51_30` | (5,3) | #14, #16, #58, #60, #66, #68, #70, #71, #133, #135, #137, #139, #165, #166, #187, #207, #209, #211, #212, #213, #239, #240, #261, #311, #313, #315, #317, #343, #344, #364, #383, #385, #428, #430, #432, #434, #460, #461, #482, #512, #532, #534, #536, #537, #538, #564, #565, #585, #593, #604, #606, #607, #629, #631 | 54 / 129 |
| `51_31` | (5,3) | #253, #263, #282, #288, #295 | 5 / 40 |
| `52_30` | (5,3) | #91, #222, #223, #224, #292 | 5 / 38 |
| `52_31` | (5,3) | #170, #171 | 2 / 18 |
| total | | | 167 / 681 |

**Reducible classes.** `bmw-degree-44-53-parity-kernels-not-left-orderable` lists eleven reducible
"Promislow-type" classes, refuted there by radius-4 SAT instances. Three of them also have certificates:
`41_40` #1174 (7 elements) and `41_41` #486 (12 elements) and #541 (7 elements). They are included in
`chains_41_40.json` and `chains_41_41.json`.

**Scope.** The claim is about the listed classes only.
- The absence of a certificate for a class is a finite search result (pure words of length at most 6,
  or 8 where stated in the proof), not an obstruction.
- `31_30` #26 and `31_31` #12 have no pure inverting pair at all up to length 8. By Theorem 4 of the
  proof, every Klein pair in `Γ^+` is `Γ`-conjugate to a pure pair. So in these two parity kernels,
  every Klein pair is conjugate to a pure pair of length greater than 8, and the method gives nothing
  for them at that length.
- The three `40_40` survivors #193, #281, #332 are already covered by
  `bmw-census-sat-free-klein-chain-certificates`. The open question for them in
  `bmw-44-sat-survivor-parity-kernels-not-left-orderable` is not changed here.

**Structural fact (proved in §5 of the proof).** If `a b a^{-1} = b^{-1}` with `b ≠ 1` in `Γ^+`, then
some `g ∈ Γ` conjugates `b` into a pure word of one family and `a` into a pure word of the other. So
along a certificate, the (K) steps alternate between `v`-type and `h`-type elements.

The proof is `bmw-census-klein-power-chain-certificates-proof`.
