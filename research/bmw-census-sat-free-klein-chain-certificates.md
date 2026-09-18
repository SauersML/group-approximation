---
rg: 2
id: bmw-census-sat-free-klein-chain-certificates
kind: claim
title: Thirty-three all-involution BMW census classes of degrees (4,3), (5,3) and (4,4), including all five (4,4) letter-ball SAT survivors, have parity kernels refuted by a cycle of four Klein-bottle relations between pure words, with no SAT solver
distinct_from:
  bmw-degree-44-53-parity-kernels-not-left-orderable: that is the census theorem, proved by positive-cone SAT refutations and excluding three (4,4) classes; this gives solver-free Klein-chain certificates for 33 classes, including the three it excludes and #176, #256 which needed the large SAT runs
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that is the SAT census of degrees (3,3), (4,3) and torsion-free (4,4); this gives a different, solver-free certificate for one (4,3) class, and more beyond
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the statement for #193, #281, #332 (reducible or not left-orderable); this proves non-left-orderability of their parity kernels as part of a wider list, independent of reducibility
  bmw-40-40-193-281-332-parity-kernels-not-left-orderable: that is the statement for the three survivors alone; this contains it and extends the same Klein-chain method to 30 more classes
artifacts:
  - experiments/bmw-klein-chains-2026-09-17/README.md
  - experiments/bmw-klein-chains-2026-09-17/chains_census_40_30.json
  - experiments/bmw-klein-chains-2026-09-17/chains_census_50_30.json
  - experiments/bmw-klein-chains-2026-09-17/chains_census_40_40.json
  - experiments/bmw-klein-chains-2026-09-17/verify_klein.py
  - experiments/bmw-klein-chains-2026-09-17/verify_census_40_30.log
  - experiments/bmw-klein-chains-2026-09-17/verify_census_50_30.log
  - experiments/bmw-klein-chains-2026-09-17/verify_census_40_40.log
  - experiments/bmw-klein-chains-2026-09-17/kpure.py
  - experiments/bmw-census-left-orders-2026-09-17/census_40_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_50_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
---

**Setting.** A class `c` of `census_{m}0_{n}0.json` in `experiments/bmw-census-left-orders-2026-09-17/`
has `m` horizontal letters `h_i` and `n` vertical letters `v_j`, all involutions (`pA = pB = 0`). It
also has one square `h v = v' h'` for each pair `(h, v)`. The group is
`Γ_c = ⟨h_i, v_j | letters², the m·n squares⟩`, and its parity kernel `Γ_c^+` is the index-4
subgroup of words with an even number of `v`-letters and an even number of `h`-letters.

**Claim.** For each class listed below, `Γ_c^+` contains nontrivial elements `x_1, x_2, x_3, x_4`
with `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` (indices mod 4). Consequently `Γ_c^+` is not
left-orderable. In each chain, two of the `x_i` are freely reduced words in the `v`-letters alone, the
other two are freely reduced words in the `h`-letters alone, and each has even length at most 8.

| pattern | classes with a chain | classes scanned |
|---|---|---|
| `40_30`, degree (4,3) | #55 | 27 |
| `50_30`, degree (5,3) | #55, #240, #241, #242, #243, #258, #430 | 190 |
| `40_40`, degree (4,4) | #31, #175, #176, #177, #193, #205, #220, #232, #233, #253, #255, #256, #261, #262, #263, #264, #272, #281, #282, #290, #318, #320, #332, #338, #552 | 301 |

The scanned classes are the census classes for which at least one automaton image is not certified
finite (`finH` or `finV` is `null` in `out_X.jsonl`). The chains are listed in
`experiments/bmw-klein-chains-2026-09-17/chains_census_X.json`.

**What is new.**
- **No SAT solver.** Each certificate is four elements and four group identities. Each identity is
  checked by rewriting with the census squares, and the full traces are in `verify_census_X.log`.
  The only other input is one elementary lemma about left orders.
- **The hard (4,4) survivors are covered.**
  - `40_40` #193, #281 and #332 stay satisfiable in every census and large-ball SAT instance, and
    they are the classes excluded from `bmw-degree-44-53-parity-kernels-not-left-orderable`.
  - `40_40` #176 and #256 stay satisfiable through `R8s2` and were refuted only by the large SAT runs.
  - All five are in the list.
- **One (5,3) survivor is covered.** `50_30` #258 stays satisfiable through `R8s2` and is in the list.
  The other one, #470, has no chain of this form with all words of length at most 8.

**Scope.** The claim is about the listed classes only.
- The absence of a chain up to length 6 (length 8 for #176 and #470) is a finite search result, not an
  obstruction to left orders.
- Patterns with transposed letter pairs (`pA > 0` or `pB > 0`, such as `51_30`) are not treated.

The proof is `bmw-census-sat-free-klein-chain-certificates-proof`.
