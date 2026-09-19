---
rg: 2
id: bmw-quaternionic-char3-type-44-parity-kernels
kind: claim
title: Nine degree-(4,4) BMW classes (40_40 #818, 41_40 #1182, 42_40 #472, #535, 42_41 #318, #500, #533, 42_42 #97, #114) embed in the constant quaternion algebra (−1, t+1) over F_3(t) with both trees Bruhat–Tits trees at t and t−1; their parity kernels have no Klein pair and are refuted by solver-free cone trees
distinct_from:
  bmw-quaternionic-type-53-parity-kernels: that is characteristic 2 (degrees (5,3) and (3,3)); this is characteristic 3, degree (4,4), with residue field F_3 on both trees
  bmw-40-40-281-is-irreducible: that proves irreducibility of the single class 40_40 #281 by a semilinear Möbius model over F_3((s)); the classes here are different and the model is an S-arithmetic embedding into PGL_2 of a quaternion algebra, which also gives torsion-freeness and excludes Klein pairs
  bmw-census-klein-power-chain-certificates: the classes here embed in PGL_2 of a field, so no Klein-power chain exists for them
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/README.md
  - experiments/bmw-cone-trees-2026-09-18/findquat3.py
  - experiments/bmw-cone-trees-2026-09-18/fpoly.py
  - experiments/bmw-cone-trees-2026-09-18/quatp.py
  - experiments/bmw-cone-trees-2026-09-18/runquat3.sh
  - experiments/bmw-cone-trees-2026-09-18/quat3_44.jsonl
  - experiments/bmw-cone-trees-2026-09-18/runquat3b.sh
  - experiments/bmw-cone-trees-2026-09-18/quat3b_44.jsonl
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep3.py
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep3.log
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
  - research/bmw-quaternionic-char3-type-44-parity-kernels-proof.md
---

**ESTABLISHED.** The proof is in `bmw-quaternionic-char3-type-44-parity-kernels-proof`. Its finite
inputs are the polynomial identities of nine representations and nine cone trees. They are checked
exactly by `verify_quat_rep3.py` (sympy over `GF(3)`) and by `verify_cone.py`.

Let `Γ` be the BMW group of one of the classes `40_40` #818, `41_40` #1182, `42_40` #472,
`42_40` #535, `42_41` #318, #500, #533 and `42_42` #97, #114, from
`experiments/bmw-census-left-orders-2026-09-17/census_<pattern>.json`, and let `Γ^+` be its parity
kernel. All nine classes are among the survivors of `bmw-44-sat-survivor-parity-kernels-not-left-orderable`
that have no irreducibility certificate in the census and no Klein-power certificate.

## Statement

Let `K = F_3(t)` and `D = (−1, t+1)`, that is, `i² = −1`, `j² = t + 1`, `k = ij = −ji`. Then
`F_3(i) = F_9`, and `D = F_9(t) ⊕ F_9(t) j` with `j x j^{-1} = x^3`. So `D` is the cyclic algebra of the
constant extension `F_9(t)/F_3(t)` and `t+1`. It is a division algebra, ramified exactly at `t+1`
and `∞`.

1. **Representations.** There is a faithful `ρ : Γ → D^*/K^*` with letters in `O = F_3[t]⟨1, i, j, k⟩`.
   - The four h-letters fix the base vertex of the Bruhat–Tits tree at `t` and move the base vertex of
     the tree at `t − 1` to its four neighbours.
   - The four v-letters do the same with the two places exchanged.
   - Both trees are 4-regular (residue field `F_3`), and the Γ-equivariant map `T_4 × T_4 → Δ_{t−1} × Δ_t`
     is an isomorphism.

   | class | inverse pairs | h-letters (`Nrd = ±(t − 1)`) | v-letters |
   |---|---|---|---|
   | `40_40` #818 | none | `i ± j ± k` (all four signs) | `i ± j`, `i ± k` (`Nrd = −t`) |
   | `41_40` #1182 | `h_0 h_1` | `1 ± (j + k)`, `i ± (j + k)` | `(t+1) i ± k`, `(t+1) i ± j` (`Nrd = t(t+1)`) |
   | `42_40` #472 | `h_0 h_1`, `h_2 h_3` | `1 ± (i + k)`, `1 ± (i − k)` | `(t+1) i ± k`, `(t+1) i ± j` (`Nrd = t(t+1)`) |
   | `42_40` #535 | `h_0 h_1`, `h_2 h_3` | `1 ± (j + k)`, `1 ± (j − k)` | `i ± j`, `i ± k` (`Nrd = −t`) |
   | `42_41` #318 | `h_0 h_1`, `h_2 h_3`, `v_0 v_1` | `1 ± (i + k)`, `1 ± (i − k)` | `1 ± j`, `i ± j` (`Nrd = −t`) |
   | `42_41` #500 | `h_0 h_1`, `h_2 h_3`, `v_0 v_1` | `1 ± (j + k)`, `1 ± (j − k)` | `(t+1) ± k`, `(t+1) i ± k` (`Nrd = t(t+1)`) |
   | `42_41` #533 | `h_0 h_1`, `h_2 h_3`, `v_0 v_1` | `1 ± (i + k)`, `1 ± (i − k)` | `1 ± k`, `i ± k` (`Nrd = −t`) |
   | `42_42` #97 | `h_0 h_1`, `h_2 h_3`, `v_0 v_1`, `v_2 v_3` | `1 ± (i + k)`, `1 ± (i − k)` | `(t+1) ± j`, `(t+1) ± k` (`Nrd = t(t+1)`) |
   | `42_42` #114 | `h_0 h_1`, `h_2 h_3`, `v_0 v_1`, `v_2 v_3` | `1 ± (j + k)`, `1 ± (j − k)` | `1 ± k`, `1 ± j` (`Nrd = −t`) |

   The exact assignment of letters to indices is in `verify_quat_rep3.log`.
2. **Consequences.**
   - `Γ` is irreducible.
   - `Γ^+` is torsion-free and has no pair `a b a^{-1} = b^{-1}` with `b ≠ 1`, pure or conjugate, of any
     length.
   - `Γ^+` contains no `BS(p, q)` with `p ≠ q`, and no Klein-power chain certifies it.
3. **Not left-orderable, without a solver.** `trees.jsonl.gz` holds a radius-4 cone-propagation tree
   for each class. It refutes every positive cone on `Γ^+`, and `verify_cone.py` checks it.

   | class | leaves | product steps |
   |---|---|---|
   | `40_40` #818 | 10 | 238 |
   | `41_40` #1182 | 14 | 341 |
   | `42_40` #472 | 10 | 259 |
   | `42_40` #535 | 8 | 232 |
   | `42_41` #318 | 14 | 385 |
   | `42_41` #500 | 8 | 184 |
   | `42_41` #533 | 8 | 180 |
   | `42_42` #97 | 14 | 360 |
   | `42_42` #114 | 8 | 165 |

## Where the family ends

`runquat3.sh` ran the strict search (letters of coordinate degree at most 1 whose `Nrd` is supported
on `{t, t−1, t+1}`) in `D`. It covered all 75 remaining `(4,4)` classes that pass the local-action filter,
and found only these nine. For this algebra, order and pair of places the search is exhaustive
(proof §5).

`runquat3b.sh` ran the same search on the filter-failing classes, with 1200 s per pattern. It completed
222 of the 502 such classes (all of `42_40`, `42_41`, `42_42`; 92 of `41_40`, 21 of `41_41`, 45 of
`40_40`) and found nothing, so the filter lost no model there.

Two other algebras were also tried, `(t+1, 2t²+2t+1)` and `(t+1, 2t²+2)`. In neither of them does the
strict search find any h-letter candidate with coordinates of degree at most 1.

The remaining patterns, and the filter-failing classes, are recorded in the `## Attempts` of
`bmw-44-sat-survivor-parity-kernels-not-left-orderable`.
