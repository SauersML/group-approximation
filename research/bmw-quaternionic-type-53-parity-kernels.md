---
rg: 2
id: bmw-quaternionic-type-53-parity-kernels
kind: claim
title: Six degree-(5,3) BMW classes embed in the constant quaternion algebra [1, t+1) over F_2(t), and 30_30 #16 in [t, t²+t+1); their parity kernels have no Klein pair and are refuted by solver-free cone trees
distinct_from:
  bmw-klein-free-quaternionic-parity-kernels: that treats 31_30 #26 and 31_31 #12 of degree (3,3) in [t, t²+t+1); this adds 30_30 #16 in the same algebra and a second family, of degree (5,3), in a different algebra with a valency-5 tree at t²+t+1
  bmw-census-klein-power-chain-certificates: that certifies classes by Klein-power cycles; the classes here embed in PGL_2 of a field, so by the PGL_2 inversion lemma they have no Klein pair and no such cycle exists
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that refutes left orders with a SAT solver; this gives the linear structure and solver-free cone certificates
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/README.md
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep2.py
  - experiments/bmw-cone-trees-2026-09-18/verify_quat_rep2.log
  - experiments/bmw-cone-trees-2026-09-18/findquat.py
  - experiments/bmw-cone-trees-2026-09-18/gf2poly.py
  - experiments/bmw-cone-trees-2026-09-18/quat.py
  - experiments/bmw-cone-trees-2026-09-18/runquat2_53.sh
  - experiments/bmw-cone-trees-2026-09-18/quat2_53.out
  - experiments/bmw-cone-trees-2026-09-18/runquat2_53b.sh
  - experiments/bmw-cone-trees-2026-09-18/quat2_53b.out
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
  - research/bmw-quaternionic-type-53-parity-kernels-proof.md
---

**ESTABLISHED.** The proof is in `bmw-quaternionic-type-53-parity-kernels-proof`. Its finite inputs
(the polynomial identities of seven representations, and seven cone trees) are checked exactly by
`verify_quat_rep2.py` (sympy over `GF(2)`) and `verify_cone.py`.

Let `Γ` be the BMW group of one of the classes below, from
`experiments/bmw-census-left-orders-2026-09-17/census_<pattern>.json`, and `Γ^+` its parity kernel.
None of them has a Klein-power certificate (`bmw-census-klein-power-chain-certificates`).

## Statement

Let `K = F_2(t)`.

1. **Family 53.** Let `D = [1, t+1)`: `i² = i + 1`, `j² = t + 1`, `j i = (i+1) j`. So `F_2(i) = F_4`,
   `D = F_4(t) ⊕ F_4(t) j` with `j x j^{-1} = x^2` on `F_4(t)`: the cyclic algebra of the constant
   extension `F_4(t)/F_2(t)` and `t+1`. It is a division algebra, ramified exactly at `t+1` and `∞`.

   For each of the classes `50_31` #243, `51_30` #660, `51_31` #279, `51_31` #309, `52_30` #386 and
   `52_31` #185 there is a faithful `ρ : Γ → D^*/K^*`, with letter coordinates of degree at most 1:
   - the five h-letters fix the base vertex of the Bruhat–Tits tree at `t` (valency 3) and move the
     base vertex of the tree at `t²+t+1` (residue field `F_4`, valency 5) to its five neighbours;
   - the three v-letters do the same with the two places exchanged.

   The Γ-equivariant map from `T_5 × T_3` to the product of the two Bruhat–Tits trees is an
   isomorphism.
2. **Family 33 (a third member of an existing family).** `30_30` #16 embeds in the same way in
   `[t, t²+t+1)`, with trees at `t` (v) and `t+1` (h). This is the algebra of
   `bmw-klein-free-quaternionic-parity-kernels`.
3. **Consequences, for all seven classes.**
   - `Γ` is irreducible.
   - `Γ^+` is torsion-free and contains no pair `a b a^{-1} = b^{-1}` with `b ≠ 1`, pure or conjugate,
     of any length.
   - It contains no `BS(p, q)` with `p ≠ q`, and no Klein-power chain certifies it.
4. **Not left-orderable, without a solver.** For each class, a cone-propagation tree on the radius-4
   ball (`trees.jsonl.gz`, found by `dtree2.py`) refutes every positive cone on `Γ^+`. `verify_cone.py`
   checks it.

   | class | h-letters | tree |
   |---|---|---|
   | `50_31` #243 | 5 involutions | 10 leaves, 318 steps |
   | `51_30` #660 | `h_0 = h_1^{-1}`, 3 involutions | 8 leaves, 234 steps |
   | `51_31` #279 | `h_0 = h_1^{-1}`, 3 involutions | 8 leaves, 232 steps |
   | `51_31` #309 | `h_0 = h_1^{-1}`, 3 involutions | 8 leaves, 274 steps |
   | `52_30` #386 | two inverse pairs, 1 involution | 10 leaves, 324 steps |
   | `52_31` #185 | two inverse pairs, 1 involution | 10 leaves, 360 steps |
   | `30_30` #16 | 3 involutions (degree (3,3)) | 8 leaves, 104 steps |

## Where the family ends

The other four `(5,3)` classes that pass the local-action test (see
`bmw-a5-parity-obstruction-to-pgl2-tree-models`) are `50_30` #499, #515, `50_31` #235 and `51_30` #661.
They have no such representation in `[1, t+1)` with the base vertices of the standard order
`O = F_2[t]⟨1, i, j, k⟩`, among letters whose reduced norm is supported on `{t, t²+t+1, t+1}`.

The search `quat2_53.out` is exhaustive for this. Because `D` is anisotropic at `∞`,
`deg Nrd(x) = max(2 deg(c_0, c_1), 2 deg(c_2, c_3) + 1)`, so such letters have coordinates of degree at
most 1.

The same search on the other 58 `(5,3)` classes that pass the parity test but fail the heuristic
filter (`runquat2_53b.sh`, `quat2_53b.out`) also finds nothing. The remaining 306 `(5,3)` classes
have no model of this kind at all, by the parity obstruction.

The four classes above still have cone trees (`bmw-census-survivor-cone-tree-certificates`). What is left open
for them is only the linear model.
