---
rg: 2
id: bmw-a5-parity-obstruction-to-pgl2-tree-models
kind: claim
title: A BMW group of degree (5, n) has no PGL_2 model over a discretely valued field in which the h-letters map the base vertex bijectively onto its neighbours, unless every v-letter permutes the h-letters evenly; 306 of the 374 remaining (5,3) survivors fail this
distinct_from:
  bmw-quaternionic-type-53-parity-kernels: that constructs models for six even classes; this proves that the odd classes have no such model in any characteristic, algebra, order or place
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that is about left orders; this is only about linear tree models
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/README.md
  - experiments/bmw-cone-trees-2026-09-18/remaining.py
  - experiments/bmw-cone-trees-2026-09-18/remaining.json
  - experiments/bmw-cone-trees-2026-09-18/parity5.py
  - experiments/bmw-cone-trees-2026-09-18/parity5.json
  - experiments/bmw-cone-trees-2026-09-18/parity5.log
  - experiments/bmw-cone-trees-2026-09-18/parity5b.py
  - experiments/bmw-cone-trees-2026-09-18/parity5b.json
  - experiments/bmw-cone-trees-2026-09-18/localfilter.py
  - experiments/bmw-cone-trees-2026-09-18/localfilter.json
  - experiments/bmw-cone-trees-2026-09-18/runquat2_53b.sh
  - experiments/bmw-cone-trees-2026-09-18/quat2_53b.out
  - research/bmw-a5-parity-obstruction-to-pgl2-tree-models-proof.md
---

**ESTABLISHED.** The proof is in `bmw-a5-parity-obstruction-to-pgl2-tree-models-proof`. The lemma has
a short proof. The count comes from two independent scripts that agree on all 374 classes.

## Setting

`Γ` is a BMW group with `m` h-letters and `n` v-letters and squares `h v = v' h'`. For a v-letter `u`,
let `π_u` be the permutation of the h-letters defined by `h' ↦ h` whenever `h v = u h'` is a square.
It is the local action of `u` on the h-edges at the base vertex.

A *tree model on the h-side* is a triple `(F, ρ, o)` where:
- `F` is a field with a discrete valuation, `ρ : Γ → PGL_2(F)` is a homomorphism, and `o` is a vertex of
  the Bruhat–Tits tree `Δ` of `PGL_2(F)`;
- every `ρ(v)` fixes `o`;
- `h ↦ ρ(h) o` is a bijection from the h-letters onto the neighbours of `o`.

This is exactly the h-half of the conditions (T1) and (T2) in `bmw-quaternionic-type-53-parity-kernels`,
`bmw-quaternionic-char3-type-44-parity-kernels` and `bmw-klein-free-quaternionic-parity-kernels`. Each
quaternionic model there, completed at the h-place, is one.

## Statement

1. **Lemma.** If `m = 5` and `(F, ρ, o)` is a tree model on the h-side, then every `π_u` is an even
   permutation. This holds in every characteristic, for every `F` and every `ρ`.

   For `m = 3` or `m = 4` there is no such constraint, because `PGL_2(F_2) = S_3` and `PGL_2(F_3) = S_4`
   act as full symmetric groups.
2. **Census count.** Among the 374 remaining `(5,3)` classes, 306 have a v-letter with odd `π_u`. So they
   have no tree model on the h-side, and in particular no quaternionic model of the type used in the
   three nodes above. The count is by `parity5.py` and the independent `parity5b.py`, which agree on
   all 374.

   | pattern | remaining | odd (excluded) | even | even and passing the filter | with a model |
   |---|---|---|---|---|---|
   | `50_30` | 182 | 162 | 20 | 2 | 0 |
   | `50_31` | 35 | 20 | 15 | 2 | 1 |
   | `51_30` | 74 | 65 | 9 | 2 | 1 |
   | `51_31` | 35 | 21 | 14 | 2 | 2 |
   | `52_30` | 32 | 27 | 5 | 1 | 1 |
   | `52_31` | 16 | 11 | 5 | 1 | 1 |
   | total | 374 | 306 | 68 | 10 | 6 |

   "Remaining" means no irreducibility certificate in the census and no Klein-power or Klein-frame
   certificate (`remaining.py`). "With a model" refers to `bmw-quaternionic-type-53-parity-kernels`.
3. **Mixed residue characteristics.**
   - A model of a `(4,3)` class on both sides needs residue fields `F_3` and `F_2` for two discrete
     valuations of one field. So that field has characteristic 0, for example a number field with
     places over 2 and 3. No function-field model exists.
   - The same holds for `(5,4)` (`F_4` and `F_3`); there are no such survivors.
   - For `(5,3)` the residue fields are `F_4` and `F_2`, so characteristic 2 or 0.

## Heuristic filter (not part of the claim)

`localfilter.py` additionally asks that the local action group `L = ⟨π_u⟩` on each side satisfy
`PSL_2(F_q) ≤ L ≤ PGL_2(F_q)` and be 2-transitive. This is expected when the image of `Stab(o)` in
`PGL_2(k)` is large, for instance by strong approximation for `S`-arithmetic models. It is **not**
proved necessary.

96 of the 994 remaining classes pass it, and the model searches ran first on those.

The 58 even `(5,3)` classes that fail the filter were then searched with the same exhaustive search in
`[1, t+1)` (`runquat2_53b.sh`, `quat2_53b.out`), and none has a model. So among the `(5,3)` classes,
in this algebra, the filter lost nothing.
