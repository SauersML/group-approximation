---
rg: 2
id: contextual-closure-certifies-quantum-rigidity
kind: claim
title: Case splits over a commuting context, where each context pattern determines one end, certify commutation in the scale-D presentation of a Z^2 SFT across fault slabs; only local double faults (explicit 2-dim window representations) obstruct them
distinct_from:
  determinism-closure-certifies-quantum-rigidity: that needs one rule that determines the tile from one side for every context; this lets the determining side depend on the context, which is exactly what crosses fault slabs, since a slab near one end leaves the other end determined.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that uses pairs of global tilings (first-order obstructions); this uses pairs of window patterns legal only on the boxes inside a finite window, which bound the support of certificates from below.
artifacts:
  - research/artifacts/gq-bh-g2-labbe-j2-contextual-probe.md
---

**ESTABLISHED (2026-09-18).** Lane proof, elementary, unreviewed. The Labbé data come from an exact computation.

## Setting

- `Ω ⊆ A^(Z^2)` is an SFT whose forbidden patterns sit in `s × s` boxes, `s = 2D + 1`.
- `C_D` is its scale-`D` presentation: generators `P_z^a`, relations (Q1)–(Q3) of
  `sft-crossed-product-fp-iff-quantum-rigid`, sup norm.
- A set `C ⊆ Z^2` of offsets is **certified** if `[P_0^a, P_v^b] = 0` in `C_D` for all `v ∈ C` and all `a, b`.
  It starts as `B_(2D)`.
- A finite `T` is **commuting** if `T − T ⊆ C`.
- A pattern `π` on `T` is **admissible** if, for every `s × s` box `B` meeting `T`, the restriction `π|_(T∩B)` extends
  to a legal `B`-pattern. The box may stick out of `T`.

## Statement

1. **Partial boxes.** If `T` is commuting and `π` is not admissible, then `prod_(z∈T) P_z^(π(z)) = 0`.
2. **Context split.** Let `T ∋ 0` and `T' ∋ v` be commuting, and `S = T ∩ T'`. Suppose that for every `S`-pattern `τ`
   with admissible extensions to both `T` and `T'`, one of the following holds:
   - all admissible `T`-extensions of `τ` have the same letter at `0`, or
   - all admissible `T'`-extensions of `τ` have the same letter at `v`.

   Then `v` is certified. Together with the `(w)`/`(z)` steps of `determinism-closure-certifies-quantum-rigidity`,
   iterating this gives the **contextual closure**. The determining side may change from context to context.
3. **Window obstruction.** Let `K` be finite, and `C_D(K)` the algebra on the generators in `K` with the relations
   supported in `K`. Suppose `x, y` are `K`-patterns that are legal on every box inside `K`, whose difference set puts
   `0` and `v` in different `2D`-components, and with `x(0) ≠ y(0)` and `x(v) ≠ y(v)`. Then the upper-triangular
   family `[[x_a, λ(x_a − y_a)], [0, y_a]]`, with `λ = 0` on the component of `0` and `λ = 1` on the component of `v`,
   represents `C_D(K)` with `[P_0^a, P_v^b] ≠ 0`. So **no certificate of that commutation, of any degree, uses only
   relations supported in `K`.**
4. **Exactness for two boxes.** Let `v = (2D+1)e_1`, `B = [0, 2D] × [−D, D]` and `B' = B + e_1`, so `K = B ∪ B'` has
   `B` and `B'` as its only boxes. Every site of `B ∩ B'` lies within `2D` of both `0` and `v`, so every item-3 pair
   agrees on `B ∩ B'`. So the following are equivalent:
   - item 2 holds with `T = B`, `T' = B'`;
   - there is no item-3 pair;
   - `[P_0^a, P_v^b] = 0` in `C_D(K)`.

## Proof

1. Insert the partition of unity at the sites of `B \ T`. All of `B` pairwise commutes, so the product over `T ∩ B`
   becomes a sum of box products over illegal box patterns, and (Q3) makes each of them vanish.
2. Put `e_τ = prod_S P^τ`.
   - `e_τ` commutes with `P_0` (all of `T` commutes) and with `P_v` (all of `T'` commutes), and `Σ_τ e_τ = 1`.
   - Expand `e_τ P_0^a` over `T`. By item 1 only admissible terms survive. So if every admissible extension has
     letter `a_0` at `0`, then `e_τ P_0^a = [a = a_0] e_τ`.
   - If `τ` has no admissible extension to `T`, then `e_τ = Σ_a e_τ P_0^a = 0`; likewise for `T'`.
   - Hence `[P_0^a, P_v^b] = Σ_τ [e_τ P_0^a, P_v^b] = Σ_τ [P_0^a, e_τ P_v^b]`, and every term vanishes.
3. This is the two-dimensional computation of `sft-wall-rigidity-iff-idempotent-commutator-ideal`, restricted to the
   relations in `K`. Every box inside `K` meets the difference set in one component, so `λ` is constant there and
   (Q3) holds. Pairs at distance `<= 2D` either lie in one component or have a scalar factor. The commutator of
   `E_(x(0))(0) = diag(1,0)` with `E_(x(v))(v) = [[1,1],[0,0]]` is `[[0,1],[0,0]]`.
4. Two boxes share no site outside `B ∩ B'`, so given the overlap pattern the fillings of `B \ B'` and of `B' \ B` are
   independent. Then a pair exists iff some overlap pattern leaves both ends undetermined.

## Calibration (exact, `research/artifacts/gq-bh-g2-labbe-j2-contextual-probe.md`)

- **Checkerboard and Ledrappier** (both rigid; Ledrappier is triangle-permutive): the contextual closure certifies
  every offset up to the stop radius, 6 and 7.
- **Full 2-shift** (not rigid): it certifies nothing beyond `B_2`, and item-3 walls exist at every window height.

## Instance

`labbe-scale-two-commutation-crosses-faults-at-distance-five`.

## Lesson for general BH

The fault-slab obstruction to determinism is not an obstruction to rigidity. A slab near one end leaves the other end
determined, so a case split on the context crosses it. The only thing that blocks every certificate supported in a
window is a **double fault** inside that window: context patterns that leave both ends free at once.
- For toral-rotation codings this happens at **resonant** separations: both one-sided failures sit near fault lines
  whose offsets differ by `L` modulo the rotation.
- So gate E2 for such codings is a multiscale induction controlled by the continued fraction of the rotation.
  Commutation at distance `L` along one fault normal costs context windows of transverse size about
  `1/‖L − ℓ‖`, where `ℓ` is a fixed offset between fault lines.
- **Golden, badly approximable rotations** are the best case: resonances are sparse, and the needed window size grows
  only linearly in `L`.
- The criterion is mechanical. It is the next test to run on any proposed rigid SFT over `Λ₀ × H`.
