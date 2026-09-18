---
rg: 2
id: edge-split-cells-share-rays-at-totally-irrational-directions
kind: claim
title: Around every totally irrational direction, any two unimodular cells containing it have edge-split descendants containing it that share a ray
distinct_from:
  rank-two-synchronization-off-totally-irrational-rays: that isolates this shared-ray problem for m = 2 as the last case of synchronization in rank three; this states it in every rank, where it is the only remaining input.
  unimodular-cells-synchronize-under-edge-splits: that is full synchronization; this is its totally irrational core, one rank at a time.
  edge-split-descent-reaches-very-close-lattice-points: that proves this statement at the very well approximable directions; this asks for it at all of them.
  edge-split-sync-reduces-to-totally-irrational-shared-rays: that proves synchronization follows from this statement in all lower ranks; this is the statement itself.
---

**OPEN** (lane bh-major-mcg-2, 2026-09-18).
- True for `m = 1`.
- For `m ≥ 2`, proved at every direction with
  `liminf |p|^m · dist(p, Rξ) = 0`.
- For `m = 2`, it holds at every direction where some nested pair of descendants has
  a transition matrix of entry sum at most 36. This part uses the bounded search of
  `unimodular-cells-synchronize-under-edge-splits`.

## Statement (TI_m)

Notation of `edge-split-sync-reduces-to-totally-irrational-shared-rays`.
- **Data.** Unimodular cells `c, F ⊂ R^{m+1}`, and a totally irrational ray `ξ` (on no
  rational hyperplane) with `ξ ∈ int c ∩ int F`.
- **Conclusion.** Some `c_1 ∈ Desc(c)` and `f_1 ∈ Desc(F)`, both containing `ξ`, share
  a ray.

## Why it matters

- **It is the whole synchronization problem.**
  `edge-split-sync-reduces-to-totally-irrational-shared-rays` proves
  `(TI_2) ∧ … ∧ (TI_m) ⇒ (Sync_m) ⇒ (TI_m)`.
- **Closed mapping class groups.** The host `𝒯_{6g−7}` of genus `g` needs
  `(TI_k)` for `k ≤ 6g − 7`.
- **For `m = 2`.** It is the open item of
  `rank-two-synchronization-off-totally-irrational-rays`, stated there as meeting of
  the vertex sets `V_c(ξ)` and `V_F(ξ)`.

## What is known

1. **`m = 1`.** Small descendants of `c` around `ξ` lie in `F` and descend from it
   (Stern–Brocot). So they are common descendants.
2. **Very well approximable directions**
   (`edge-split-descent-reaches-very-close-lattice-points`). If
   `liminf_{|p| → ∞} |p|^m dist(p, Rξ) = 0`, a single good approximation `p` becomes a
   ray in both descent systems. This covers exponent `ω(ξ) > m`.
3. **Finite-configuration criterion** (lane proof, one line).
   - **Criterion.** Let `c' ∈ Desc(c)` and `f' ∈ Desc(F)` contain `ξ`, with
     `c' ⊆ f'`. If the pair `(c', f')` synchronizes, then `(TI_m)` holds at `ξ`. For
     example, the pair synchronizes if the transition matrix `Y = U'^{-1}W'` (frames
     `U'`, `W'`) is won in the matrix game of
     `unimodular-cells-synchronize-under-edge-splits`: some common descendant then
     contains `ξ`.
   - **`m = 2`.** That node's bounded search wins every stuck nonnegative unimodular
     `3×3` matrix of entry sum at most 36. A non-stuck matrix left-reduces to a smaller
     entry sum. So every nonnegative unimodular `3×3` matrix of entry sum at most 36 is
     won (lane search, not a proof).
   - **Consequence.** A failure of `(TI_2)` at `ξ` needs every nested pair of
     descendants containing `ξ` to have transition entry sum above 36. The descent
     system of `F` can never get close, in the lattice sense, to that of `c` around
     `ξ`.

## A reading (heuristic, not a proof)

- **Rescaling.** Rescale a pair of descendants around `ξ` by the frame of the outer
  cell. A failure at `ξ` is then inherited by every rescaled pair.
- **Recurrent directions.** If the two descent systems contained cells of comparable
  size and shape at infinitely many scales, the transition matrices would lie in a
  finite set. Criterion 3 would then turn `(TI_m)` into a finite check, as in the scale
  collapse of the Z² rigidity programme. This is plausible where the diagonal-flow
  orbit of `ξ` returns to compact sets, for instance at badly approximable directions,
  whose orbits are bounded (Dani's correspondence, recalled).
- **Very well approximable directions** are settled by item 2.
- **What is missing.** No argument yet shows that a descent system contains fat cells
  at the scales where the lattice is fat. The singular directions of moderate
  exponent, whose orbits diverge, fit neither mechanism.

## Attempts

1. **Legendre route** (lane bh-major-mcg-2, 2026-09-18).
   - **What it gives.** Capture of one lattice point along a Euclid path on its
     coordinates (item 2).
   - **Where it stops.** The capture threshold is `K^{-m}` against the Dirichlet scale
     `K^{-1/m}`, because the path may pass through thin cells. Paths through fat cells
     would reach the Dirichlet scale, and then constants decide. So this route alone
     does not cover the generic directions.
2. **Braid-cut strategy** (lane bh-free-61, recorded in
   `unimodular-cells-synchronize-under-edge-splits`). It wins all 10310 stuck `3×3`
   matrices of entry sum at most 36. No termination measure is known.

## Lesson for general BH

- **The Serret gate is Diophantine.** For hosts built from `GL_n(Z)` acting on a
  rational Cantorization, the Serret-type gate is a statement about how the free-choice
  continued-fraction systems of two frames meet around an irrational direction.
- **Two regimes are tractable.**
  - Very well approximable directions: a single good approximation is a shared vertex.
  - Directions whose lattice orbit recurs: bounded configurations recur, which points
    to a finite check.
- **The missing link.** What is needed is a mechanism that makes descent systems
  contain fat cells at fat scales. The singular directions are the natural test case,
  and possibly the place to look for a counterexample.
