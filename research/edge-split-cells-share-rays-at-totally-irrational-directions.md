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

**ESTABLISHED** in every rank (2026-09-18), by the route
`totally-irrational-shared-rays-via-half-tube`. That route is the Dirichlet corollary of
bh-free-61's `half-tube-lattice-points-are-edge-split-vertices`. bh-major-mcg-2
re-checked the half-tube proof step by step. It is a lane proof, not refereed.
- Attempts 1, 3 and 4 below (the Legendre route, tracking, residues) are superseded:
  none of them is needed.
- The original status is kept below as a record.

Original status: **OPEN** (lane bh-major-mcg-2, 2026-09-18).
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

3. **Recurrent directions reduce to one tracking lemma and one finite check**
   (lane bh-major-mcg-2, 2026-09-18; lane reasoning, not a proof).
   - **Flow coordinates.**
     - Let `k_ξ ∈ SO(m+1)` rotate `ξ` to `e_0`.
     - Let `a_t = diag(e^{−mt}, e^t, …, e^t)`, and put `Λ_t = a_t k_ξ Z^{m+1}`.
     - A cell with frame `W` that contains `ξ` is *`C`-fat at time `t`* if every
       entry of `a_t k_ξ W` has absolute value at most `C`.
   - **Fat cells exist at recurrence times.**
     - If `Λ_t` lies in a compact set `K`, a reduced basis of `Λ_t` has norm at most
       `C_K`.
     - One of the `2^{m+1}` cones spanned by that basis with signs contains
       `a_t k_ξ ξ`.
     - Its preimage is a `C_K`-fat unimodular cell `φ_t ∋ ξ`.
   - **(T_K), tracking (OPEN).** There is `B = B(K)` with the following property. For
     every cell `c` with `ξ ∈ int c`, and every large enough `t` with `Λ_t ∈ K`, some
     `g ∈ Desc(c)` contains `ξ` and has `‖φ_t^{-1} W_g‖, ‖W_g^{-1} φ_t‖ ≤ B`.
   - **(S_K), a finite check.** For each `Y ∈ GL_{m+1}(Z)` with
     `‖Y‖, ‖Y^{-1}‖ ≤ B^2`, the pair `(Δ, cone(Y))` synchronizes at every common point.
     - There are finitely many such `Y`.
     - For each one this is finitely many instances of `(Sync_m)`: cut `Δ` by the
       facet planes of `cone(Y)`.
   - **Conclusion.** If `(T_K)` and `(S_K)` hold, then `(TI_m)` holds at every `ξ`
     whose orbit `Λ_t` returns to `K` for arbitrarily large `t`.
     - Apply `(T_K)` to `c` and to `F` at the same time `t`. The transition between
       the two cells obtained is bounded by `B^2`.
     - `(S_K)` then gives a common descendant containing `ξ`.
   - **Scope.**
     - For almost every `ξ`, the orbit is equidistributed (recalled, not re-read), so
       it returns to a fixed small ball `K` around any lattice. So one `(T_K)` and one
       `(S_K)` would cover almost every direction.
     - Directions with divergent orbits are the singular vectors (Dani's
       correspondence, recalled). There are no fat cells at large times, so this
       reduction says nothing there. That makes the singular directions the place to
       look for a counterexample to `(TI_m)`.
   - **What `(T_K)` needs.** A split schedule that keeps cells fat at recurrence
     times. A fixed deterministic algorithm is not expected to do this, so a proof must
     use the free choice of edge at each step. This is the "fat cells at fat scales"
     mechanism asked for above.

4. **Tracking through containing cells is a bounded-residue property of left
   reduction** (lane bh-major-mcg-2, 2026-09-18). Parts (a)–(c) are exact lane
   proofs; part (d) is a remark.
   - **(a) The containing cells.** Let `φ ⊆ c` be cells with frames `Φ` and `W_c`,
     and put `N = W_c^{-1}Φ`, which is nonnegative. The cells `g ∈ Desc(c)` with
     `g ⊇ φ` are exactly `cone(W_c M)` for `M ∈ 𝕄` with `M^{-1}N ≥ 0`.
     - Writing `M = T_{a_1b_1} ⋯ T_{a_kb_k}`, every prefix quotient
       `T_{a_ib_i} ⋯ T_{a_kb_k} M^{-1}N` is a product of nonnegative matrices.
     - So these cells are precisely the stages of the left-reduction sequences of
       `N` in the matrix game of `unimodular-cells-synchronize-under-edge-splits`.
     - At the cell reached, `W_g^{-1}Φ` is the current matrix, the *residue*.
   - **(b) Tracking from the residue.** If some left-reduction sequence of
     `N = W_c^{-1}φ_t` ends at a residue `R` with `‖R‖ ≤ B`, then the cell reached is
     a tracking cell for `(T_K)` with bound `max(B, ‖R^{-1}‖)`. That cell contains
     `φ_t`, hence `ξ`. Left reductions lower the entry sum, so maximal sequences give
     the smallest residues along their path. A permutation residue means
     `φ_t ∈ Desc(c)`, which is exact tracking.
   - **(c) What a stuck residue means, for `m = 2`.** A residue is stuck exactly when
     `φ` meets both open sides of each first-split plane `y_a = y_b` of the current
     cell `g`. These planes are the three medians of `g`, through the centroid
     `w_0 + w_1 + w_2`.
     - So a large stuck residue says that a much smaller `φ` sits across all three
       medians of `g`, next to the centroid of `g` in `g`'s coordinates.
     - The centroid is a ray of a depth-two descendant of `g` containing `ξ`, since
       subset sums of rays are always captured.
     - So the obstruction to tracking is a centroid event: `ξ` very close, in `g`'s
       frame, to the sum of the rays of a large descendant.
   - **(d) Remark.** By the bounded search of
     `unimodular-cells-synchronize-under-edge-splits`, every stuck residue of entry
     sum at most 36 is won with split depth at most 24. So in rank three, a bound of
     36 on the residue sum would already give a common descendant of `g` and `φ_t`
     that contains `ξ` and is at bounded distance from `φ_t`.
   - **Open.** Whether one can choose, at recurrence times, a reduction order that
     avoids centroid events of unbounded size. The free choice enters here: different
     orders reach different residues, since reduction is not confluent.

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
