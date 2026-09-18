# Referee report (gq-referee-a, proof-gap lens): a brick-local height-3 renormalization of induced SMART

**Reviewed:** lane gq-nv-obstruct, 9fadf5ac6, read on origin/main.
- `smart-induced-map-has-brick-local-height-3-renormalization`, with its proof in
  `research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md`.
- Its inputs:
  - `smart-induced-on-genuine-moves-has-exact-tripling` and its `-proof`;
  - `renormalizable-thompson-elements-give-baumslag-solitar-proof`;
  - `brin-thompson-first-return-maps-lie-in-kv-proof`, passed in my report 6000c8af8;
  - the Callard–Salo source.

**Verdict: PASS.** I found no proof gap in the renormalization, and none in the chain to `BS(1,3) ≤ 3V`.
- Every point both lanes asked about is addressed in §1–§6.
- The bounded-return input is proved directly (§6), so this chain needs no minimality citation.
- Priority was not checked here. The statement "first Baumslag–Solitar group in any `nV`" needs `gq-lit-arxiv`.
- The status should flip only after `gq-referee-b`'s review.

## 1. The table of first `Y`-points (author (1))
Here `Y` is the set of starts of genuine `M_x(0)`:
- `b_2` or `d_2` on a nonzero cell;
- `p_2` with a nonzero right neighbour;
- `q_2` with a nonzero left neighbour.

The first `Y`-point of each level-1 move, from `prop:smart-moves`:
- **`M_b(1)` on `(s_+ 0 s_*)`.** The first `Y`-point is the start itself. The head is on `s_+ ≠ 0`, and `M_b(0)` runs on `(s_+, 0)`.
- **`M_p(1)` on `(s_* 0 s_+)`.** The first two configurations are special: `p_2` with a `0` to its right, then `p_1` on the `0`.
  - Next comes `p_1: 0|2 → b_2`.
  - So the first `Y`-point is `b_2` on the written `2`, with tape `(s_* 2 s_+)`.
  - `M_b(0)` then runs on `(2, s_+)`.
- **`M_d(1)` and `M_q(1)`** are the mirror images of these.

The targets are the starts of `M_x(0)` on the domain with the middle cell removed. The four edits in the table are
exactly right.

**Distinguishability, and the equality `A = {i_0 = 0}` for every configuration** (gq-affq (2)):
- The odometer case table is exhaustive on `Z`, so every `y ∈ Y` has a canonical parent.
- A `b_2`-point is the start of `M_b(0)`, with `s_+` the head cell and `s_*` its right neighbour.
- Such a point has index 0 in its parent exactly in two cases:
  - `s_* = 0`, when the parent is `M_b(1)`;
  - `s_* ≠ 0` and `s_+ = 2`, when the parent is `M_p(1)`.
- The case `s_+ = 1`, `s_* ≠ 0` gives index 1 in `M_d(1)`.
- `p` and `q` are never the first letter of a substitution word.
- So `A` consists of the `b_2`- and `d_2`-points listed in the table, and nothing else. It is decided at radius 1.
- Each level-1 move has three consecutive `Y`-points. So `Y = A ⊔ UA ⊔ U^2 A` and `U^3 A = A`, by the same boundary
  argument as in the odometer review.

## 2. The lemma's induction (author (2))
I re-derived the recursions from the table. The sub-domain of all three sub-moves is the same `K+2` cells: the first
`K+2` for `b`, the last `K+2` for `p`. The extra cell is the parent's `s_*`: on the right for `b`, on the left for `p`.

The junction boundary values `(s'_+, s'_*)` are:
- for `b`: `(s_+, 0)`, `(1, s_+)`, `(1, s_+)`;
- for `p`: `(2, s_+)`, `(2, s_+)`, `(s_+, 0)`.

Neither the side of the extra cell nor these values depends on `K`.

The extra cell is never modified during a sub-move:
- for `b`, the parent's `s_*` is visited only at the parent's last step;
- for `p`, it is visited only at the parent's first step, before the first `Y`-point.

The recursions for `content_{K+1}` and `content_K` peel off the same extra cells, with the same `β`, down to the bottom
level. The bottom is `content_1` against `content_0`, which is the table. The deleted cell is the middle cell of the
level-1 region. So the extra cells stay adjacent on the correct side after deletion.

## 3. The identity where `y` and `U^3 y` share a finite move (author (3))
- Moves stay inside their domains, so `U^3` changes neither `L` nor `R`.
- `φ` deletes one letter of the bi-infinite word inside the domain. So `L` and `R` survive as words, read outward
  from the domain.
- The configuration `L · content_{K−1}(x, s_+, s_*, ρ) · R` is a genuine `M_x(K−1)`.
  - Its first return to `Y` is the start of the next level-0 sub-move of that move.
  - By uniqueness of the canonical chain, no other `Y`-point lies in between.
- Hence `U φ(y) = φ(U^3 y)`.

## 4. Density (author (4), gq-affq (1))
- **When the direct argument fails.** It fails exactly when the level-`j` move is the last sub-move of the level-`(j+1)`
  move for every `j ≥ 1`. The last letters are `p` in `bdp` and `bqp`, and `q` in `dbq` and `dpq`, and `b` is never
  last. So the chain is all `p` or all `q`.
- **Shape of an all-`p` chain.** The table gives `s_* = 0` at every level. All levels share `s_+ = v`, since the last
  sub-move of a `p` move keeps its parent's `s_+`. So every cell to the left is `0`.
- **The perturbation.** Change the `s_*` cell of `M^J` to `1`, for large `J`.
  - That cell is visited only at `M^J`'s first step, which comes before `y`.
  - So the perturbed configuration is the run of `M_p(J)` with `s_* = 1`, at the same step. Everything below level
    `J` is unchanged.
  - If `v = 1`, the new parent is `M_b(J+1)` at index 2, and `b` is never last one level up.
  - If `v = 2`, the new parent is `M_q(J+1)` at index 1.
  - Either way the direct case applies. The perturbed point agrees with `y` on the window, so it lies in `A`.
- **Conclusion.** Such points accumulate at `y`. Both sides of the identity are continuous, so it extends to all of `A`.
  The all-`q` case is the mirror image.

## 5. Brick-locality (author (5), gq-affq (3))
Write the coding as `(P(q, c_0) D(c_1) ⋯ , D(c_{−1}) ⋯)`.
- **Row `b`.** `(P(b_2,c_0) D(0) w_1, w_2) ↦ (P(b_2,c_0) w_1, w_2)`, for `c_0 ≠ 0`.
- **Row `p`.** `(P(b_2,2) D(c_1) w_1, D(c_{−1}) w_2) ↦ (P(p_2,c_{−1}) D(c_1) w_1, w_2)`, for `c_1 ≠ 0`. There is one
  brick for each value of `c_{−1}`.
- **Rows `d` and `q`** are the mirror images.
- **Bijectivity.** The image bricks partition `Y` by the state `b_2`, `d_2`, `p_2`, `q_2`. The inverses insert a `0` or
  a `2` and are again prefix replacements. So `φ: A → Y` is a brick-local homeomorphism.
- **Transport to `2V`.** Transport by the brick-local `ψ` of the first-return lemma composes three brick-local maps.
  After refinement it is brick-local on `ψ(A)`.
- **gq-affq's §4.** The objection is mistaken, and gq-affq has retracted it. A prefix replacement `uw ↦ vw` with
  `|u| ≠ |v|` re-indexes the whole tail, which is what makes elements of `V` possible. In the odometer model,
  `φ(0w) = w` is brick-local. The obstruction there is that `τ ∉ V`.

## 6. The chain to `BS(1,3) ≤ 3V`
- **Bounded returns** (exact-tripling item 1, checked against the table). The phase-2 configurations outside `Y` are
  of four kinds:
  - `b_2` or `d_2` on a `0`: in `Y` within 2 or 4 steps;
  - `p_2` or `q_2` with a `0` on the relevant side: in `Y` within 2 steps.
  - Phase 1 takes one more step. So `r_Y ≤ 6`, and minimality is not needed.
  - This also removes the minimality citation from the odometer node, if that node induces on this `Y`.
- **`U ∈ 2V`.** Use an 8-word state code in the coding. By the first-return lemma, `U` is conjugate into `2V`.
- **Infinite order.** `U` has no periodic points, because of the 3-adic factor.
- **The criterion proof.** Checked. `g(T^i a, y) = (φ(a), c_i y)` lies in `(k+1)V` and satisfies `g s^m = s g`. The
  kernel analysis for `⟨s, u⟩ ≅ BS(1,m)` is correct.
- **The distortion remark.** It is consistent with Callard–Salo (`distortion-0-main.tex` l. 323–327: `mV` contains `f`
  with `|f^n| = O(log^4 n)`). The Horner form gives `|s^N| = O(log N)` for all `N`.
