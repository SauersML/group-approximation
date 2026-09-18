---
rg: 2
id: fpbs-mal-fold-closure-exactness-proof
kind: route
title: Fold abstract copies of coset hulls in the Cayley tree; the folding rules at a vertex are exactly the 2-of-3 rule
target: fpbs-mal-fold-closure-exactness
requires: []
artifacts:
  - research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md
  - research/artifacts/fpbs-chord-unfolding-length-floor-2026-09-18.md
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify.py
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify_out.txt
---

The complete proof is §1 of `fpbs-fold-bootstrap-seeding-2026-09-17.md`
(Lemma 1.1 and Theorem 1.2). §4 of `fpbs-chord-unfolding-length-floor-2026-09-18.md`
checks it independently. It imports only Stallings folding: a connected
folded graph immersing into a tree embeds.

1. **Easy half.** `D` satisfies the 2-of-3 rule, because `w ~ a w` and
   `b^2 w ~ b a w` hold in `R_K`. So `cl(A) ⊆ D`.
2. **Coordinates.** In one orbit, `g x_0 ↦ z = g^{-1}` sends `R_K`-classes
   to left cosets `zK`. The hull of `zK` in the right Cayley tree `T'` is
   `z · hull(K)`.
3. **Vertex types.** The core `Γ_K` has vertices `0, v_1, v_2` and edges
   `a : 0 → 0`, `b : 0 → v_1`, `a, b : v_1 → v_2`. Readable words end at
   `0`, `v_1`, `v_2` exactly on `K`, `K b`, `K b^2`. So each `y ∈ T'` lies
   in exactly three hulls: those of `yK`, `y b^{-1} K`, `y b^{-2} K`, with
   types `0`, `1`, `2`.
4. **Folding rules.** From the local stars:
   - `(0,1)` at `y` forces `(0,2)` at `y a` and `(1,2)` at `y b`;
   - `(0,2)` at `y` forces `(0,1)` at `y a^{-1}`;
   - `(1,2)` at `y` forces `(0,1)` at `y b^{-1}`.

   Writing `d(y)` for `(0,1)` at `y`, consistency at `y` is the 2-of-3 rule
   on `{y, y a^{-1}, y b^{-1}}`, which is `T_w` in the original
   coordinates. Seeds are `d(z)` for `g x_0 ∈ A`.
5. **Closing.** The identification prescribed by the closure is folded, and
   it stays inside `R'`-classes. A connected folded graph immersing into
   `T'` embeds. So cosets at `y` that are in one class are already
   identified, i.e. `D ⊆ cl(A)`.

`certify.py` (`exactness_tests`) finds `D = cl(A)` on 30 random seed sets
in the radius-9 ball.
