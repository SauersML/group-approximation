---
rg: 2
id: isometric-shift-frames-over-uhf-bases-fail-the-k-budget
kind: claim
title: An isometric shift frame s t = 1, t s = p over a matricial base containing Q forces either a unit class of finite order or, in a graded ring, a degree-one unit; so every such design of index other than 1, and every graded one of index 1, fails the scalar K-budget
distinct_from:
  rational-leavitt-path-k1-k2-scalar-dichotomy: that is Leavitt path algebras of finite graphs over Q, through the Ara--Brustenga--Cortiñas computation; this is any ring with an isometric frame over a matricial base such as U_Q, with an elementary K_0 argument and no graph.
  graded-rings-with-degree-one-units-fail-the-k-budget: that assumes a degree-one unit; this produces one from an index-one frame, and handles the other indices by K_0.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the ring gate; this closes its isometric-shift designs over one-type matricial bases.
---

**ESTABLISHED** through `isometric-shift-frames-over-uhf-bases-fail-the-k-budget-proof`. Refereed:
gq-referee-a PASS, proof-gap lens (report cec484d63, nits applied); gq-referee-b PASS, citation and scope lens (report a141e77ba,
W1 applied to the title). Elementary, given `rational-k1-detection-forces-infinite-order-unit-class` and
`graded-rings-with-degree-one-units-fail-the-k-budget`. No priority is claimed.

**Setting.** `R` is a unital ring and `B ⊆ R` a unital subring with `Q ⊆ B`. An *isometric frame of size `k` over
`B`* is a row `s = (s_1, ..., s_k)` and a column `t = (t_1, ..., t_k)^T` of elements of `R` with
- `s t = s_1 t_1 + ... + s_k t_k = 1`, and
- `p = t s = (t_i s_j) in M_k(B)`.

`p` is then an idempotent. This is the shape of a Cuntz--Pimsner ring of a finitely generated projective
correspondence over `B` with covariance at the unit: the `s_i` and `t_i` are the images of a frame of the module
and its dual, and `p` is its Gram matrix. Leavitt `(1,d)`-tuples are the case `B = Q`, `p = I_d`. A skew Laurent
unit `u` is the case `k = 1`, `s = u`, `t = u^-1`, `p = 1`. Call `B` *matricial* if it is a directed union of
unital subalgebras `M_(n_i)(Q)`, as `Q`, `U_n = ⊗_Z M_n(Q)` and `U_Q = colim M_(n!)(Q)` are. Then
`K_0(B) ⊆ Q` with `[1_B] = 1`, and `[p] = r` is the index of the frame, a positive rational number.

**Statement.**
1. **Unit class.** `[1_R] = [p]` in `K_0(R)`. So if `m [p] = n [1_B]` in `K_0(B)` for integers `m != n`, then
   `(m - n)[1_R] = 0`. No grading is needed.
2. **Index `r != 1` over a matricial base.** `[1_R]` has finite order, so `ker(Q^x -> K_1(R))` is not finitely
   generated, and the `K_1` half of the K-budget fails (`rational-k1-detection-forces-infinite-order-unit-class`).
   This is the Leavitt collapse `[1] = r[1]`.
3. **Index `1` over a matricial base.** `p` is equivalent to `e_11` in `M_k(B)`, and the frame gives a unit `u in R`. It satisfies
   `u^-1 B u ⊆ B` when `t B s ⊆ M_k(B)`. If `R` is `Z`-graded with `B` in degree `0`, the `s_i` in degree `1`
   and the `t_i` in degree `-1`, then `u` has degree `1`. So `graded-rings-with-degree-one-units-fail-the-k-budget`
   applies: either `ker(Q^x -> K_1(R))` is not finitely generated, or no `E_N(R)` with `N >= 3` is finitely
   presented.
4. **Conclusion.** No ring that is graded in this way and has an isometric frame over a matricial base meets the
   K-budget of `fp-simple-resolvent-ring-with-divisible-unit-class`. That covers every shift of any index over
   `U_Q`-type bases, including the ring lamplighter (`k = 1`) and the index-`d` isometries with
   `(1 - [X]) = (1 - d)` on the rational classes.

## Calibration

- Leavitt `L_Q(1,d)`: `r = d`, and item 1 gives `(d - 1)[1] = 0`, the known relation.
- `U_n ⋊ Z`: `r = 1`, and item 3 recovers the degree-one unit.

## What is left open

- **Ungraded index-one frames.** Item 3 still gives the unit `u`, with `u^-1 B u ⊆ B` when `t B s ⊆ M_k(B)`, but without a grading the
  symbols `{λ, u}` have no known boundary map, so it is open whether they are finitely generated.
- **Toeplitz frames.** Frames with `t s = p` but `s t != 1` are not covered; `1 - s t` is then a vacuum
  idempotent.
- **Multi-type bases** (heuristic, conditional on the Pimsner sequence (P) of
  `resolvent-register-units-give-rational-symbols`). For `B` a finite product of `U_Q`-type rings, `[X]` is a
  rational matrix `A`, and `K_1(B)` is `V^m` with `V = K_1(U_Q)` a `Q`-vector space. `K_1` detection needs `[1]`
  to survive in `coker(1 - A) ⊗ Q`, which forces `det(1 - A) = 0`. Then `ker((1 - A) ⊗ V)` is an infinite-dimensional
  subspace of `K_1(B)` that lifts to `K_2(R)`. Whether those lifts lie in the image of `K_2(N, R)`, which
  is what `infinitely-generated-symbols-block-fp-elementary-groups` needs, is open.
