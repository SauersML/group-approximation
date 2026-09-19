---
rg: 2
id: fpbs-transverse-skeleton-ray-codes-are-match-rigid-proof
kind: route
title: Proof that transverse skeleton ray codes on a torsion-free hyperbolic group are uniform quasi-geodesic and exactly matched by coset alignment in the tree of the malnormal skeleton, hence match-rigid under forward injectivity
target: fpbs-transverse-skeleton-ray-codes-are-match-rigid
requires:
  - fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups
---

# Proof

Notation is as in the claim. `(u · v)_w` is the Gromov product. `N_r(Y)` is the closed `r`-neighbourhood. A
**piece** of `P_x` is either an `F`-piece (the subpath read by a maximal run of `F`-letters) or an insertion piece
(a geodesic `[p, p s]` for an insertion letter `s`). Each `F`-letter is realised by a fixed geodesic of length at
most `ell_F = max(|a|, |b|)`.

## Standard inputs

- **(Q1) Quasiconvexity.** `F` is `kappa`-quasiconvex, and the orbit map `F -> Gamma` is a
  `(lambda_F, eps_F)`-quasi-isometric embedding of the tree `T_F` (the Cayley graph of `F` on `a, b`). So the path of a
  reduced `F`-word is a `(lambda_F, eps_F')`-quasi-geodesic lying in `N_{ell_F}` of its coset.
- **(Q2) Malnormal cosets.** For each `r` there is `B_mal(r)` such that `diam(N_r(hF) ∩ N_r(h'F)) <= B_mal(r)` when
  `hF ≠ h'F`. This holds because `F` is quasiconvex and `F ∩ u F u^{-1} = 1` for `u ∉ F` (Gitik--Mitra--Rips--Sageev,
  *Widths of subgroups*, Trans. AMS 350 (1998), Lemma 1.2 and the proof of its main theorem; the pigeonhole argument
  produces a nontrivial element of `F ∩ u F u^{-1}` from a long coarse intersection).
- **(Q3) Morse and local-to-global.** A `(lambda, eps)`-quasi-geodesic is within `M(lambda, eps, delta)` of any
  geodesic with the same endpoints. For every `B` and every `(lambda, eps)` there are `L_*` and `(lambda', eps')` such
  that the following holds. A concatenation of `(lambda, eps)`-quasi-geodesic pieces of length `>= L_*`, with Gromov
  products at most `B` at the junctions, is a `(lambda', eps')`-quasi-geodesic (e.g. Coornaert--Delzant--Papadopoulos,
  *Géométrie et théorie des groupes*, Ch. 3, Thm. 1.4, applied to the geodesic chords of the pieces). Two
  `(lambda', eps')`-quasi-geodesic rays with the same starting point and the same endpoint in `dGamma` are at Hausdorff
  distance `<= C_0(lambda', eps', delta)`. Two such rays with the same endpoint have tails at Hausdorff distance
  `<= C_0`.
- **(Q4) Coarse monotonicity.** If `P, P'` are `(lambda', eps')`-quasi-geodesics at Hausdorff distance `<= C_0`, and
  `p_1, p_2 ∈ P` precede each other by more than `E = E(lambda', eps', C_0, delta)`, then any `p'_1, p'_2 ∈ P'` with
  `d(p_i, p'_i) <= C_0` occur in the same order.

## Step 1. Junctions and (R)

Let `s ∈ I^±` and `f ∈ F`. If `(f · s)_1 > t + delta`, then the initial subsegment of length `t` of `[1, s]` lies in
`N_delta([1, f]) ⊂ N_{delta+kappa}(F)`. By (I1) this is impossible for `t = D(delta + kappa)`. Hence

`(f · s)_1 <= B := D(delta + kappa) + delta` for all `f ∈ F`, `s ∈ I^±`. (1)

At a junction of `P_x`, an `F`-piece ending at `p` meets an insertion `[p, p s]`, or an insertion `[p s^{-1}, p]`
meets an `F`-piece starting at `p`. The Gromov product at `p` is `(f · s)_1` or `(s^{-1} · f)_1`, for `f` the inverse
of a terminal subword, or a subword, of the `F`-piece. It is `<= B + O(lambda_F, eps_F, delta)` by (1) and (Q1).
Choose `L_0 >= L_*`, with `L_*` from (Q3) for this bound. Then every `P_x` is a `(lambda', eps')`-quasi-geodesic
in both directions, uniformly in `x` and in the code. This gives (R), and `|c_k(x)| -> ∞`.

Fix `C_0` from (Q3) and `M` from (Q3). Put `r_1 = C_0 + M + ell_F + kappa`.

## Step 2. No revisits

Suppose two distinct `F`-pieces of one path `P_y` lie in the same coset `hF`. The subpath between them has endpoints
in `N_{ell_F}(hF)`, and it is a `(lambda', eps')`-quasi-geodesic. So it lies in `N_{r_1}(hF)`. It contains a whole
insertion piece, which is a geodesic of length `>= L_I > D(r_1)` inside `N_{r_1}(hF)`. That contradicts (I1). So the
cosets of the successive `F`-pieces of any path are pairwise distinct.

## Step 3. Piece matching

Let `P, P'` be two paths (translates of rays of the code) at Hausdorff distance `<= C_0` on a stretch. Let `sigma` be
an `F`-piece of `P` in the coset `hF`, not among the first or last two pieces of the stretch. Let `pi ⊂ P'` be the
subpath between points `C_0`-close to the endpoints of `sigma`. Then `pi ⊂ N_{C_0 + M}(sigma) ⊂ N_{r_1}(hF)`.

- An insertion piece of `P'` contained in `pi` would be a geodesic of length `>= L_I > D(r_1)` in `N_{r_1}(hF)`.
  That is excluded by (I1). So `pi` contains no whole insertion piece.
- Between two `F`-pieces of `P'` there is an insertion piece. So `pi` meets at most one `F`-piece `sigma'` of `P'`,
  together with at most two partial insertion pieces at its ends.
- Each partial insertion piece is a geodesic subsegment inside `N_{r_1}(hF)`, so its length is `< D(r_1)`.

Hence `sigma' ∩ pi` has length at least `|pi| - 2 D(r_1)`. Also `|pi| >= |sigma| / lambda' - eps' - 2 C_0`. Let
`h'F` be the coset of `sigma'`. The stretch `sigma' ∩ pi` lies in `N_{ell_F}(h'F) ∩ N_{r_1}(hF)`. If

`L_F / (lambda_F lambda') > B_mal(r_1) + 2 D(r_1) + eps' + 2 C_0 + 10 (C_0 + M + ell_F)`, (2)

then `h'F = hF` by (Q2). We call `sigma'` the **partner** of `sigma`. By symmetry, every such `F`-piece of `P'` has a
partner in `P` in the same coset. By Step 2, partnership is a bijection between the pieces of the two paths (away from
the ends of the stretch). By (Q4), and since pieces are longer than `E`, it preserves order.

## Step 4. An exact common vertex

Keep `sigma ⊂ hF` and its partner `sigma' ⊂ hF`. Write their vertex sequences as `h f_0, h f_1, ...` and
`h f'_0, h f'_1, ...`, where `(f_i)` and `(f'_j)` are geodesic vertex sequences in the tree `T_F`, read off the reduced
`F`-words. Every vertex of `sigma' ∩ pi` is within `C_0 + M + ell_F` of some vertex of `sigma` in `Gamma`. By (Q1),
every `f'_j` on that stretch is within `C_T = lambda_F (C_0 + M + ell_F) + eps_F` of some `f_i` in `T_F`.

In a tree, let a geodesic segment `alpha'` of length `> 2 C_T + 2` have every vertex within `C_T` of a geodesic
`alpha`. Then `alpha` and `alpha'` share a vertex. Indeed, the projection of `alpha'` to `alpha` is a path, and the
vertices of `alpha'` at distance `> C_T` from its endpoints lie on `alpha`. By (2), the stretch is long enough.
So there are `i, j` with `f_i = f'_j`, that is, a vertex common to `P` and `P'`.

## Step 5. Exact matching (part 2 of Theorem 2)

Let `g zeta(x) = zeta(x')`. By (Q3), the tails of `g P_x` and `P_{x'}` are at Hausdorff distance `<= C_0`. By Steps 3
and 4, applied to a far `F`-piece, there are `k, k'` with `g c_k(x)^{-1} = c_{k'}(x')^{-1}`. Put `y = x + k` and
`y' = x' + k'`. Then

`zeta(y) = c_k(x) zeta(x) = c_k(x) g^{-1} zeta(x') = c_{k'}(x') zeta(x') = zeta(y')`,

and `P_y`, `P_{y'}` both start at `1` and end at the same point. By (Q3) they are at Hausdorff distance `<= C_0` along
their whole length, so Steps 3 and 4 apply to all their pieces except the first.

We may choose the common vertex in the interior of the partners' common tree segment. Then the first piece of each path
is an `F`-piece containing `1`, in the coset `F`. Write

`P_y = w_1 s_1 w_2 s_2 ...`, `P_{y'} = w'_1 s'_1 w'_2 s'_2 ...`,

with `w_i, w'_i` reduced `F`-words (elements of `F`) and `s_i, s'_i ∈ I^±`. The second `F`-pieces lie in the cosets
`w_1 s_1 F` and `w'_1 s'_1 F`. By Step 3 and order preservation, the partner of the second piece of `P_y` is the second
piece of `P_{y'}`. (A later piece would leave the second piece of `P_{y'}` without an order-compatible partner; the
first piece is excluded because `w'_1 s'_1 F ≠ F`, as `s'_1 ∉ F` by (I1).) Hence

`w_1 s_1 F = w'_1 s'_1 F`, so `s'_1 ∈ w'^{-1}_1 w_1 s_1 F ⊂ F s_1 F`.

By (I2), `s'_1 = s_1 =: s`. Then `s^{-1} (w'^{-1}_1 w_1) s ∈ F`, so `w'^{-1}_1 w_1 ∈ F ∩ s F s^{-1}`. Since `s ∉ F`
and `F` is malnormal, `w_1 = w'_1`. `F` is free on `a, b`, so the reduced words agree letter by letter. Hence
`G(y + t) = G(y' + t)` for `1 <= t <= |w_1| + 1`.

Now translate by `(w_1 s)^{-1}`. The paths `P_{y_2}`, `P_{y'_2}` with `y_2 = y + |w_1| + 1` and
`y'_2 = y' + |w_1| + 1` again start at `1`, in `F`-pieces, and have the same endpoint. Repeat the argument.

If one path has no further insertion, its tail is an infinite reduced `F`-word from `1`, so its endpoint lies in
`Lambda_F`. Suppose the other path had an insertion. Its next `F`-piece would lie in a coset `≠ F` and would need a
partner, but the first path has only the piece in `F`. This contradicts Step 3. So both tails are `F`-rays from `1`
with the same endpoint, and since `dT_F -> Lambda_F` is injective, they are equal words.

By induction, `G(y + t) = G(y' + t)` for all `t >= 1`. This is part 2.

## Step 6. (MR), (MR±) and the kill (part 3)

If the forward coding is injective, part 2 gives `x + k = x' + k'`, so `x' ∈ x + Z`: this is (MR).

For a symmetric code on an odometer, `zeta^-(x) = zeta(-x-1)`. As in the claim of
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`, (MR) on `X_0 ∩ (-X_0)` gives (MR±) with
`Rel = {x' ∈ ±x + Z}`. Theorem 1 there then gives a totally dissipative diagonal for every class carried by
`Gamma zeta(X_0)`, hence no BB boundary class.

## Choice of `L_0`

All constants depend only on `Gamma`, `F`, `delta`, `kappa`, `(lambda_F, eps_F)` and the function `D`. First comes
`B` from (1), then `(lambda', eps')` and `L_*` from (Q3), then `C_0`, `M`, `E` and `r_1`. Take `L_0` larger than
`L_*`, `E`, `D(r_1)`, `2 C_T + 2` and the right side of (2) times `lambda_F lambda'`. No constant depends on `L_I` or
`L_F`, so there is no circularity.

## Proof of the Corollary

This is the contrapositive of part 3. If (I1) holds for `D`, and `L_I, L_F >= L_0(D)`, and (I2) and forward
injectivity hold, then every match is on-orbit. Step 3 is the only step that uses (I1) beyond the bounded junctions
(1). It is where an `F`-piece is shadowed by an insertion when (I1) fails.
