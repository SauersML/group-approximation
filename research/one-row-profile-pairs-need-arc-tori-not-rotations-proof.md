---
rg: 2
id: one-row-profile-pairs-need-arc-tori-not-rotations-proof
kind: route
target: one-row-profile-pairs-need-arc-tori-not-rotations
title: Proof that one-row pairs of profile 3 need two rows, via the break lemma, the power structure of centralisers of a cycle, and an exact arc-torus reformulation of permutation distance
requires:
  - excised-thick-torus-kills-width-matched-one-sided-repair
  - near-exact-tuples-saturate-linear-conversion-defect
---

Throughout, `b = +1` on `Z/n` and `c` is a permutation of `Z/n`. For permutation matrices `P` and `Q` on a finite set
`X`, let `diff(P, Q) = #{x : P(x) != Q(x)}`. Since `rank(P - Q) = rank(Q^-1 P - I) = |X| - cyc(Q^-1 P)`, and each
nontrivial cycle of length `l` contributes `l - 1`, which lies in `[l/2, l]`:

  (R) `diff(P, Q) / 2 <= rank(P - Q) <= diff(P, Q)`.

**Item 1 (break lemma).** `c^t b^s(x) = b^s c^t(x)` holds exactly when `c^t(x+s) = c^t(x) + s`, that is, when
`D_t(x+s) = D_t(x)`. If `D_t(x+s) != D_t(x)`, then some `y` in `{x, ..., x+s-1}` has `D_t(y+1) != D_t(y)`, which means
`y` is in `B_t`. Each `y` lies in at most `s` such windows. So `[b^s, c^t]` moves at most `s |B_t|` points, and by (R)
`rank([b^s, c^t] - I) <= s |B_t| <= (s+t) sup_t |B_t|`. []

**Item 2 (single-row lower bound).** Let `(b', c')` commute on `X = Z/n u P` with `b'` a single `|X|`-cycle. The
centraliser of a full cycle is the group it generates, so `c' = b'^w` for some `w`. If `w = 0` mod `|X|`, then
`c' = id` and `c'` differs from `c (+) gamma` at every point that `c` moves: `n - |Fix c|` old points. Otherwise `c'`
is fixed-point-free, so it differs from `c` at every point of `Fix c`. By (R),
`rank(c' - c (+) gamma) >= min(|Fix c|, n - |Fix c|) / 2`. []

**Item 3 (the family).** Put `L = beta + gamma`. On `A`, `c = id`. On the arc `B u C = [alpha, n)`, with coordinate
`y = x - alpha` in `Z/L`, `c` is `y -> y + gamma` on `B = [0, beta)` and `y -> y - beta = y + gamma - L` on
`C = [beta, L)`. So `c` restricted to `B u C` is the rotation by `gamma` of the cyclically ordered arc, and `c^t` is the
rotation by `t gamma mod L`.
- Consecutive pairs `(x, x+1)` inside `A` are not breaks. Inside the arc there is at most one break, at the wrap point
  of the rotation. The only other candidates are `x = alpha - 1` and `x = n - 1`. So `|B_t| <= 3`, and item 1 gives
  `Lambda_rect <= 3`.
- Since `1 <= gamma < L`, the rotation by `gamma` has no fixed point, so `Fix c = A` and `n - |Fix c| = L`. Item 2 gives
  the single-row lower bound `min(alpha, L) / 2`.
- *The two-row repair.* Let `b'` agree with `b`, except that `b'(alpha - 1) = 0` and `b'(n - 1) = alpha`. Then
  `b' = b tau` for a transposition `tau`, so `rank(b' - b) = 1`. The cycles of `b'` are `A`, on which `b'` is the cyclic
  `+1`, and `B u C`, on which it is the cyclic `+1`. On `A`, `c` is the identity. On `B u C`, `c` is a power of the
  cyclic `+1`. So `c` commutes with `b'`, and `(b', c)` has cost 1 with no padding. `verify.py` checks all three
  statements for every `(alpha, beta)` with `n <= 40`. []

**Item 4 (arc-torus reformulation).**

*First direction.* Let `(b', c')` be an `(m, e)`-arc-torus.
- `rank(b' - b (+) beta) <= m`, by (R).
- Let `P_in` be the set of padding points `p` with `c'(p)` in `P`. The points of `P \ P_in` are sent by `c'` into
  `Z/n`. Their images are old points that are not images of old points under `c'`, so there are at most as many of them
  as old points `x` with `c'(x)` in `P`, and those are among the `e` changed points.
- Choose `gamma` on `P` to extend the injective partial map `c'` restricted to `P_in`. Then `c'` and `c (+) gamma`
  differ in at most `2e` points, so the rank is at most `2e`.

*Structure.* At every old point `x` outside the `m` changed points, `b'(x) = x + 1`. So a maximal run of old points
joined by `b'`-steps of `+1` ends at a changed point. Each `b'`-cycle is therefore a cyclic concatenation of such arcs
and of runs of padding, with at most `m` arcs in total unless `m = 0`. Because `c'` commutes with `b'`, it maps each
`b'`-cycle onto a `b'`-cycle of the same length and conjugates `+1` to `+1`, so it is a translation in row coordinates.

*Converse.* Suppose `(b', c')` commutes and has permutation cost `delta`. By (R), `diff(b', b (+) beta) <= 2 delta`
and `diff(c', c (+) gamma) <= 2 delta`. The second bound counts old points in particular. []

**Item 5 (twist beta + gamma).** Put `c = S + theta` and `theta = L`. Then `c(x) = x + L` on `A`, `x + L + gamma` on
`B`, and `x + gamma` on `C`, all mod `n`.

Place padding `P = {n, ..., n + beta - 1}` between `n - 1` and `0`, so that `b'` is `+1` on `Z/(n + beta)`. This
differs from `b (+) beta` only at `n - 1` and `n + beta - 1`, where `beta` is the cyclic shift of `P`. Put
`c' = +L` on `Z/(n + beta)`. Then `c'` agrees with `c` at every old point outside `B`:
- For `x` in `A`, `x + L < alpha + L = n`.
- For `x` in `C`, `x + L` lies in `[n + beta, n + beta + gamma)`. Mod `n + beta` this is `x + gamma - n`, which is `c(x)`.
- For `x` in `B`, `x + L` lies in `[n, n + beta)`, which is padding.

So `m = 2` and `e = beta`. For `E(a, k)`, `theta = a = beta + gamma`, so this is the column insertion at the holes found
in the excised-torus node. `verify.py` checks this for `n <= 40`. []

**Scope.** The data in the claim (resonant twists, `beta = 1`, the 157 example) come from computation in
`experiments/one-row-2026-09-18` and are not proved. The corrected next step is a conjecture.
