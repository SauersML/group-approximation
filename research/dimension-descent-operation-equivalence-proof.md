---
rg: 2
id: dimension-descent-operation-equivalence-proof
kind: route
title: Minimal dimension and one ultraproduct identify the descent hypothesis with MF-residual membership
target: dimension-descent-operation-equals-mf-residual-membership
requires: []
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

## Proof

Notation is as in the target.

**(E1).**
- *Empty implies Op.* If `Vis(R, eps)` is empty, the descent condition is a
  statement about all elements of the empty set, so it holds.
- *Op implies empty.* Suppose `Vis(R, eps)` is nonempty. The dimensions of
  its elements form a nonempty set of positive integers. Let `d` be its
  least element and `U` an element of dimension `d`. `Op(R, eps)` gives
  `V in Vis(R, eps)` of dimension `d' < d`, contradicting minimality.
- *Threshold form.* `Vis(R, eps)` is empty iff no `U` has
  `||z(U) - I|| >= 1` and `delta_R(U) < eps`, iff `delta_*(R) >= eps`.

**(E2), emptiness implies membership.** This is the conclusion of
`dimension-descent-criterion-for-non-mf`, repeated here so that this route
needs no prerequisite.
- Let `pi : G -> U(Q)`, `Q = prod_n M_(d_n) / (+)_n M_(d_n)`, be a
  homomorphism. Lift the generators to unitaries `U_n in U(d_n)^k`, using
  the fact that unitaries of `Q` lift to sequences of unitaries.
- Every relator `r` of `G` satisfies `limsup_n ||r(U_n) - I|| = 0`. `R` is
  finite, so `delta_R(U_n) < eps` for all large `n`.
- If `pi(z) != 1`, then `pi(z)` is a self-adjoint unitary other than `1`.
  So `pi(z) - 1` has spectrum containing `-2`, and `||pi(z) - 1|| = 2`.
  Hence `limsup_n ||z(U_n) - I|| = 2`, and some large `n` puts `U_n` in
  `Vis(R, eps)`.
- So `Vis(R, eps)` empty forces `pi(z) = 1` for every `pi`, that is,
  `z in Res_MF(G)`.

**(E2), membership implies emptiness.**
- Suppose `Vis(R, eps)` is nonempty for every finite `R` and every `eps > 0`.
- Enumerate the relators of `G` as `r_1, r_2, ...`, which is possible since
  `F_k` is countable. Put `R_n = {r_1, ..., r_n, z^2}` and choose
  `U_n in Vis(R_n, 1/n)`, of dimension `d_n`.
- Let `u_i` be the class of `(U_(n,i))_n` in `Q = prod_n M_(d_n) / (+)_n M_(d_n)`.
  Each `u_i` is unitary.
- For each relator `r_m`, `||r_m(U_n) - I|| < 1/n` for all `n >= m`. So
  `r_m(u) = 1` in `Q`, and `s_i -> u_i` defines a homomorphism
  `pi : G -> U(Q)`.
- `||pi(z) - 1|| = limsup_n ||z(U_n) - I|| >= 1`, so `pi(z) != 1` and
  `z` is not in `Res_MF(G)`.
- Contrapositive: if `z in Res_MF(G)`, some finite `R` and some `eps > 0`
  give `Vis(R, eps)` empty. Enlarging `R` or shrinking `eps` keeps it empty,
  so `z^2` may be assumed to lie in `R`.

**(E3).**
- The hole `binary-leavitt-dimension-descent-operation` asks for `Op(R, eps_0)`
  for the binary Leavitt unit group `H` and its involution `z`, with `R` a
  finite set of relations containing `z^2`.
- By (E1), that is `Vis(R, eps_0)` empty. By (E2), some such pair exists iff
  `z in Res_MF(H)`.
- The route `leavitt-full-radical-via-dimension-descent` concludes
  `z in Res_MF(H)` from the hole, together with simplicity of `H`. So the
  hole already contains the conclusion.
- Neither direction above uses anything beyond the well-ordering of the
  positive integers, lifting of unitaries from `prod / (+)`, and countability
  of `F_k`. A Kazhdan-free proof of either side therefore gives a
  Kazhdan-free proof of the other.

**(E4).**
- If a candidate formula `Phi` produces an output from some
  `U in Vis(R, eps)`, then `delta_*(R) <= delta_R(U) < eps`. By (E1),
  `Op(R, eps)` then fails, and the minimal-dimension element of `Vis(R, eps)`
  is where `Phi` fails.
- Suppose instead that `Phi` sends each `U in Vis(R, eps)` to some `V` with
  - `dim V < dim U`,
  - `||z(V) - I|| >= 1`, and
  - `delta_R(V) <= f(delta_R(U))`, where `f(t) < t` on `(0, eps)`.

  Then `delta_R(V) < delta_R(U) < eps`, so `V in Vis(R, eps)` and
  `Op(R, eps)` holds. By (E1), `Vis(R, eps)` is empty. This covers the
  quadratic loss `f(t) = C t^2` with `eps < 1/C`.
- It also covers any loss when the threshold is allowed to vary. If `Phi`
  sends `Vis(R, eps_1)` into strictly smaller dimension with `f(t) < t`,
  then (E1) applied at `eps = min(eps_1, t_0)` empties `Vis(R, eps)`,
  where `t_0` is the supremum of the interval on which `f(t) < t`.
