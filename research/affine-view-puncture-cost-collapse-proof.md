---
rg: 2
id: affine-view-puncture-cost-collapse-proof
kind: route
title: An affine image relation that is not a bijection graph caps acceptance at 1/p, and a Can_comp labeling pays only where sigma departs from beta_t at the labels it uses
target: affine-view-verifiers-collapse-up-to-puncture-cost
requires: []
artifacts:
  - experiments/puncture-triples-2026-09-17/check_puncture_triples.py
---

Notation as in the target.

## Item 1 (rigidity)

The map `h -> (rho_w(h_(o(w))), rho_(w')(h_(o(w'))))` is affine on the affine
space `H_e`, so its image `U_t` is an affine subspace and every fiber has the same
size. A uniform `h in H_e` therefore gives a uniform point of `U_t`, and
```text
acc(t) = |{ (u, v) in U_t : sigma(u) = v }| / |U_t|.
```
Since `H_e` projects onto `A_(o(w))`, the first projection of `U_t` is `I_w`, and
likewise the second is `I_(w')`. Each `u` has at most one `v` with `sigma(u) = v`,
so `acc(t) <= |I_w| / |U_t| = p^(-f_1)`, where `f_1` is the fiber dimension of
`U_t -> I_w`. Since `sigma` is a bijection, each `v` has at most one such `u`, so
`acc(t) <= p^(-f_2)` with `f_2` the fiber dimension of `U_t -> I_(w')`. If
`acc(t) > 1/p`, then `f_1 = f_2 = 0`. So `U_t` is the graph of a map
`I_w -> I_(w')` that is injective and onto, that is, of a bijection `beta_t`, which
is affine because its graph is an affine subspace.

For the weight bound: each incompatible triple rejects with probability at least
`1 - 1/p`, so
`eps = sum_e mu_e sum_t tau_e(t)(1 - acc(t)) >= (1 - 1/p)(1 - w_comp)`.

## Item 2 (transfer)

Take a labeling `X` of `Can_comp`: a coset `X_(z,K) in A_z/K` for each vertex. Put
`F(w) = rho_w(X_(o(w), ker rho_w))`, which lies in `I_w`. The constraint of a
compatible `t` is satisfied iff `beta_t(F(w)) = F(w')`. For such `t`,
`sigma(F(w)) = beta_t(F(w)) = F(w')` unless `F(w) in S_t`. Hence, on edge `e`,
```text
acc_e(F) >= sum_(compatible t) tau_e(t) [constraint sat]
            - sum_(compatible t) tau_e(t) [F(w_t) in S_t],
```
and the last sum is at most the maximum in the definition of `kappa`, because
`(F(w))_w` is one admissible tuple `u_w in I_w`. Averaging over `e ~ mu` gives
`val(V(Phi)) >= w_comp * val_X(Can_comp) - kappa`. Take `X` optimal.

## Item 3 (pointwise bound)

Fix `e` and a view `w`, and put
`c_(e,w)(u) = sum_(compatible t on e, w_t = w) tau_e(t) [u in S_t]` for `u in I_w`.
Choose `h in H_e` with `rho_w(h_(o(w))) = u`, which exists because `H_e` projects
onto `A_(o(w))`. For a compatible `t = (w, w', sigma)` with `u in S_t`, the honest
second label is `rho_(w')(h_(o(w'))) = beta_t(u) != sigma(u)`, so `t` rejects `h`.
By pointwise completeness, `c_(e,w)(u) <= eps`. Now
`sum_t tau_e(t)[u_(w_t) in S_t] = sum_w c_(e,w)(u_w)`. The coordinates `u_w` range
independently, so the maximum is `sum_w max_u c_(e,w)(u)`. Only views that are the
first view of some compatible triple with `S_t` nonempty contribute, and exact
triples have `S_t` empty. So the maximum is at most `r_e eps <= r eps`, and
`kappa <= r eps`. Combining with Items 1 and 2, and using that the oblivious
rejection is at most the pointwise bound `eps`, gives the displayed inequality.

## Item 4 (sharpness)

In `puncture-triples-defeat-partition-coarsening` the same-owner triples
`(w_z, w_z, pi)` have `U_t` the diagonal, so they are compatible with
`beta_t = id` and `S_t = {0, 1}`. At `u_a = u_b = 0` the puncture cost on each edge is
`alpha`, so `kappa = alpha`, and `val(V) = r/(2r-1) < 1 = val(Can_comp)`. The
twin `V^0` has the same `Can_comp` and value `1`. Pointwise rejection is `alpha`
there, consistent with `kappa <= 2 alpha`.

## Replay

`experiments/puncture-triples-2026-09-17/check_puncture_triples.py`: part (RIG)
checks `acc > 1/p => compatible` on more than 2600 triples, and part (TR) checks
`val(V) >= w_comp val(Can_comp) - kappa` and `kappa <= r * pointwise-rejection` on
750 random one-edge instances (four affine views, two to five triples, arbitrary
or punctured `sigma`) with `(p, m, k)` in `(2,3,2), (3,2,1), (2,2,2)`. The script
reports 0 failures on seeds `20260917` and `7`. In 26 instances the value falls
strictly below `w_comp val(Can_comp)`, so the `kappa` term is needed.
