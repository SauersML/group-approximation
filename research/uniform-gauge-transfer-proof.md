---
rg: 2
id: uniform-gauge-transfer-proof
kind: route
title: Averaging a Can_comp labelling with uniform marginals turns puncture cost into oblivious rejection, and free functionals on DKKMS folding classes give such an average of value 1
target: dkkms-affine-view-verifiers-any-sigma-sound-at-2c-1
requires: [affine-view-verifiers-collapse-up-to-puncture-cost, grassmann-composed-2to2-coarsenings-are-satisfiable]
artifacts:
  - experiments/uniform-gauge-2026-09-17/check_uniform_gauge_transfer.py
  - experiments/uniform-gauge-2026-09-17/check_dkkms_homogeneous_gauge.py
---

Notation as in the target.

Imported from the graph, both ESTABLISHED:

- `affine-view-verifiers-collapse-up-to-puncture-cost`, Item 1 (rigidity: a
  triple accepting more than a `1/p` fraction of `H_e` is compatible). From its
  proof we also use that `h -> (rho_w(h), rho_(w')(h))` pushes the uniform measure
  on `H_e` to the uniform measure on `U_t`.
- `grassmann-composed-2to2-coarsenings-are-satisfiable` with its route: Lemma A
  (i)-(iv), Lemma B (exact pairs on an agreement edge are `M_i = r_i(N)`, with
  constraint "some `phi in Fun(N)` has `s_i(r_i x) = phi(x) + h_(U_i)(x - r_i x)`
  for `x in N`, `i = 1, 2`"), Lemma C, and the Theorem (`F*` satisfies every exact
  pair).

## Item 1 (uniform-marginal transfer)

**Acceptance of a compatible triple.** Let `t` be compatible. A uniform
`h in H_e` gives a uniform point of `U_t`, the graph of `beta_t` over `I_(w_t)`.
So the first honest label `u` is uniform on `I_(w_t)` and the second is
`beta_t(u)`. The triple rejects iff `sigma(u) != beta_t(u)`, that is, iff
`u in S_t`. Its rejection probability is `|S_t| / |I_(w_t)|`, and the compatible
triples contribute exactly `E_comp` to `eps`. Write `E_inc = eps - E_comp` for the
part carried by incompatible triples. Each of them rejects with probability at
least `1 - 1/p`, so
```text
E_inc >= (1 - 1/p)(1 - w_comp).                                   (1)
```

**Transfer.** Fix a labelling `X` of `Can_comp` and put
`F_X(w) = rho_w(X_(o(w), ker rho_w))`. This is well defined, because an affine map
is constant on cosets of the kernel of its linear part, and it lies in `I_w`. For
a compatible `t = (w, w', sigma)`, if the `Can_comp` constraint holds, that is if
`beta_t(F_X(w)) = F_X(w')`, then `t` accepts `F_X` iff `F_X(w) notin S_t`. So
```text
[t accepts F_X] >= [constraint of t holds under X] - [F_X(w) in S_t].
```
Incompatible triples contribute at least `0`. Sum with weights `mu_e tau_e(t)`,
and take expectations over `X ~ D`:
```text
val(V(Phi)) >= E_X val_(F_X)(V) >= w_comp nu_D - sum_(compatible t) mu_e tau_e(t) Pr_X[F_X(w_t) in S_t].
```
Since `rho_w` induces a bijection `A_z / ker rho_w -> I_w` and the marginal of
`D` at `(z, ker rho_w)` is uniform, `F_X(w)` is uniform on `I_w`. Hence
`Pr_X[F_X(w_t) in S_t] = |S_t| / |I_(w_t)|`, and the last sum is `E_comp`. This
proves the first inequality.

For the second, use `E_comp = eps - E_inc`, then (1) and `nu_D <= 1`:
```text
w_comp nu_D - E_comp >= w_comp nu_D + (1 - 1/p)(1 - w_comp) - eps
                     >= nu_D - (1 - w_comp) nu_D / p - eps
                     >= nu_D - (1 - w_comp)/p - eps.
```
By (1), `1 - w_comp <= p eps / (p - 1)`. So `(1 - w_comp)/p <= eps/(p-1)`, and the
bound is `nu_D - eps - eps/(p-1) = nu_D - p eps/(p-1)`.

No step uses pointwise completeness, affinity of `sigma`, or the number of
views per edge.

## Item 2 (homogeneous gauges on DKKMS instances)

Every compatible triple of `Can_comp` has the same image relation `U_t`, and the
same `beta_t`, as the exact triple with the same kernel pair and
`sigma = beta_t`. Compatibility depends only on `H_e` and the two views. So the
edges of `Can_comp` are the kernel pairs of Lemma B together with same-owner
pairs of equal kernels, which carry the identity constraint, and each carries
the constraint of Lemma B. `F*` satisfies all of them by the imported Theorem.

**Homogeneous constraints.** For a Lemma B pair `(M_1, M_2) = (r_1 N, r_2 N)`, the
set of pairs `(s_1|M_1, s_2|M_2)` meeting the constraint is the graph of an affine
bijection. Its linear part is the set of pairs `(g_1, g_2)`, `g_i in Fun(M_i)`,
for which some `phi' in Fun(N)` has `g_i(r_i x) = phi'(x)` for `x in N` and
`i = 1, 2`. Adding a solution of this homogeneous constraint to a solution of the
original gives a solution of the original, with `phi + phi'`.

**`pi_N` is well defined and bijective.** Let `(U, N) in A_m`, `m = dim N`, and
let `Q` be its class with representative `R_Q`. By Lemma A(iv), applied to the
class `Q` at dimension `m`, `R_Q meet H_U = {0}` and `R_Q + H_U = N + H_U`. So
`pi_(Q,U)(x)`, the `R_Q`-component of `x in N`, is defined, and the map is linear.
If `pi_(Q,U)(x) = 0`, then `x in N meet H_U = {0}`. So it is injective, hence
bijective by dimension. If also `(U', N) in A_m`, Lemma C shows that `(U', N)` is
in the same class and that `pi_(Q,U)(x) = pi_(Q,U')(x)`: the proof of Lemma C
gives `q = q'`. So `Q(N)` and `pi_N` depend on `N` alone. For the private class of
a subspace with no legitimate `U`, `pi_N = id`.

**`G_psi` satisfies every homogeneous constraint.** Take a Lemma B pair with
`N != 0`. The same-owner pairs are trivial, and `N = 0` is trivial.

- *Endpoint `i` is an A-class through `(U_i, L_i)`.* Then `N <= W <= L_i`, so
  `(U_i, N) in A_m` and `Q(N)` is a genuine class. Since
  `x - r_i x in H_(U_i)` for `x in N`, we get `M_i + H_(U_i) = N + H_(U_i)`. So
  `(U_i, M_i)` and `(U_i, N)` lie in one folding class, `Q(M_i) = Q(N) =: Q`. The
  same identity shows that `r_i x` and `x` have the same `R_Q`-component in
  `R_Q + H_(U_i)`. So `pi_(M_i)(r_i x) = pi_N(x)`, and
  `G_psi(z_i, M_i)(r_i x) = psi_Q(pi_N(x))`.
- *Endpoint `i` is a B-vertex.* Then `r_i = id` and `M_i = N`, so
  `G_psi(z_i, N)(x) = psi_(Q(N))(pi_N(x))`.

In every case both endpoints give `psi_(Q(N))(pi_N(x))` for `x in N`. If one
endpoint is an A-class, both use the genuine class `Q(N)`. If both are B-vertices,
both use `Q(N)`, genuine or private. So the homogeneous constraint holds with
`phi' = psi_(Q(N)) o pi_N`.

**Uniform marginals.** Draw `psi_Q` independently and uniformly from `Fun(R_Q)`
for every class. At a vertex `(z, Ann(M))`, `M != 0`, the label is
`F*(z, M) + psi_(Q(M)) o pi_M`. Since `pi_M` is a linear bijection, `psi o pi_M` is
uniform on `Fun(M)`, and a fixed translate of a uniform variable is uniform.
The vertex with `M = 0` has one label. So `D = law(F* + G_psi)` has uniform
marginals and value `nu_D = 1`.

## Item 3 (class kill)

Apply Item 1 with `p = 2` and `nu_D = 1`: `val(V(Phi)) >= 1 - 2 eps = 2c - 1` on every
3LIN input, since Item 2 uses no satisfiability. A reduction to `Gap-UG(c, s)`
has `s >= val(V(Phi))` on NO instances, so `s >= 2c - 1`.

## Item 4 (hypothesis needed)

Take the family of `puncture-triples-defeat-partition-coarsening` with `p = 2`,
`l = 3`, `r = 3` and `alpha = 2/5`. Identity views have trivial kernel. The cross
constraints `v = lambda_i u`, for three distinct `lambda_i`, hold simultaneously
only at `u = v = 0`. So the unique optimal `Can_comp` labelling is `0`, with value 1,
and its marginals are point masses. The oblivious rejection is
`eps = alpha * 2/8 = 1/10`, and that claim gives
`val(V) = max(1 - alpha, (1 - alpha)/3 + alpha) = 3/5 < 4/5 = 1 - 2 eps`.
`check_uniform_gauge_transfer.py` replays this exactly.
