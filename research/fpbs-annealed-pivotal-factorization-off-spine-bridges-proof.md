---
rg: 2
id: fpbs-annealed-pivotal-factorization-off-spine-bridges-proof
kind: route
title: Split each pivotal by whether the two separated clusters touch the spine; a spine-free cluster is a pure Bernoulli cluster, so BK in the quenched product leaves one deterministic factor and annealing factorizes; for activations, cut a connecting path at its first and last spine vertex
target: fpbs-annealed-pivotal-factorization-off-spine-bridges
requires:
  - fpbs-quenched-bk-russo-collapse-operator-gate
  - fpbs-continuous-activation-collapse-family
---

Notation as in the target. `u ≠ v` throughout; for `u = v` all kernels are `1`
and all increments vanish. Paths are self-avoiding.

## 1. The quenched lemma (frozen environment)

Fix a finite `Lambda`, a set `Z ⊆ E`, a volume `H` with
`Lambda ⊆ H ⊆ Lambda ∪ Z`, and `r in [0,1]`. Let `P^Z_r` be the product
measure on `{0,1}^{Lambda \ Z}` with parameter `r`. Edges of `Z ∩ H` are open
deterministically; edges outside `H` are absent. Write
`tau^Z_r(x,y) = P^Z_r(x <-> y in (xi_r ∪ Z) ∩ H)`.

The event `{u <-> v in (xi_r ∪ Z) ∩ H}` depends only on the finitely many
random coordinates in `Lambda \ Z`, so `r -> tau^Z_r(u,v)` is a polynomial.
Russo's formula for product measures gives
`d/dr tau^Z_r(u,v) = sum_{f in Lambda \ Z} P^Z_r(Piv_f)`.

Fix `f in Lambda \ Z` with endpoints `a ≠ b`; a loop is never pivotal. Let
`omega'` be the configuration with `f` closed, and `C'(x)` the cluster of `x`
in `omega' ∩ H`. Then `Piv_f` is the disjoint union of `E^{ab}_f` and
`E^{ba}_f`, where

```text
E^{ab}_f = { a in C'(u), b in C'(v), C'(u) ≠ C'(v) }.
```

Summing over the two orientations and over multi-edges,
`sum_f P(Piv_f) = sum_{(a,b)} J_{Lambda \ Z}(a,b) P(E^{ab}_f)`, with
`J_{Lambda \ Z} <= J_W` entrywise.

Let `Y = V(Z ∩ H)`, and let `Bridge = {C'(u) ∩ Y ≠ ∅ and C'(v) ∩ Y ≠ ∅}`.

**Lemma 1.** With `beta^Lambda_r(x,y) = P(x <-> y in xi_r ∩ Lambda)`,

```text
P^Z_r(E^{ab}_f \ Bridge) <= tau^Z_r(u,a) beta^Lambda_r(b,v) + beta^Lambda_r(u,a) tau^Z_r(b,v).
```

If the graph `Z ∩ H` is connected, then `E^{ab}_f ∩ Bridge = ∅`.

*Proof.* Off `Bridge`, either `C'(v) ∩ Y = ∅` or `C'(u) ∩ Y = ∅`.

Suppose `C'(v) ∩ Y = ∅`. No edge of `C'(v)` lies in `Z ∩ H`, because such
an edge has both endpoints in `Y`. So `C'(v)` is spanned by edges of
`H \ Z ⊆ Lambda \ Z` that are open in `xi_r`. Take an open path `gamma_1`
from `u` to `a` in `omega' ∩ H`, and an open path `gamma_2` from `b` to `v`
in `C'(v)`. They are vertex-disjoint, since `C'(u) ≠ C'(v)`, and neither uses
`f`. The random edges of `gamma_1` witness the increasing event
`{u <-> a in (xi_r ∪ Z) ∩ H}`. The edges of `gamma_2` are all random and
witness `{b <-> v in xi_r ∩ Lambda}`. So `E^{ab}_f ∩ {C'(v) ∩ Y = ∅}` lies in
the disjoint occurrence of these two increasing events. The BK inequality
holds for the product measure `P^Z_r`, and the second event does not see the
deterministic coordinates. This gives the bound
`tau^Z_r(u,a) · P^Z_r(b <-> v in xi_r ∩ (Lambda \ Z)) <= tau^Z_r(u,a) beta^Lambda_r(b,v)`.

The case `C'(u) ∩ Y = ∅` is symmetric, and the union bound adds the two
cases.

For the second claim, every component of the graph `Z ∩ H` is open, so it
lies inside one cluster of `omega' ∩ H`. On `Bridge`, `C'(u)` contains a
vertex of some component `K` and `C'(v)` a vertex of some component `K'`.
Then `K ⊆ C'(u)` and `K' ⊆ C'(v)` are disjoint, so `K ≠ K'`, and `Z ∩ H`
has at least two components. ∎

## 2. Theorem 1

Take `H = Lambda` and `Z = Z_r`, which is `M`-measurable. Given `M`, the law
of `omega_r ∩ Lambda` is `P^{Z_r}_r`, so `E[tau^{Z_r}_r(x,y)] = T^Lambda_r(x,y)`.
By definition, `R^Lambda_r(u,v) = E[sum_{(a,b)} J_{Lambda \ Z_r}(a,b) P^{Z_r}_r(E^{ab}_f)]`.

Split each term on `Bridge`. Let
`Br^Lambda_r(u,v) = E[sum_{(a,b)} J_{Lambda \ Z_r}(a,b) P^{Z_r}_r(E^{ab}_f ∩ Bridge)]`.
By Lemma 1 it vanishes on `{Z_r ∩ Lambda connected}`. On the complement,
Lemma 1 gives

```text
E[ tau^{Z_r}_r(u,a) ] beta^Lambda_r(b,v) + beta^Lambda_r(u,a) E[ tau^{Z_r}_r(b,v) ]
   = T^Lambda_r(u,a) beta^Lambda_r(b,v) + beta^Lambda_r(u,a) T^Lambda_r(b,v).
```

Here we used that `beta` is deterministic and `J_{Lambda \ Z_r} <= J`.
Finally `beta^Lambda_r <= T^Lambda_r`, because `xi_r ⊆ omega_r`. ∎

## 3. Theorem 2 (R): the Russo part

Fix `s < t` and condition on `M`. Put `Z = Z_t` and `H = Lambda ∪ Z_t`. Then
`Z ∩ H = Z_t` is connected, so Lemma 1 has no bridge term. For `r in [s,t]`,
`Phi(r; Z_t) = tau^{Z_t}_r(u,v)`, and

```text
d/dr tau^{Z_t}_r(u,v) <= sum_{a,b in W} J_W(a,b) [ tau^{Z_t}_r(u,a) beta_r(b,v) + beta_r(u,a) tau^{Z_t}_r(b,v) ].
```

The endpoints of `f in Lambda` lie in `W`. Both factors are nondecreasing in
`r`, so the right side is at most its value at `r = t`. Integrating over
`[s,t]`:

```text
Phi(t; Z_t) - Phi(s; Z_t) <= (t-s) sum_{a,b} J_W(a,b) [ tau^{Z_t}_t(u,a) beta_t(b,v) + beta_t(u,a) tau^{Z_t}_t(b,v) ].
```

Now take expectations. Given `M`, the configuration
`(xi_t ∪ Z_t) ∩ (Lambda ∪ Z_t)` equals `omega_t ∩ (Lambda ∪ Z_t)`, and `xi_t` is
independent of `M`. So `E[tau^{Z_t}_t(x,y)] = X_t(x,y)`. Also
`beta_t <= X_t` on `W`. This proves (R). ∎

## 4. Theorem 2 (A): the activation part

Fix `s < t` and condition on `M`. Write `omega^s(Z) = (xi_s ∪ Z) ∩ (Lambda ∪ Z)`.
Because `Z_s ⊆ Z_t`, we have `omega^s(Z_s) ⊆ omega^s(Z_t)`. Hence
`Phi(s;Z_t) - Phi(s;Z_s) = P(F)`, where
`F = {u <-> v in omega^s(Z_t)} \ {u <-> v in omega^s(Z_s)}`.

On `F`, take an open path `gamma` from `u` to `v` in `omega^s(Z_t)`.

* If `gamma` avoids `V(Z_t)`, then all its edges lie in `xi_s ∩ Lambda`, so
  `u <-> v` holds in `omega^s(Z_s)`. That is excluded, so `gamma` meets
  `V(Z_t)`.
* Let `x` be the first vertex of `gamma` in `V(Z_t)`, and `y` the last. The
  segment `gamma[u,x]` has no edge of `Z_t`, because such an edge has both
  endpoints in `V(Z_t)`. So it consists of open edges of `xi_s ∩ Lambda`, and
  `x in W`. The same holds for `gamma[y,v]`.
* If both `x` and `y` were in `V(Z_s)`, then, since `Z_s` is connected,
  `gamma[u,x]`, a `Z_s`-path from `x` to `y`, and `gamma[y,v]` would connect
  `u` to `v` in `omega^s(Z_s)`. That is excluded.

So `F` is contained in the union, over `x,y in W ∩ V(Z_t)` not both in
`V(Z_s)`, of `{u <-> x in xi_s ∩ Lambda} ∘ {y <-> v in xi_s ∩ Lambda}`. The two
segments of the self-avoiding path `gamma` are edge-disjoint. The index set
is `M`-measurable, and `xi_s` is independent of `M`. So BK for Bernoulli
percolation gives

```text
P(F | M) <= sum_{x,y in W} 1{x,y in V(Z_t), not both in V(Z_s)} beta_s(u,x) beta_s(y,v).
```

Take expectations. Since `{x,y in V(Z_s)} ⊆ {x,y in V(Z_t)}`,
`P(x,y in V(Z_t), not both in V(Z_s)) = S_t(x,y) - S_s(x,y)`. Hence
`D^A_{s,t} <= beta_s (S_t - S_s) beta_s`. Adding (R) and (A) proves the last
display of the target. ∎

## 5. Remarks

* The factor `2` is the union of the two orientations of spine-freeness. At
  most one of the two separated clusters can touch a connected spine, and the
  spine-free side is Bernoulli. This is why annealing factorizes: the
  environment enters only one factor.
* In plain volumes the same argument leaves exactly `Br^Lambda_r`. A
  connected spine cut by `Lambda` can have several pieces joined outside
  `Lambda`, and a pivotal between two pieces has both sides
  environment-correlated.
