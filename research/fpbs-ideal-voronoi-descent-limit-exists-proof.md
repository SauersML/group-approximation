---
rg: 2
id: fpbs-ideal-voronoi-descent-limit-exists-proof
kind: route
title: Nucleus consistency makes descent chains geodesic, compactness gives a limit, clopen cylinders pass the rootless and geodesic events to it, and the weak-containment closure keeps it below Bernoulli
target: fpbs-ideal-voronoi-descent-limit-exists
requires: []
---

Complete direct proof. Notation is that of the target. The only imported facts are the definition of weak
containment (Kechris), and that factors and weak-star limits of actions weakly contained in `b_Gamma` stay weakly
contained. The second is proved in §3, following §0 of `fpbs-hp-condensation-bernoulli-exit-proof`.

## 1. The finite-intensity objects are well defined, equivariant factors of iid

1. For `eps > 0`, `omega_eps` is almost surely infinite, because `Gamma` is infinite and the `U(g)` are iid.
2. The values `W(g)` are almost surely distinct.
3. Balls in `d` are finite. So the minimiser `p_eps(x)` exists and is unique almost surely, and it depends on
   finitely many coordinates on the event `{d(x, omega_eps) <= R}`, whose probability tends to one as `R` grows.
4. The Cayley graph with edges `x ~ xs` is invariant under left multiplication, and `d` is left invariant.
5. So `(sigma_eps(g), U(g), W(g))_g` is a measurable `Gamma`-equivariant function of the iid field. Its law `nu_eps`
   is shift invariant, and `s_{nu_eps}` is a factor of `b_Gamma`, hence `s_{nu_eps} ≺ b_Gamma`.

## 2. Consistency: the descent step keeps the nucleus

Let `x` not be in `omega_eps`, with `p = p_eps(x)`, `n = d(x,p) >= 1`, `s = sigma_eps(x)` and `y = xs`, so that
`d(y,p) = n-1`. Take any `q` in `omega_eps`.
1. `d(y,q) >= d(x,q) - 1 >= n - 1`.
2. If `d(y,q) = n-1`, then `d(x,q) <= n`, and minimality gives `d(x,q) = n`. So `q` ties with `p` at `x`, hence
   `W(q) >= W(p)`, with equality only for `q = p`.
3. Therefore `p` minimises `(d(y,.), W)` at `y`, that is, `p_eps(y) = p_eps(x)`.

Iterating, the chain from `x` reduces the distance to the fixed nucleus `p` by one at each step. It reaches `p` after
exactly `n` steps, so it is a geodesic segment from `x` to `p`.

## 3. Compactness and the closure

1. `K` is compact metrizable, so `K^Gamma` is compact metrizable, and the shift-invariant probability laws form a
   weak-star compact set. Choose `eps_n -> 0` with `nu_{eps_n} -> nu`. The limit is invariant.
2. Let `P` be a finite partition, `F` a finite subset of `Gamma`, and `delta > 0`.
   - Approximate `P` in `nu`-measure by a partition `P'` into finite unions of products of `nu`-continuity sets of
     finitely many coordinate marginals. These have `nu`-null boundaries.
   - Then `nu_{eps_n}(g P'_i ∩ P'_j) -> nu(g P'_i ∩ P'_j)` for `g` in `F`.
   - For large `n`, `s_{nu_{eps_n}} ≺ b_Gamma` supplies a partition of `b_Gamma` matching these numbers within
     `delta`.
   - So `s_nu ≺ b_Gamma`.
3. The projection to `([0,1]^2)^Gamma` is continuous, and it pushes every `nu_eps` to the iid uniform law. So it pushes
   `nu` to the iid uniform law too.
4. Almost surely the labels `W(g)` are distinct, and `gamma . omega = omega` would force `W(gamma^{-1} h) = W(h)`
   for all `h`. So the action is essentially free.

## 4. No roots

1. `{sigma(e) = *}` is a cylinder on one coordinate with values in the discrete factor `S ∪ {*}`, so it is clopen.
2. Weak-star convergence gives `nu(sigma(e) = *) = lim_n nu_{eps_n}(sigma(e) = *) = lim_n eps_n = 0`.
3. By invariance and countability of `Gamma`, almost surely `sigma(g) != *` for every `g`.

## 5. Chains are geodesic rays

Fix `m >= 1`, and let `G_m` be the event that the `m`-step chain from `e` is defined and ends at word length `m`: the
arrows `s_1, ..., s_m` read along the chain are all different from `*`, and `|s_1 ... s_m| = m`.
1. `G_m` depends only on the `S ∪ {*}` coordinates in the ball `B(m)`, so it is clopen.
2. Under `nu_eps`, suppose `omega_eps` misses `B(m)`. Then `d(e, p_eps(e)) > m`. By §2, the first `m` steps are an
   initial segment of a geodesic from `e` to its nucleus, so `G_m` holds.
3. Hence `nu_eps(G_m) >= 1 - |B(m)| eps`, and by clopenness `nu(G_m) = lim_n nu_{eps_n}(G_m) = 1`.
4. Intersecting over `m` and over translates, almost surely every forward chain is a geodesic ray.

A cycle of `f` would give a periodic chain, which is not a geodesic ray. Every component contains a forward ray, so
every component is infinite.
