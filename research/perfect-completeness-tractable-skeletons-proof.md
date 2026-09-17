---
rg: 2
id: perfect-completeness-tractable-skeletons-proof
kind: route
title: Seeds with correct labels propagate without conflict, separating pairings force whole merge components, certified wrappers make the merged unique game satisfiable, and affine skeletons are linear systems
target: perfect-completeness-rich-2to1-tractable-skeletons-are-in-p
requires: [left-preserving-local-richness-wrappers-are-affine-ug-merges]
artifacts:
  - experiments/rich-2to1-perfect-completeness-2026-09-17/forcing_closure_check.py
---

Notation is as in the target claim.

**Lemma 0.** On input `x`, run `R` and then `A`, and compute the value of `A`'s
labeling. Accept iff it exceeds `delta`.

* If `x in Lang`, the value exceeds `delta` by hypothesis.
* If `x notin Lang`, every labeling has value `<= val(R(x)) <= delta`.

Both steps take polynomial time.

**Closure soundness.** Let `(L, M)` satisfy `G`, and seed the closure with
`L|S`. Induct on forcing steps. The claim is that every labelled vertex carries
its `(L, M)` label.

* *Right step.* `M_v = pi_(uv)(L_u)`, which is the true right label because the
  edge is satisfied.
* *Left step.* Every labelled neighbour `v` of `w` carries `M_v`, and
  `pi_(wv)(L_w) = M_v`. So `L_w in C_w`, which is therefore never empty, and
  `|C_w| = 1` gives `C_w = {L_w}`.

All labelled vertices agree with `(L, M)`, so the final edge check passes.
Every edge at a labelled left vertex has its right end labelled, so the mass of
satisfied edges is the mass at labelled left vertices.

**(M1).** Take each connected component `C` separately. For every `S` in `C`
with `|S| <= t` and every labeling of `S`, compute the closure. Discard it on a
conflict. Among the survivors keep the largest labelled mass, and take the union
over components. Components share no vertices or edges, so the partial labelings
combine. Label the remaining vertices arbitrarily.

* *Value.* A surviving closure passed the edge check, so all its labelled edges
  are satisfied, whatever `S` was. By closure soundness, the true seeds survive,
  so the kept mass in `C` is at least the component term of `kappa_t`. Summing,
  the value is `>= kappa_t(G) > delta`.
* *Time.* The cost is `|V|^t (2k)^t poly(|G|)`. Apply Lemma 0.

*The digraph condition.* Suppose `u` is labelled and `u -> w` in `D`. Then every
`v in N(u) ∩ N(w)` is labelled. `C_w` lies in
`intersection over v in N(u) ∩ N(w) of pi_(wv)^(-1)(M_v)`. That set contains
`L_w` and lies in one class of the separating partition, so it is `{L_w}` and
`w` is forced. By induction, closure contains the `D`-reachability set.

*Two pairings with no common pair separate.* If `a` has partner `b` in the first
and partner `c` in the second, then `b != c`. So the fibres through `a`
intersect in `{a}`.

**(M2).** Let `(L, M)` satisfy `Psi_Sigma(U)`. Fix a right `v` and neighbours
`u, u'`. Suppose `phi_(uv)(L_u) = a != a' = phi_(u'v)(L_(u'))`. Some
`sigma in Sigma_v` separates `a` from `a'`. The right vertex `(v, sigma)` then
needs `sigma(a) = M(v,sigma) = sigma(a')`, a contradiction. So all
`phi_(uv)(L_u)` agree. Call that label `M'(v)`; then `(L, M')` satisfies `U`.

Conversely, if `(L, M')` satisfies `U`, then `M(v,sigma) = sigma(M'(v))`
satisfies `Psi_Sigma(U)`.

For the arcs: if `u, w` share a `U`-neighbour `v`, then `N(u) ∩ N(w)` contains
every `(v, sigma)`. The maps `sigma o phi_(wv)` are the separating family
`Sigma_v` pulled back through the bijection `phi_(wv)`, so they separate.
`D`-reachability therefore covers the connected component of `U`. When `U` is
satisfiable, one seed per component labels everything, so `kappa_1 = 1`.

In the YES case `Psi_Sigma(R'(x))` is satisfiable. Apply (M1) with `t = 1`.

**(M3).** In the YES case take a certified satisfying labeling, so `beta = 0`.
Item 5 of the wrapper theorem gives `val_(U_W(G))(L) >= 1 - 0`, so `U_W(G)` is
satisfiable. Item 6 says `U_W(G)` is computable in polynomial time.

A satisfiable unique game is solved by propagation. In each component, try all
`2k` labels at one vertex, propagate through the bijections, and check every
edge. The true label passes.

The resulting `L` has `val_(U_W)(L) = 1`, and item 4 gives
`val_W(L) >= (1 - alpha_k) > delta`. Apply Lemma 0.

**(M4).** Write a variable in `F_q^(d_u)` for each left vertex and `F_q^(d_v)`
for each right vertex of the skeleton. Each skeleton edge contributes the
equations `e_v(M_v) = T_(uv) e_u(L_u) + c_(uv)`.

* In the YES case the true labeling solves the system.
* Gaussian elimination over `F_q` returns some solution in polynomial time.
* Every solution decodes through the bijections `e` to labels that satisfy every
  skeleton edge.

So the value is `>= mass > delta`. Apply Lemma 0.

*Translations.* An affine surjection `F_2^d -> F_2^(d-1)` with kernel `{0, b}`
has fibres `{x, x + b}`. So the 2-to-1 affine constraints are exactly the
`F_lin` pairings.

**Computation.** `forcing_closure_check.py` exits 0.

* *Check A* covers closure soundness.
* *Check B* covers the (M2) equivalence and one-seed forcing.
* *Check C* confirms, on the Grassmann skeleton, that the closure is the set of
  2-subspaces of the seed span, and that elimination solves the offset affine
  skeleton.
