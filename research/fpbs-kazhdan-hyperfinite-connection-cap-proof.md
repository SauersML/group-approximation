---
rg: 2
id: fpbs-kazhdan-hyperfinite-connection-cap-proof
kind: route
title: An invariant vector in the class-indicator field gives finitely many classes per orbit, a finite-index extension of a hyperfinite relation is amenable, and Zimmer's theorem forbids that for a nonamenable free action
target: fpbs-kazhdan-hyperfinite-connection-cap
requires:
  - fpbs-kazhdan-local-cost-formula
  - fpbs-hp-condensation-bernoulli-exit
---

This is a full written proof, not a formal verification.

**Imported inputs.**
- **[T]** Kazhdan pair. For every unitary representation `pi` with invariant projection `P`, and every `xi`,
  `kappa ||xi - P xi|| <= max_{s in S} ||pi(s) xi - xi||`.
- **[FI]** Finite-index extensions. Let `E ⊆ F` be countable Borel equivalence relations on a standard probability
  space such that every `F`-class is a finite union of `E`-classes. If `E` is hyperfinite, then `F` is
  `mu`-amenable, hence hyperfinite off a null set. See Jackson--Kechris--Louveau, *Countable Borel equivalence
  relations* (2002), Section 1, and Connes--Feldman--Weiss.
- **[CS]** Amenability passes from a complete section `U` of an invariant set `Y` to `R|Y`. See Kechris--Miller,
  *Topics in orbit equivalence*, Section 9.
- **[Z]** Zimmer, *Ergodic theory and semisimple groups*, Prop. 4.3.3, and Kechris--Miller, Section 9. A free p.m.p. action of a countable group on a set of positive measure with amenable orbit relation
  forces the group to be amenable. Infinite Kazhdan groups are nonamenable.
- **[LCF]** `fpbs-kazhdan-local-cost-formula`, Theorem 1 and Corollary 2.
- **[HPX]** `fpbs-hp-condensation-bernoulli-exit`. From §A: members of `W_b` joined with `b` are ergodic. From §C:
  coins constant on classes of a hyperfinite subrelation of the cluster relation keep the thinning in `W_b`, and
  unions of independent samples stay in `W_b`.

## 1. Theorem A

**The class field.**
- For `x` in `X`, put `V_x = {g in Gamma : g^{-1} x in V}`. Partition `V_x` by `g ~ h` iff
  `(g^{-1} x, h^{-1} x) in E`, and let `Cl(x)` be the set of classes.
- Freeness makes `g -> g^{-1} x` injective, so the classes are subsets of `Gamma`. Also `V_{gamma x} = gamma V_x`
  and `Cl(gamma x) = gamma Cl(x)`.
- As in `fpbs-kazhdan-local-cost-formula-proof`, Section 1, `H = L^2(X; l^2(Cl(x)))` carries the unitary
  representation `(pi(gamma) xi)_x(C) = xi_{gamma^{-1} x}(gamma^{-1} C)`.

**Invariant vectors are zero.** Let `eta` in `H` be invariant and nonzero.
- For small `c > 0`, the set `F_c(x) = {C : |eta_x(C)| >= c}` is finite and equivariant, and it is nonempty on a set
  `Y` of positive measure. `Y` is invariant.
- Let `U = {x in Y : the class of e in V_x belongs to F_c(x)}`. For `x` in `Y`, take `C` in `F_c(x)` and `g` in `C`.
  Then `g^{-1} x` is in `U`, since `V_{g^{-1}x} = g^{-1} V_x` carries the class `g^{-1} C` of `e`. So `U` is a
  complete section of `R|Y`.
- Take `x` in `U`. The points of its `R|U`-class are the `g^{-1} x` with `g` in a class of `F_c(x)`. The points coming
  from one class `C` are pairwise `E`-related, and points coming from distinct classes are not. So each `R|U`-class
  is the union of `|F_c(x)| < infinity` classes of `E|U`.
- `E|U` is hyperfinite, so `R|U` is amenable by [FI], `R|Y` is amenable by [CS], and `Gamma` is amenable by [Z]. This
  is a contradiction. Hence `P = 0` on `H`.

**The bound.** Take `xi_x(C) = (|C cap B_R| / |B_R|)^{1/2}`.
- By invariance, `||xi||^2 = E|V_x cap B_R|/|B_R| = p`.
- `(pi(s) xi)_x(C) = (|C cap s B_R|/|B_R|)^{1/2}`, and `(a^{1/2} - b^{1/2})^2 <= |a - b|`. So
  `||pi(s) xi - xi||^2 <= E sum_C | |C cap B_R| - |C cap s B_R| | / |B_R|`.
- By [T] with `P xi = 0`, `kappa^2 p <= max_s ||pi(s) xi - xi||^2`. This is the general statement.
- For `R = 0`, `xi_x(C) = 1{e in C}`, and the square-root step is an equality. Here
  `||pi(s) xi - xi||^2 = mu(x in V, e and s not in one class) + mu(s^{-1} x in V, s and e not in one class)`.
  Since `e` and `s` lie in one class iff `x in V`, `s^{-1} x in V` and `(x, s^{-1} x) in E`, this equals
  `2(p - tau^E(s))`. Hence `kappa^2 p <= 2 max_s (p - tau^E(s))`, that is, `min_s tau^E(s) <= theta p`.

## 2. Corollary B

- Adjoin independent labels to get a free action `X = omega x b`, with `V = {omega(e) = 1}` (or `V = X` for a bond
  percolation) and `E` the cluster relation. Hyperfiniteness does not depend on the adjoined labels ([HPX], end of
  §C).
- The classes of `E` in `V_x` are the clusters. For a finite window `W`, every window class `K` is contained in a
  cluster. By the triangle inequality under merging, `D_{R,W}(s) >= E sum_C | |C cap B_R| - |C cap s B_R| | / |B_R|`.
- Theorem A gives `max_s D_{R,W}(s) >= kappa^2 p`. That is the negation of the hypothesis `D < kappa^2 p` of [LCF]
  Theorem 1.
- For a hyperfinite subrelation `E'` of the cluster relation, the `E'`-classes refine the clusters. So the sum over
  `E'`-classes dominates the sum over clusters, and Theorem A for `E'` gives the same bound directly.

## 3. Theorem C

**Membership and marginal.** Let `A` and `B` be two independent samples of `mu`, each thinned by coins constant on
`E`-classes. By [HPX] §C each thinned sample is in `W_b`, and so is their union `mu'`. A vertex is open in a thinned
sample with probability `pq`. So `P(e in A cup B) = 1 - (1 - pq)^2 = 1 - (1-p) = p`, since `1 - pq = sqrt(1-p)`.

**Growth.** Suppose `e` and `s` are joined in `mu` by an open path whose vertices are all `E`-related to `e`. The whole
path lies in one coin class, so it survives with probability `q`. Hence `P(e ~ s in A) >= q tau^E_path(s)`, and the
same holds for `B`. Connection in `A` or in `B` gives connection in `A cup B`. By independence,
`tau_{mu'}(s) >= 1 - (1 - q tau^E_path(s))^2 = p f_p(tau^E_path(s)/p)`. The map `f_p` is increasing on
`[0, 1/(qp)]`, which contains `[0, 1]`, so `min_s tau_{mu'}(s) >= p f_p(t^E)`.

**Threshold.**
- The equation `q^2 p t^2 - 2qt + theta = 0` has smaller root `(1 - sqrt(1 - p theta))/(qp) = t_*`, using
  `qp = 1 - sqrt(1-p)`. So `f_p(t) > theta` iff `t > t_*` on `[0, 1]`.
- The function `g(x) = 1 - sqrt(1 - x)` is strictly convex with `g(0) = 0`, so `g(p theta) < theta g(p)`. That is,
  `t_* < theta`.
- Expanding `g(x) = x/2 + x^2/8 + O(x^3)` gives `t_*/theta = (1 + p theta/4)/(1 + p/4) + O(p^2)`. Hence
  `(theta - t_*)/theta = p kappa^2/8 + O(p^2)`.
- The script `experiments/fpbs-hyperfinite-cap-2026-09-17/band.py` checks `f_p(t_*) = theta` to `1e-12` and the
  width against `p kappa^2/8` (within 2% for `p <= 0.01`), for `kappa` in `{0.05, 0.2, 0.5, 1}`.

**Condensation and cost.** If `t^E > t_*`, then `tau_{mu'}(s) > theta p` for every `s`.
- Apply [LCF] Theorem 1 to the free action `mu' x b`, which is ergodic by [HPX] §A. Take `R = 0`, the open vertex
  set, and the induced open subgraph with `F = S`.
- For a finite window `W`, `D_{0,W}(s) = 2(p - P(e, s open and joined inside W))`. This decreases to
  `2(p - tau_{mu'}(s)) < kappa^2 p` as `W` increases to `Gamma`, so some finite `W` meets the hypothesis.
- Theorem 1 gives the finite equivariant set of infinite clusters. It also gives
  `C(mu' x b) <= 1 + E[(deg(e)/2 - 1) 1{e open}] + D/kappa^2 < 1 + (|S|/2 - 1)p + p = 1 + |S|p/2`.
- By [LCF] Corollary 2, since `mu' x b` is weakly contained in `b`, `C(b_Gamma) <= 1 + |S|p/2`.

**The cap.** `tau^E_path <= tau^E`, and Theorem A applies to `E` on `V = {omega(e) = 1}`, so `t^E <= theta`.

## 4. Corollary D

- `mu_1` is Bernoulli(`p`), a factor of iid, so it is in `W_b`. Neighbours that are both open are adjacent, so
  `tau_1(s) = p^2`, that is, `t_1 = p`.
- **Growth holds for exact thinning.** With `E` the full cluster relation, the argument of Section 3 gives
  `t_{i+1} >= f_p(t_i)`, with no hyperfiniteness needed for the inequality. Since `f_p` is increasing,
  `t_i >= f_p^{i-1}(p)`.
- **`n_0` is finite.** On `(0, theta]`, `f_p(t) - t = t(2q - 1 - q^2 p t) >= t(2q - 1 - q^2 p theta) > 0`, because
  `f_p(theta) > theta` (Section 3, `t_* < theta`). The last factor is bounded below on `[p, theta]`, so the iterates
  pass `theta` after finitely many steps.
- **`j_0 <= n_0 + 1`.** If stages `1, ..., n_0 + 1` were all hyperfinite, stage `n_0 + 1` would have `t > theta`,
  contradicting Theorem A.
- **Membership.** `mu_1` is in `W_b`. If `mu_i` is in `W_b` with hyperfinite cluster relation, then `mu_{i+1}` is in
  `W_b` by [HPX] §C. So every stage `i <= j_0` is in `W_b`.
- **(I').** If some stage `i <= j_0` has `t_i > theta`, Section 3 ("Condensation and cost"), applied to `mu_i` itself,
  gives the finite set of infinite clusters and `C(b_Gamma) <= 1 + |S|p/2`.
- **(II').** Otherwise, every stage `i <= j_0` has `t_i <= theta`. For `i < j_0`, stage `i` is hyperfinite and
  `mu_{i+1}` is its exact-coin union. If `t_i > t_*`, then `t_{i+1} >= f_p(t_i) > theta` with `i + 1 <= j_0`, which is
  (I'). So in (II') every `i < j_0` has `t_i <= t_*`.

## 5. The retention inequality with hyperfinite coins

This is the "exact step where it dies" in the claim. For a pair joined in `mu` whose endpoints lie in different
`E`-classes, both endpoints survive the thinning only if both class coins succeed, which has probability `q^2`. So
`P(e ~ s in A) <= q tau^E(s) + q^2 (tau(s) - tau^E(s)) = q^2 tau(s) + q(1-q) tau^E(s)`. For an `s` with
`tau^E(s) <= theta p` (Theorem A), and using `tau(s) <= p`, this is at most `qp(1 - (1-q) kappa^2/2)`. The exact
Hutchcroft--Pete engine needs `q tau(s)`, whose value at the fixed point is `qp`.

## 6. Scope and novelty

- The case `V = X` of Theorem A is folklore: a hyperfinite subrelation cannot almost contain the generators of a
  Kazhdan group.
- The contributions are the density-relative ball-scale form, its consequence that window certificates require
  non-hyperfinite clusters, the band `(t_*, theta]` with its asymptotic width, and the explicit stage bound for the
  exact recursion.
- Nothing here produces a pair `(mu, E)` in the band for any group.
