---
rg: 2
id: subgroup-average-projections-reduced-bc-proof
kind: route
title: Invariant square-summable vectors vanish, induction from a finite orbit, and a faithful trace
target: subgroup-average-projections-give-no-reduced-bc-obstruction
requires:
  - kazhdan-projections-vanish-in-regular-group-algebra
---

**Part 1.**
- Take a finite symmetric Kazhdan set `S` for `Lambda`,
  `T = |S|^-1 sum_(s in S) u_s` and `a = (1 + T)/2`.
- The powers `a^n` converge in `C*_max(Lambda)` to `p_Lambda`, which acts in
  every representation as the projection onto the invariant vectors
  (`kazhdan-projection-finite-target-calculus-proof`).
- `lambda` is continuous, so `lambda(p_Lambda) = lim lambda(a)^n` is the
  projection onto the `Lambda`-invariant vectors of `l^2(G)`.
- That projection is `0` by `kazhdan-projections-vanish-in-regular-group-algebra`:
  an invariant vector is constant on the infinite cosets `Lambda g`, hence
  not square-summable unless it is zero.

**Part 2.**
- `G/H` is a proper cocompact `G`-space with
  `K^G_0(G/H) = K_0(C* H) = R(H)`.
- On this orbit the assembly map is induction along `C* H -> C*_r G`. It sends
  the trivial representation, the projection `|H|^-1 sum_h u_h` of `C* H`, to
  `[p_H]`.
- The orbit maps equivariantly to `Ebar G`, so by naturality `[p_H]` lies in
  the image of `mu_r`.
- Conjugation by `u_g` does not change K-classes.

**Part 3.**
- `tau(x^* x) = ||x delta_e||^2`. The right translation unitaries commute with
  `C*_r G` and carry `delta_e` to every `delta_g`. So `x delta_e = 0` forces
  `x = 0`, and `tau` is faithful.
- `tau (x) Tr` is a faithful trace on `M_n(C*_r G)`.
- If `v^*v = p` and `v v^* <= p`, then
  `tau(p - v v^*) = tau(v^* v) - tau(v v^*) = 0` with `p - v v^* >= 0`, so
  `v v^* = p`.
- For a strict compression, the `Gamma`-invariant vectors are
  `t Gamma t^-1`-invariant, and `u_t p_Gamma u_t^*` is the projection onto the
  latter. So `p_Gamma <= u_t p_Gamma u_t^*` in `C*_max G`.
- For infinite Kazhdan `Gamma`, both sides map to `0` under `lambda` by part 1.
