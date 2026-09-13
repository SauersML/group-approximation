---
rg: 2
id: free-kernel-extensions-modular-finiteness-proof
kind: route
title: Separate the kernel augmentation ideal by p-group quotients, count ranks on sofic models, and fold doubles onto free kernels
target: free-kernel-extensions-keep-modular-stable-finiteness
requires: []
---

Throughout, `D` is a division ring of characteristic `p`, group elements commute with `D` in
`D[W]`, and matrices over `D` act on columns with scalars on the right.

## 1. Separated ideals

Let `R` be unital, `J` a two-sided ideal with `intersection_m J^m = 0`, and `R/J` stably finite.
If `BA = I_n` over `R`, then `AB = I_n` modulo `J`, so `E = I_n - AB` lies in `M_n(J)`. From
`BA = I_n` we get `E^2 = E`, so `E = E^m` lies in `M_n(J^m)` for every `m`, and `E = 0`. The case
`n = 1` gives the directly finite version.

## 2. The kernel ideal is separated

Let `w = omega(N)`, the augmentation ideal of `D[N]`.

- **Finite p-groups.** For a finite `p`-group `P`, `omega(P)` is nilpotent. Induct on `|P|`. Pick
  `z` central of order `p`. It commutes with `D`, so `z - 1` is central in `D[P]` and
  `(z-1)^p = z^p - 1 = 0` in characteristic `p`. Put `K = (z-1)D[P]`, so `K^p = 0` and
  `D[P]/K = D[P/<z>]`. By induction `omega(P)^m <= K` for some `m`, hence `omega(P)^(mp) = 0`.
- **Separation.** Let `0 != u in D[N]` with finite support `S`. Separate the finitely many
  `s^-1 t` (`s != t` in `S`) by finite `p`-group quotients and take the product map
  `phi : N -> P`. It is injective on `S`, so `phi(u) != 0`. Since `phi(w^m) <= omega(P)^m = 0`
  for large `m`, `u` is not in `w^m`. So `intersection_m w^m = 0`.
- **Pass to `W`.** Conjugation by `W` preserves `N` and fixes `D`, so `D[W] w = w D[W]`. Hence
  `J = w D[W]` is a two-sided ideal and `J^m = w^m D[W]`. For a right transversal `T` of `N`,
  `D[W] = directSum_(t in T) D[N] t` as a left `D[N]`-module, so `w^m D[W] = directSum_t w^m t`.
  Therefore `intersection_m J^m = directSum_t (intersection_m w^m) t = 0`.
- **Quotient.** `x = sum_t x_t t` maps to `0` in `D[Q]` iff every `x_t` has coefficient sum `0`,
  i.e. `x_t in w`. So `D[W]/J = D[Q]`, and Section 1 gives item 1.

## 3. Free groups are residually finite p-groups

Let `v = x_(i_1)^(a_1) ... x_(i_k)^(a_k)` be reduced (`k >= 1`, `i_j != i_(j+1)`, `a_j != 0`).
Killing the other basis elements is a retraction onto a free group of finite rank `r` that fixes
`v`.

- **Magnus expansion.** Send `x_i` to `1 + X_i` in `F_p<<X_1..X_r>>`. Write `a_j = p^(s_j) u_j`
  with `p` not dividing `u_j`. Then `(1+X)^(p^s) = 1 + X^(p^s)`, and the series binomial theorem
  gives `(1 + Y)^u = 1 + uY + O(Y^2)` for `u` of either sign. So factor `j` is
  `1 + u_j X_(i_j)^(p^(s_j))` plus higher powers of `X_(i_j)^(p^(s_j))`.
- **Leading coefficient.** Put `M = X_(i_1)^(p^(s_1)) ... X_(i_k)^(p^(s_k))`, a word with exactly
  `k` maximal letter blocks. A term of the expanded product picks exponents `e_j p^(s_j)`
  (`e_j >= 0`). Its word has at most `#{j : e_j > 0}` blocks, so it equals `M` only if every
  `e_j > 0` and then every `e_j = 1`. The coefficient of `M` is therefore
  `u_1 ... u_k != 0`.
- **Finite quotient.** Let `d = deg M` and `A = F_p<X>/(monomials of degree > d)`. The `1 + X_i`
  are units of `A`, giving `F_r -> 1 + (X)A`. That group is finite of order a power of `p`, and
  the image of `v` has nonzero `M`-coefficient, so it is not `1`.
- **Free abelian groups.** For `0 != v in directSum_X Z`, reduce its finitely many coordinates
  modulo `p^k > max |v_x|`.

## 4. Sofic groups over division rings

Suppose `BA = I_m` and `E = I_m - AB != 0` in `M_m(D[Q])`. Let `S` contain `1` and all supports
of `A`, `B` and their products, and fix an entry `e = sum_(q in S_E) c_q q != 0` of `E`, where
every `c_q != 0`.

- **Model.** Take `sigma : Q -> Sym(n)` with `sigma(1) = id` (normalizing costs `epsilon`), with
  `sigma(s)sigma(t)` and `sigma(st)` differing in at most `epsilon n` columns for `s, t in S`, and
  `sigma(q)v != sigma(q')v` for all but `epsilon n` points `v` when `q != q'` in `S`. Extend
  `P(sum c_q q) = sum c_q sigma(q)` entrywise to matrices.
- **Upper bound.** Each defect `sigma(s)sigma(t) - sigma(st)` has rank at most `epsilon n`. So
  `P(B)P(A) = I + R_1` and `P(A)P(B) = I - P(E) + R_2`, with `rk R_i <= C epsilon n` and `C`
  depending only on `A` and `B`.
- **Rank swap.** Over a division ring `rk(I - ab) = rk(I - ba)`: `v -> bv` maps `ker(I - ab)`
  injectively into `ker(I - ba)` (if `bv = 0` then `v = abv = 0`), and symmetrically. Hence
  `rk P(E) <= rk R_1 + rk R_2 <= 2C epsilon n`.
- **Lower bound.** At the at least `(1 - |S_E|^2 epsilon)n` good points, where the `sigma(q)v`
  (`q in S_E`) are distinct, the column `v` of `P(e)` has support `R_v = {sigma(q)v}`, all
  entries nonzero. Take a maximal set `V` of good points with pairwise disjoint `R_v`. These
  columns are independent. By maximality every good point lies in
  `{sigma(q')^-1 sigma(q) v : v in V}`, so `rk P(E) >= rk P(e) >= |V| >=
  (1 - |S_E|^2 epsilon) n / |S_E|^2`.
- For small `epsilon` the two bounds contradict, so `AB = I_m`. This is item 3.

## 5. Doubles and trivial HNN extensions

Let `x_0 = Gamma in X = G/Gamma`, and `F` free on `e_x` (`x in X`) with `e_(x_0) = 1`.

- **Action.** `alpha_g(e_x) = e_(gx) e_(g x_0)^-1` is an action: `alpha_g alpha_h = alpha_(gh)`
  and `alpha_g(e_(x_0)) = 1`.
- **Maps.** `Phi(g) = (1, g)` and `Phi(ghat) = (e_(g x_0)^-1, g)` respect products in the second
  copy, and agree on `Gamma` since `gamma x_0 = x_0`. The reverse map is `Psi(g) = g` and
  `Psi(e_(g x_0)) = g ghat^-1`. This is well defined, because `gamma` and `gammahat` coincide in
  the double, and it respects `alpha`: `h g ghat^-1 h^-1 = (hg)(hg)hat^-1 (h hhat^-1)^-1`.
- **Compositions.** Both are the identity on generators.
- **HNN.** For `<G, t | [t, Gamma]>`, use `F(X)` with `alpha_g(e_x) = e_(gx)`,
  `t -> (e_(x_0), 1)` and `e_(g x_0) -> g t g^-1`. The same checks apply.
- **Conclusion.** In each group of item 4 the kernel is free or free abelian, hence residually a
  finite `p`-group by Section 3, and `G` is a retract. `D[G]` is a unital subring, which gives
  one direction; Section 2 gives the other. `QED`
