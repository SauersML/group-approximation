---
rg: 2
id: leavitt-kazhdan-relative-commutant-no-type-one-proof
kind: route
title: Place a Thompson II_1 factor in the grown commutant and count unital matrix units
target: leavitt-kazhdan-relative-commutant-has-no-type-one-part
requires: [openai-nine-leaf-leavitt-configuration, binary-leavitt-full-character-simplex, thompson-v-character-simplex]
---

**Reduction to a regular character.**  By the character classification,
the GNS algebra of `tau o sigma` on `sigma(G)''` is `C (+) L(G)`, with weights
`lambda` and `1 - lambda`.  Let `q` be the central support of the regular
summand.  It commutes with `sigma(G)`, so `g -> sigma(g) q` is a model in
`qMq` with regular character.  From now on assume `tau o sigma = delta_e`.

**Item 1.**

* Restricting `delta_e` to `V_1` gives its regular character, so
  `sigma(V_1)'' ~= L(V_1) ~= L(V)`.
* `V` is an infinite simple finitely generated group, hence ICC: its
  FC-centre is normal, so it is trivial or all of `V`.  A finitely generated
  FC group has finite commutator subgroup, while `V` is perfect and infinite.
  So `L(V)` is a II_1 factor.  `thompson-v-character-simplex` records the same
  fact at the level of characters.
* `J` commutes with `Gamma`, so `V_1 = u J u^(-1)` commutes with
  `u Gamma u^(-1)`, and `sigma(V_1) <= A_1`.
* `V_1 <= Gamma` (`openai-nine-leaf-leavitt-configuration`), so `sigma(V_1)`
  commutes with `A_0`.

**Item 2.**  Put `N = sigma(V_1)''`, a factor commuting with `A_0`.  For
`a in A_0` and `y in N`,
`E_N(a) y = E_N(a y) = E_N(y a) = y E_N(a)`, so
`E_N(a) in N cap N' = C`.  Hence `E_N(a) = tau(a)` and
`tau(a y) = tau(E_N(a) y) = tau(a) tau(y)`.  Commuting subalgebras that are
independent for a faithful trace generate their tensor product:
`A_0 v N ~= A_0 (tensor) N`.

Both factors lie in `A_1` (item 1 and `A_0 <= A_1`), and
`Ad sigma(u) : A_0 -> A_1` is a trace-preserving isomorphism.

For `k >= 2`, `V_j = u^j J u^(-j)` with `1 <= j <= k` gives pairwise commuting
factors `sigma(V_j)'' ~= L(V)`:

* each commutes with `A_0`, since `V_j <= Gamma`, and lies in `A_j <= A_k`;
* for `i < j`, `V_i` commutes with `Gamma_i`, and
  `V_j <= Gamma_(j-1) <= Gamma_i`.

Each `sigma(V_j)''` is a factor commuting with `A_0 v sigma(V_1)'' v ... v sigma(V_(j-1))''`,
so the independence argument above applies inductively.  That gives
`A_0 (tensor) L(V)^(tensor k) <= A_k`.

**Item 3.**  `J` commutes with `Gamma`, so `sigma(J)'' ~= L(V)` is a unital
II_1 factor inside `A_0`.  Let `e` be a central projection of `A_0` with
`A_0 e` of type I, say `A_0 e = (+)_m L^infinity(X_m) (tensor) M_m`.

* `L(V)` contains a unital copy of `M_k` for every `k`.  Since `e` is central
  and `M_k` is simple, `x -> x e` embeds `M_k` unitally into `A_0 e`.
* Cutting by each central summand, `M_k` embeds unitally into
  `L^infinity(X_m) (tensor) M_m` whenever that summand is nonzero, which
  forces `k | m`.
* Taking `k = m + 1` kills the summand.  So `e = 0` and `A_0` is of type II_1.
* `A_1 ~= A_0` via `Ad sigma(u)`, so `A_1` is of type II_1 too.

**Item 4.**  For fixed `m`, let `z_n` be the central projection of `A_n`
collecting its summands of size at most `m`, and `z = [z_n]`.

* `z` is central in `prod_omega A_n = A_0`.
* Every `A_n z_n` satisfies the standard polynomial identity `s_(2m)`
  (Amitsur--Levitzki).  A multilinear identity holding coordinatewise holds in
  the ultraproduct, so `A_0 z` satisfies `s_(2m)`.
* A von Neumann algebra satisfying a polynomial identity is of type I
  (Kaplansky), which by item 3 forces `z = 0`, i.e. `lim_omega tau(z_n) = 0`.
