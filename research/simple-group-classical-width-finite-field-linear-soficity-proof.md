---
rg: 2
id: simple-group-classical-width-finite-field-linear-soficity-proof
kind: route
title: Cover double commutators by a commutator seed with a large fixed space, counted through fixed-space stabilizers
target: simple-group-classical-width-finite-field-linear-soficity
requires: [liebeck-shalev-normal-subset-covering, simple-group-psl-width-is-finite-field-linear-soficity, simple-group-relator-width-in-finite-simple-targets]
artifacts:
  - research/artifacts/classical-relator-width-part1-class-sizes-2026-09-13.md
  - research/artifacts/classical-relator-width-part2-commutator-choice-2026-09-13.md
---

Lemma numbers `1.x`–`3.x` refer to part 1 and `4.x`–`5.x` to part 2 (artifacts above). `G = <X | R>`
is infinite, finitely presented, simple, and not linear sofic over finite fields. `delta_0 <= 1` is
the uniform constant of item 0 of `simple-group-psl-width-is-finite-field-linear-soficity`, which
gives both collapse inequalities over every finite field. `c` is the Liebeck--Shalev constant and `c'`
the minimal-degree constant (items 1 and 3 of `liebeck-shalev-normal-subset-covering`). (E1), (E2) and
`Cons_K` are as in `simple-group-relator-width-in-finite-simple-targets-proof`. `V`, `F`, `q_F`, `I(V)`
and `Q_0` are as in part 1, Section 0.

**Standard fact used, not re-read.** For `d >= 9`, `I(W)'` is `Sp_d(q)`, `SU_d(q)` or `Omega^+-_d(q)`,
and its quotient by the centre is a nonabelian simple group. The targets are the groups `Q_0/Z_0`
with `Q_0 = Sp, SU, Omega` and `Q_0/Z(Q_0)` simple. Each satisfies `I(V)' <= Q_0 <= I(V) ∩ SL(V)`, and
`Z_0` is central of order `<= q + 1`, as a group of scalars `lambda` with `lambda^dagger lambda = 1`
(Kleidman--Liebeck, Chapter 2). A tuple in `Q_0/Z_0` lifts to `Q_0`, and `Cons_K` in `Q_0` maps
into `Cons_K` in the quotient. So we bound `w_(Q_0)(a)` for `a in Q_0^X`, with conjugators in `Q_0`.

## 1. Template and centre trick

`G` is perfect, so `G = G''`. Fix, for every `x in X`, words `c_(x,j)` and `c'_(x,j)` in `[F(X), F(X)]`
(`j <= J`), and `n_x`, a product of `J'` conjugates of `R^(+-1)`, with
`x = prod_j [c_(x,j), c'_(x,j)] · n_x` in `F(X)`.
- **(T2)** If each `[c(a), c'(a)]` lies in `Cons_(K_1)(R(a))`, then `w_(Q_0)(a) <= J K_1 + J'`.
- **(Z)** If `Z` is central in a group `H` and every element of `H` is `s z`, with `s` a product of at
  most `k` `H`-conjugates of `h^(+-1)` and `z in Z`, then every commutator in `H` is a product of at
  most `2k` `H`-conjugates of `h^(+-1)`.

## 2. Bounded dimension, `n < N_1`

Here `N_1 = ceil(480/eta)` and `eta = delta_0/(40|X|)`.
- **Central relators.** If every `r(a)` is central, (E1) in `Q_0/Z(Q_0)` makes every `a_x` central.
  Every commutator is then `1`.
- **A non-central relator.** Otherwise some `h = r(a)` has nontrivial class `Sbar` in the simple
  quotient, and `|Sbar| - 1 >= c' q`.
  - For `q >= q_1 = ceil(c'^-2)`, `log|Sbar| >= (1/2) log q` and `log|Q_0| <= 2 N_1^2 log q`.
    Liebeck--Shalev and (Z) give `K_1 <= 8 c N_1^2`.
  - The finitely many groups with `q < q_1` give `K_1 <= 2 max |Q_0|`, by (E2) in the simple quotient
    and (Z).

## 3. Proportional regime, `n >= N_1` and `P := max_x rho(a_x) >= n/(20|X|)`

- **The relator.** The projective collapse gives `h = r*(a)` with
  `rho(h) >= (delta_0/2) min(P, n/2) >= eta n`.
- **The seed.** Lemma 4.2 with `r' = floor(eta n/6)`, which is at least `3` and at most `n/16`, gives
  `y in I(V)' <= Q_0`. The seed `k = [h, y] in Cons_2(R(a))` has `s = rk(k - 1)` with
  `eta n/12 <= s <= n/4`.
- **Class size.** By Lemma 3.2, `log|k^(Q_0)| >= (eta n^2/24 - 3n - 4) log q`. Dividing by
  `|Z_0| <= q + 1`,
  ```text
  log|Sbar| >= (eta n^2/24 - 3n - 8) log q >= (eta/48) n^2 log q ,
  ```
  using `log 4 + log(q + 1) <= 4 log q` and `n >= 480/eta`.
- **Covering.** `log|Q_0/Z_0| <= 2 n^2 log q`, and `k` is non-central (it is `!= 1` and has fixed
  vectors). So Liebeck--Shalev gives `Sbar^(k_1) = Q_0/Z_0` with `k_1 = ceil(96 c/eta)`.
- **Commutators.** By (Z), `[c(a), c'(a)] in Cons_(4 k_1)(R(a))`.

## 4. Near-central regime, `n >= N_1` and `P < n/(20|X|)`

- **Trivial case.** If `P = 0`, every `a_x` is central and every commutator is `1`. Assume `P >= 1`.
- **Divide out scalars.** Choose `lambda_x` with `rk(a_x - lambda_x) = rho(a_x) < n/3`. By Lemma 5.1,
  `b_x = lambda_x^-1 a_x in I(V)`.
  - Scalars are central, so `[c(a), c'(a)] = [c(b), c'(b)]` and `r(a) = lambda_r r(b)`.
  - `max_x rk(b_x - 1) = P`.
- **Localize.** Lemma 5.2 gives a nondegenerate `W` with `d_0 = dim W <= 2|X| P`, such that all words
  in `b` lie in `I(W) x 1`. So `c(b)` and `c'(b)` lie in `I(W)' x 1`.
- **The relator.** The linear collapse for `b` gives `r*` with `h_0 = r*(b)` and
  `delta_0 P <= t = rk(h_0 - 1) <= d_0`.
- **Displace.** Lemma 5.3 with `d' = d_0` applies, because `9 d_0 + 2 <= 18|X|P + 2 < n`. It gives
  `W'''` of dimension `d = 9 d_0` and `y in I(V)' <= Q_0`, with
  ```text
  h := [r*(a), y] = [h_0, y] in Cons_2(R(a)),   h in I(W''') x 1,   rk(h - 1) = 2t .
  ```
- **The local group.** Put `H = I(W''')'`. Then `H x 1 <= I(V)' <= Q_0`, and `c(b)|_(W''')` lies in
  `I(W)' x 1 <= H`.
  - `h` is non-central in `H`: `h != 1`, and it fixes a subspace of dimension `d - 2t >= 7 d_0`.
  - By the standard fact, `H/Z(H)` is simple for `d >= 9`.

**4a. Large local dimension, `d_0 >= D_0 = ceil(16|X|/delta_0)`.**
- **Support.** `s = 2t` satisfies `delta_0 d/(9|X|) <= s <= 2 d_0 <= d/4`.
- **Class size.** Lemma 3.2 in `W'''`, then division by the centre, gives
  ```text
  log|Sbar| >= (delta_0 d^2/(18|X|) - 3d - 8) log q >= (delta_0/(36|X|)) d^2 log q ,
  ```
  since `d >= 9 D_0 >= 144|X|/delta_0` gives `delta_0 d/(36|X|) >= 4 >= 3 + 8/d`.
- **Covering.** Liebeck--Shalev covers `H/Z(H)` with `k_2 = ceil(72 c|X|/delta_0)`.
- **Commutators.** By (Z) in `H`, with conjugators in `H x 1 <= Q_0`,
  `[c(b), c'(b)] in Cons_(4 k_2)(R(a))`.

**4b. Bounded local dimension, `1 <= d_0 < D_0`.**
- **Large `q`.** `9 <= d < 9 D_0`. The class of `h` in `H/Z(H)` is nontrivial, so `|Sbar| >= c' q`.
  For `q >= q_1`, `K_1 <= 8 c (9 D_0)^2`.
- **Small `q`.** Finitely many `H`, and (E2) with (Z) gives `K_1 <= 4 max |H|`.

## 5. Conclusion

- **The bound.** `w_(Q_0)(a) <= J max(8cN_1^2, 2 max_(n<N_1, q<q_1) |Q_0|, 4k_1, 4k_2, 8c(9D_0)^2, 4 max |H|) + J'`,
  independent of `n`, `q`, the form type and `a`.
- **Fixed characteristic.** Under "not `F_p`-linear sofic", item 0 of the special linear theorem gives
  `delta_0` uniform over `F_(p^e)`. This includes `F_(q^2)` for unitary groups, and the same proof gives
  the uniform bound over `q = p^e`.
