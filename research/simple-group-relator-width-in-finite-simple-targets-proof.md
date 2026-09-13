---
rg: 2
id: simple-group-relator-width-in-finite-simple-targets-proof
kind: route
title: Cover by one relator class with Liebeck--Shalev or Rodgers, after the moved-set collapse makes that class large
target: simple-group-relator-width-in-finite-simple-targets
requires: [liebeck-shalev-normal-subset-covering, simple-group-support-and-semisimple-rank-models-collapse]
---

`G = <X | R>` is infinite, finitely presented and simple. `Cons_K^Q(S)` denotes products of at
most `K` `Q`-conjugates of elements of `S^(+-1)`.

## 0. Two elementary facts

- **(E1) No finite quotient.** For finite `Q` and `a in Q^X`, the generators lie in the normal
  closure of the relator values inside `<a>`. The map `F(X) -> <a> / <<R(a)>>` kills `R`, so
  it factors through `G`. Its image is finite, hence trivial. If every `r(a) = 1`, then
  `a` is a homomorphism from `G` and every `a_x = 1`.
- **(E2) Width in a finite group.** In a finite group `H`, every element of a normal closure
  `<<S>>` is a product of at most `|H|` conjugates of `S^(+-1)`. In a shortest product the
  partial products are distinct.

## 1. Bounded rank and sporadic targets

Let `Q` be finite simple of Lie type of rank `<= rho` over `F_q`, and suppose some
`r(a) != 1`; otherwise (E1) gives `w = 0`.
- **The class is large.** Let `S` be the conjugacy class of `r(a)`. `Q` acts on `S` by
  conjugation, nontrivially. So `C[S]` minus its trivial summand is a nontrivial
  representation, and `|S| - 1 >= c q^(rk Q) >= c q` by item 3 of `liebeck-shalev-normal-subset-covering`.
  The rank of `Q` may be below `rho`; only `|S| >= c q` is used below (review 2026-09-13,
  `research/artifacts/ex-review-backlog-2026-09-13-part2.md` §2.2).
- **The group is not too large.** `|Q| <= q^(D(rho))`, with `D(rho)` the dimension of the
  ambient algebraic group, which is bounded in terms of `rho`.
- **Covering.** So `log|Q| / log|S|` is bounded in terms of `rho` once `q` is large. The finitely
  many groups with small `q` and rank `<= rho` are handled by (E2). Item 1 of the import gives
  `S^k = Q` with `k` bounded in terms of `rho`, so `a_x in S^k`.

Sporadic groups are finitely many and handled by (E2).

## 2. Symmetric targets

Assume `G` is not sofic. Let `eps_0` be the constant of Lemma 1.2 of
`simple-group-support-and-semisimple-rank-models-collapse-proof`: for every permutation tuple,
`max_r |supp r(a)| >= eps_0 |Omega_0|`, where `Omega_0` is the moved set. Let `a in Sym(n)^X`
and `n' = |Omega_0|`.

- **Small moved set.** If `n' <= N_0 := ceil(e^8 eps_0^-4)`, then `<a> <= Sym(Omega_0)` has order
  at most `N_0!`. So (E1) and (E2) give `w <= N_0!`.
- **Large moved set.** Pick `r*` with `s := |supp r*(a)| >= eps_0 n'`.
  - *Cycle count.* Let `c_j` be the number of `j`-cycles of `r*(a)`. Then
    `sum_(j>=2) j c_j = s` and `sum_(j>=2) c_j <= s/2`.
  - *Class size.* Its `Sym(Omega_0)`-class `C` has
    `|C| = n'! / ((n'-s)! prod_(j>=2) j^(c_j) c_j!)`. Using `n'!/(n'-s)! >= s!`,
    `j^(c_j) c_j! <= s^(c_j)` and `s! >= (s/e)^s`,
    ```text
    log|C| >= s log(s/e) - (s/2) log s = (s/2) log s - s .
    ```
  - *Simplify.* With `n' >= N_0` we have `log s >= log n' - log(1/eps_0) >= (3/4) log n'` and
    `s <= (s/8) log n'`. So `log|C| >= (s/4) log n'`.
  - *Rodgers.* Let `k_0 = ceil(24/eps_0) + 1`. For `k >= k_0`,
    `|C|^k > n'^(6(n'-2))`, because `k s/4 > 6 n'` whenever `k > 24/eps_0`. By item 2 of the
    import, `C^k` is `Alt(Omega_0)` or its odd coset, according to the parity of
    `k · sgn(r*(a))`.
  - *Parity.*
    - If `r*(a)` is odd, choose `k in {k_0, k_0 + 1}` matching the parity of `a_x`.
    - If `r*(a)` is even and `a_x` is odd, some relator value `r'(a)` is odd. Otherwise the
      sign map kills every relator, so by (E1) it kills every generator. Write
      `a_x = r'(a) · (r'(a)^-1 a_x)`, with the second factor in `C^(k_0)`.
  - *Result.* Every conjugator lies in `Sym(Omega_0) <= Sym(n)`. So `w <= k_0 + 1`.

So `w_(Sym(n))(a) <= K := max(N_0!, ceil(24/eps_0) + 2)`.

## 3. Alternating targets

Let `a in Alt(n)^X`. The small case is as in Section 2, with `<a> <= Alt(n)`. In the large case
all relator values are even. Let `S` be the `Alt(Omega_0)`-class of `r*(a)`.
- **Class size.** `|S| >= |C|/2`, so `log|S| >= (s/8) log n'` for `n' >= N_0`.
- **Group size.** `log|Alt(Omega_0)| <= n' log n'`.
- **Covering.** Item 1 of the import gives `S^k = Alt(Omega_0)` for `k >= 8c/eps_0`.
  `a_x` is even and supported in `Omega_0`, so it lies in `Alt(Omega_0) <= Alt(n)`.

## 4. Converse of (B), and (C)

- **Converse of (B).** A sofic `G` has permutation models with normalized Hamming defect
  `eps -> 0` and a generator moving a fixed proportion of points. If `w <= K`, every
  generator moves at most `K eps n` points. That is a contradiction for small `eps`, so the
  width is unbounded.
- **(C).** Bi-invariance and the triangle inequality give `l(a_x) <= w_Q(a) max_r l(r(a))`,
  and `l(g_0(a)) <= |g_0| max_x l(a_x)`. So the models' separation forces
  `eps >= 1/(K |g_0|)`.
