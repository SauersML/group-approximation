---
rg: 2
id: simple-group-psl-width-is-finite-field-linear-soficity-proof
kind: route
title: Cover commutators of a fixed template, proportional case by Liebeck--Shalev on the projective collapse, near-scalar case after displacing the moved subspace
target: simple-group-psl-width-is-finite-field-linear-soficity
requires: [liebeck-shalev-normal-subset-covering, simple-group-support-and-semisimple-rank-models-collapse, simple-group-relator-width-in-finite-simple-targets]
---

`G = <X | R>` is infinite, finitely presented and simple. `Cons_K(S)` is the set of products of at most
`K` `Q`-conjugates of elements of `S^(+-1)`. `c` is the constant of item 1 of
`liebeck-shalev-normal-subset-covering`. (E1), (E2) are the two facts of
`simple-group-relator-width-in-finite-simple-targets-proof`, Section 0: generators lie in the normal
closure of the relator values, and in a finite group `H` every element of a normal closure is a product
of at most `|H|` conjugates.

## 0. Uniform collapse (Theorem item 0)

Lemmas 2.1 and 2.2 of `simple-group-support-and-semisimple-rank-models-collapse-proof` do not mention
the field: their constants depend only on `X`, `R` and the integers `c_(x,r)`.
- **Varying fields.** Suppose tuples `a^(i)` over finite fields `F_(q_i)` with `M_i > 0` and relator
  ratio `delta_i -> 0`. The proof of Lemma 2.3 runs verbatim.
  - Some fixed generator has normalized rank at least `eta/|X|` on `Z_i = V_i/U_i`.
  - Relators have normalized rank below `delta_i/eta`.
  - Along `omega` this gives a nontrivial homomorphism `G -> prod_omega GL(Z_i)/N_omega`. It is
    injective by simplicity, so `G` is linear sofic over finite fields.
- **Projective form.** It follows by the adjoint argument of item 4, which applies item 3 to `Ad(a)`
  over the same field.
- **Fixed characteristic.** If every `q_i` is a power of `p`, restriction of scalars to `F_p` gives
  `F_p`-linear soficity instead.

## 1. The template

`H_1(G) = 0`, so `x in [F, F] <<R>>` for each `x in X`. Fix, once for all `x`, words with
```text
x = [u_(x,1), v_(x,1)] ... [u_(x,J), v_(x,J)] · n_x   in F(X),   n_x a product of J' conjugates of R^(+-1).
```
For every group `Q` and `a in Q^X`: `a_x = prod_j [u_(x,j)(a), v_(x,j)(a)] · n_x(a)` with
`n_x(a) in Cons_(J')(R(a))`.

**(T) If every commutator `[u(a), v(a)]` of template words lies in `Cons_(K_1)(R(a))`, then
`w_Q(a) <= J K_1 + J'`.**

**(Z) Centre trick.** Let `Z` be central in `Q`, `S` a normal subset of `Q`, and `u in S^k Z`. Write
`u = s z` with `s in S^k`. Then `[u, v] = [s, v] = s · (v s^-1 v^-1)`, a product of `2k` conjugates of
elements of `S^(+-1)`.

A tuple in `SL_n(q)/Z_0` lifts to `SL_n(q)`, and `Cons_K` in `SL_n(q)` maps into `Cons_K` in the quotient.
So it suffices to treat `Q = SL_n(q)`. Assume (i), and let `delta_0 <= 1` be the uniform constant of
Section 0. Put `eta = delta_0/(16|X|)` and `D = ceil(32|X|/delta_0) + 3`. Then `D^2 >= 32 D |X|/delta_0 >= 8/eta`.

## 2. Class sizes in `GL_d(q)`

For `h in GL_d(q)`, the centralizer is the unit group of the centralizer algebra `C(h)`. By the Jordan
count in the proof of item 4 of the collapse theorem, `dim C(h) <= d max(d - rho(h), d/2)`. So
```text
|h^(GL_d(q))| >= |GL_d(q)| / q^(dim C(h)) >= c_0 q^(d min(rho(h), d/2)),   c_0 = prod_(i>=1)(1 - 2^-i) > 1/4 .
```
- The `SL_d(q)`-class has at least `|h^(GL_d)|/(q - 1)` elements, because
  `|C_(GL)(h) : C_(SL)(h)| <= q - 1`.
- Its image in `PSL_d(q)` has at least `|h^(GL_d)|/(q - 1)^2` elements.
- So if `h in SL_d(q)`, its image class `Sbar` satisfies
  ```text
  log|Sbar| >= d min(rho(h), d/2) log q - 2 log q - log 4 ,   log|PSL_d(q)| <= d^2 log q .   (2.1)
  ```

## 3. Bounded rank

Let `n < D`, and fix a template commutator `[u(a), v(a)]`.
- **Central relators.** If every relator value is central, then by (E1) in `PSL_n(q)` every `a_x` is
  central. Every commutator is then `1`.
- **A non-central relator.** Otherwise its class `Sbar` in `PSL_n(q)` is nontrivial.
  - Let `(n, q)` be outside the finitely many pairs with `q < q_1(D)`. By item 3 of the import,
    `|Sbar| - 1 >= c' q^(n-1)`, which is `>= q^(1/2)` for `q >= q_1(D)`.
  - So `Sbar^k = PSL_n(q)` with `k <= 2 c D^2`, and (Z) gives `[u(a), v(a)] in Cons_(4cD^2)`.
- **Small cases.** The finitely many pairs with `q < q_1(D)`, and `SL_2(2)`, `SL_2(3)`, are bounded by
  (E1) and (E2) with `K <= max |SL_n(q)|`.

## 4. Proportional case: `P := max_x rho(a_x) >= n/(8|X|)`

- **A relator far from the scalars.** By Section 0, some relator value `h = r*(a)` has
  `rho(h) >= (delta_0/2) min(P, n/2) >= eta n`.
- **Class size.** Assume `n >= D` (otherwise Section 3 applies), so `n^2 >= 8/eta`. By (2.1),
  `log|Sbar| >= eta n^2 log q - 4 log q >= (eta/2) n^2 log q`.
- **Covering.** Liebeck--Shalev gives `Sbar^(k_1) = PSL_n(q)` with `k_1 = ceil(2c/eta)`. So every
  `u(a) in S^(k_1) Z`, and by (Z) every commutator lies in `Cons_(2 k_1)(R(a))`.

## 5. Near-scalar case: `P < n/(8|X|)`

If `P = 0`, every `a_x` is scalar and every commutator is `1`. Assume `P >= 1`.

**5.1 Divide out scalars.**
- Choose `lambda_x in F_q^x` with `rk(a_x - lambda_x) = rho(a_x)`, and put `b_x = lambda_x^-1 a_x in GL_n(q)`.
- For every word, `u(a) = lambda_u u(b)` with `lambda_u` a scalar. So `[u(a), v(a)] = [u(b), v(b)]` and
  `r(a) = lambda_r r(b)`.
- `max_x rk(b_x - 1) = P`.

**5.2 Localize.**
- Put `U = ∩_x ker(b_x - 1)` (codimension `<= |X| P`), `I = sum_x im(b_x - 1)` and `C` a complement
  of `U`. Let `W = I + C`, so `d_0 = dim W <= 2|X| P`.
- Each `b_x^(+-1)` maps `W` into `W + I = W`. Since `W + U = V`, a complement `W'` of `W ∩ U` in `U`
  gives `V = W (+) W'`.
- So every word in `b` lies in `GL(W) x 1_(W')`.
- `d_0 >= 1` and `4 d_0 < n`.

**5.3 A relator of rank proportional to `P`.** Item 3 of Section 0 for the tuple `b` gives `r*` with
`t := rk(h_0 - 1) >= delta_0 P`, where `h_0 = r*(b)`. Also `t <= d_0`.

**5.4 Displacement.**
- Split `W' = W_1 (+) W_3 (+) W_4` with `dim W_1 = d_0` and `dim W_3 = d - 2 d_0`, where
  `d = max(4 d_0, D)`. Assume `n >= D` (otherwise Section 3 applies), so `d <= n`. Choose an
  isomorphism `sigma : W -> W_1`.
- Define `y` by `y(w + w_1) = -sigma^-1 w_1 + sigma w` on `W (+) W_1`, and the identity on `W_3 (+) W_4`.
  Its determinant is `(-1)^(d_0) det(-sigma^-1) det(sigma) = 1`, so `y in SL_n(q)`.
- Then
  ```text
  h := [r*(a), y] = [h_0, y] = h_0 · y h_0^-1 y^-1 = h_0|_W (+) sigma h_0|_W^-1 sigma^-1 (+) 1_(W_3 (+) W_4),
  ```
  and `h in Cons_2(R(a))`.
- `h` lies in `SL(W''') x 1`, with `W''' = W (+) W_1 (+) W_3` of dimension `d`.
  - `rk(h - 1) = 2t`.
  - The fixed space of `h` on `W'''` has dimension `>= d - 2t >= d/2`.
  - For `lambda != 1`, `rk(h|_(W''') - lambda) >= d/2 >= 2t`.
  - So `rho(h|_(W''')) = 2t <= d/2`.

**5.5 Cover in `SL(W''')`.** Let `S` be the `SL(W''')`-class of `h|_(W''')`. It is non-central.
- **Rank against dimension.**
  - If `d = 4 d_0`, then `d <= 8|X| P` and `2td >= 2 delta_0 P d >= delta_0 d^2 / (4|X|)`.
  - If `d = D > 4 d_0`, then `2td >= 2 delta_0 d >= 2 delta_0 d^2 / D`.
  - Either way `2td >= delta_0 d^2 / (4|X| D)`.
- **Class size.** By (2.1),
  `log|Sbar| >= (delta_0/(4|X|D)) d^2 log q - 4 log q >= (delta_0/(8|X|D)) d^2 log q`, because
  `d >= D` gives `(delta_0/(8|X|D)) d^2 >= delta_0 D/(8|X|) >= 4`.
- **Covering.** Liebeck--Shalev in the simple group `PSL_d(q)` (`d >= 3`) gives `Sbar^(k_2) = PSL(W''')`
  with `k_2 = ceil(8c|X|D/delta_0)`.
- **Commutators.** Take template words `u`, `v`, and put `delta_u = det(u(b)|_W)`.
  - Let `u~ = u(b)|_W (+) diag(delta_u^-1, 1, ..., 1)` on `W (+) (W_1 (+) W_3)`, with the diagonal on a
    fixed basis of `W_1 (+) W_3`. Define `v~` likewise.
  - Then `u~, v~ in SL(W''')`, and diagonal matrices commute, so
    `[u~, v~] = [u(b)|_W, v(b)|_W] (+) 1`. This is `[u(a), v(a)]` restricted to `W'''`.
  - `u~ in S^(k_2) Z(SL(W'''))`. By (Z), `[u(a), v(a)]` is a product of `2 k_2` `SL(W''')`-conjugates
    of `h^(+-1)`.
  - Conjugators in `SL(W''') x 1_(W_4) <= SL_n(q)` are allowed. With `h in Cons_2(R(a))`, this gives
    `[u(a), v(a)] in Cons_(4 k_2)(R(a))`.

## 6. Conclusion of (i) => (ii), and the converse

- **(i) => (ii).** By (T), `w_Q(a) <= J max(4 c D^2, 2 k_1, 4 k_2, max_(n<D, q<q_1) |SL_n(q)|) + J'`. No
  constant depends on `n` or `q`. Under "not `F_p`-linear sofic", Section 0 gives `delta_0` uniform over
  `F_(p^e)`, and the same proof gives item 2.
- **(ii) => (iii).** For a bi-invariant length, `l(a_x) <= K max_r l(r(a))`, as in part (C) of
  `simple-group-relator-width-in-finite-simple-targets`.
- **(iii) => (i).** Suppose `G` embeds in `prod_omega GL_(n_i)(F_(q_i))/N_omega`, with generator lifts `a^(i)`.
  - Relators have `rk(r(a^(i)) - 1) <= eps_i n_i` with `eps_i -> 0` along `omega`. Some `x_0` has
    `rk(a^(i)_(x_0) - 1) >= alpha n_i`.
  - Put `a~_x = a_x (+) 1_(n_i) (+) a_x^(-T) in SL_(3 n_i)(q_i)`. Then `rho(r(a~)) <= 2 eps_i n_i`, and
    `rho(a~_(x_0)) >= min(2 alpha n_i, n_i)`, because `1_(n_i)` forces `rk(a~ - lambda) >= n_i` for
    `lambda != 1`.
  - `rho` is invariant under scalars and conjugation and subadditive, so `l = rho/(3 n_i)` is a
    bi-invariant length on `PSL_(3 n_i)(q_i)`. These are weak models, contradicting (iii).
  - The same estimate shows `w` is unbounded, contradicting (ii) directly.
