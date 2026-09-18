---
rg: 2
id: higman-derived-length-three-edge-collapse-proof
kind: route
title: A b-d-b conjugation chain carries a triple commutator of the opposite pair to a word with nonzero exponent sum, reducing derived length 3 to the metabelian collapse
target: higman-derived-length-three-edge-images-collapse
requires:
  - virtually-metabelian-edge-images-collapse-higman-quotients
  - nilpotent-edge-images-collapse-higman-quotients
artifacts:
  - experiments/higman-two-sided-ladder-2026-09-18/ladder.py
  - experiments/higman-two-sided-ladder-2026-09-18/ladder-output.txt
---

Conventions: `x^y = y^-1 x y` and `[x,y] = x^-1 y^-1 x y`.

Let `Q = H4/R` and write `a, b, c, d` for the images. Fix `m >= 1`, and put

```text
alpha = a^m,  gamma = c^m,  P = 2^m >= 2,  N_j = 2^(P^j) (j >= 0),  A = <alpha, gamma> <= Q.
```

**Assume** `A''' = 1`. We prove `Q = 1`.

Let `Phi` be the free group on two letters, also written `alpha, gamma`, and let `ev : Phi -> Q` be
the evaluation map. For a word `u` in `alpha^±1, gamma^±1`:
- the **`alpha`-height** of a letter is the net `alpha`-exponent of the prefix before it;
- the **`gamma`-height** of a letter is the net `gamma`-exponent of the prefix before it.

## Step 1 (relations)

- **The `b` side.** From `a^-1 b a = b^2` we get `alpha^-1 b alpha = b^P`, so
  `alpha^-j b alpha^j = b^(P^j)` for `j >= 0`. From `b^-1 c b = c^2` we get `b^-n gamma b^n = gamma^(2^n)`.
  Put `gamma_j = alpha^j gamma alpha^-j`. For `j >= 0`,

  ```text
  b^-1 gamma_j b = alpha^j (alpha^-j b^-1 alpha^j) gamma (alpha^-j b alpha^j) alpha^-j = alpha^j b^(-P^j) gamma b^(P^j) alpha^-j = gamma_j^(N_j).
  ```

- **The `d` side.** In the same way, `d^c = d^2` and `a^d = a^2` give
  `d^-1 alpha_i d = alpha_i^(N_i)` for `i >= 0`, where `alpha_i = gamma^i alpha gamma^-i`.

**Substitution maps.**
- For a word `w`, let `iota_b(w)` replace each letter `gamma^ε` at `alpha`-height `j` by
  `gamma^(ε N_j)`. This is defined when every `gamma`-letter has `alpha`-height `>= 0`.
- `iota_d` is the mirror image: each `alpha^ε` at `gamma`-height `i` becomes `alpha^(ε N_i)`. It is
  defined when every `alpha`-letter has `gamma`-height `>= 0`.

**Lemma 1.** Let `w` have `alpha`-exponent sum 0, with every `gamma`-letter at `alpha`-height `>= 0`.
Then `ev(iota_b(w)) = b^-1 ev(w) b`. The mirror statement holds for `iota_d` and `d`.

*Proof.* `w` is freely equal to `prod_k gamma_(j_k)^(ε_k)`, where the `k`-th `gamma`-letter has sign
`ε_k` and height `j_k >= 0`. Also `iota_b(w)` is freely equal to `prod_k gamma_(j_k)^(ε_k N_(j_k))`,
because it has the same `alpha`-letters in the same places. Apply Step 1. ∎

`iota_b` keeps the `alpha`-letters and their `alpha`-heights. It changes the `gamma`-heights.

## Step 2 (two counts)

Let `u` be a word.

**The count `E`.** If `u` has `alpha`-exponent sum 0, put
`E(u) = sum over gamma-letters l of ε_l X^(alpha-height(l)) in Z[X^±1]`.
- `E(u)` is invariant under free reduction.
- It is the image of `u` in `P/P' ≅ Z[X^±1]`, where `P` is the kernel of `Phi -> <alpha>`, free on the
  `gamma_j`.
- `E^d` is the mirror count, over `alpha`-letters by `gamma`-height, into `P_d/P_d'`.

**The count `S`.** For a `gamma`-letter `l`, let `kappa(l) : Z -> Z` be the finitely supported function
whose value at `h` is the net exponent of the `alpha`-letters before `l` that have `gamma`-height `h`. Put

```text
S(u) = sum over gamma-letters l of ε_l t^(kappa(l))   in the group ring Z[Z^(Z)],  t^kappa = prod_h t_h^(kappa_h).
```

Inserting `x x^-1` does not change `S`: two cancelling `gamma`-letters carry the same `kappa`, and an
inserted `alpha alpha^-1` has no `gamma`-letter between its two letters. So `S` is invariant under free
reduction. Let `kappa_fin(u)` be the value of `kappa` after the whole word. Then `kappa_fin(u) = 0`
exactly when `E^d(u) = 0`.

**Lemma 2 (the `d`-step computes `E` from `S`).**
- **Hypotheses.** `v` has `gamma`-exponent sum 0, every `alpha`-letter of `v` has `gamma`-height
  `>= 0`, and `kappa_fin(v) = 0`.
- **Conclusion.** `u = iota_d(v)` has exponent sums `(0, 0)`, and

  ```text
  E(u) = S(v) evaluated at t_h -> X^(N_h).
  ```

*Proof.*
- The `gamma`-letters of `u` are those of `v`.
- Before a `gamma`-letter `l`, the prefix of `u` has `alpha`-exponent `sum_h N_h kappa(l)_h`, since each
  `alpha^ε` at `gamma`-height `h` became `alpha^(ε N_h)`.
- The total `alpha`-exponent of `u` is `sum_h N_h kappa_fin(v)_h = 0`. ∎

`ladder.py` (`brute_force_check`) confirms Lemma 2 by direct expansion on 300 random words
`v = [r_1, r_2]`, with `r_i` random products of `alpha_0^±1, alpha_1^±1, alpha_2^±1` and `P = 2`.

**Lemma 3 (separation).** Let `delta : Z -> Z` be nonzero and finitely supported on `[h_1, ∞)`, with
`h_1 >= 0` and `||delta||_1 < N_(h_1)`. Then `sum_h delta_h N_h != 0`.

*Proof.*
- Let `H` be the largest `h` with `delta_h != 0`.
- If `H = h_1`, the sum is `delta_H N_H != 0`.
- Otherwise `|sum_(h<H) delta_h N_h| <= ||delta||_1 N_(H-1) < N_(h_1) N_(H-1) <= N_(H-1)^2 <= N_(H-1)^P = N_H`,
  while `|delta_H N_H| >= N_H`. ∎

## Step 3 (the chain)

Let `x = gamma_1 gamma_0^-1`, `y = gamma_0^-1 gamma_1` and `x_2 = gamma_0 gamma_1 gamma_0^-2`. These lie
in `Phi'`. Put

```text
w_0 = [[x, y], [y, x_2]]  in Phi''',
```

a reduced word of length 56 (printed in `ladder-output.txt`). Its `gamma`-letters have `alpha`-heights
0 and 1, and its exponent sums are `(0, 0)`. Since `A''' = 1`, `ev(w_0) = 1`.

**(a) The first `b`-step.** Put `u_1 = iota_b(w_0)`. By Lemma 1, `ev(u_1) = b^-1 ev(w_0) b = 1`.
- `w_0` lies in the free factor `P_(>=0) = <gamma_j : j >= 0>` of `P`, and `Phi''' <= P''` because
  `Phi' <= P`. The retraction `P -> P_(>=0)` kills the other basis elements, so
  `w_0 in P_(>=0) ∩ P'' = P_(>=0)''`.
- On `P_(>=0)`, `iota_b` is the endomorphism `gamma_j -> gamma_j^(N_j)`. So
  `u_1 in P_(>=0)'' <= Phi''`.
- Hence `u_1` has exponent sums `(0, 0)`. It also lies in `P_d'`, because `Phi' <= P_d`, so
  `kappa_fin(u_1) = 0`.

**(b) The `d`-step.** Let `n_0 >= 0` be such that every `alpha`-letter of `u_1` has `gamma`-height
`>= -n_0`. For `n >= n_0`, put `v_1 = gamma^n u_1 gamma^-n` and `u_2 = iota_d(v_1)`. By Lemma 1,
`ev(u_2) = 1`.
- **Shift of `S`.** The `n` leading `gamma`-letters have `kappa = 0`. The `n` trailing letters
  `gamma^-1` have `kappa = kappa_fin(u_1) = 0`. So these cancel in `S`, and `S(v_1)` is `S(u_1)` with every
  height shifted up by `n`.
- **Lemma 2.** It applies to `v_1`, so `u_2` has exponent sums `(0, 0)`, and
  `E(u_2) = sum_kappa s_kappa X^(sum_h N_(h+n) kappa_h)`, where `S(u_1) = sum_kappa s_kappa t^kappa`.
- **Separation.** Suppose `S(u_1) != 0`. Let `B` be the largest `||kappa||_1` over its support.
  Choose `n` so that `N_(n - n_0) > 2B`. For distinct support elements `kappa != kappa'`, the difference
  `delta = kappa - kappa'` has `||delta||_1 <= 2B`, and after the shift it is supported on heights
  `>= n - n_0 >= 0`.
- By Lemma 3 the exponents are pairwise distinct, so no terms merge, and **`E(u_2) != 0`**.

**(c) The second `b`-step.** Write `E(u_2) = sum_j e_j X^j`, and let `J` be its top degree. Choose
`n' >= 0` so that every `gamma`-letter of `u_2` has `alpha`-height `>= -n'`, and so that
`N_(J-1+n') > ||e||_1`. Put `v_2 = alpha^(n') u_2 alpha^(-n')` and `u_3 = iota_b(v_2)`.
- By Lemma 1, `ev(u_3) = 1`.
- The `alpha`-exponent sum of `u_3` is 0, and its `gamma`-exponent sum is

  ```text
  Y := sum_j e_j N_(j+n').
  ```

- `Y != 0`. If `E(u_2)` has one term this is clear. Otherwise
  `|sum_(j<J) e_j N_(j+n')| <= ||e||_1 N_(J-1+n') < N_(J-1+n')^2 <= N_(J+n') <= |e_J N_(J+n')|`.

So `u_3` is a word with exponent sums `(0, Y)`, `Y != 0`, and `ev(u_3) = 1`. Since
`u_3 gamma^-Y in Phi'`, we get **`gamma^Y in A'`**.

**(d) The mirror chain.** The relations of Step 1 are symmetric under `alpha <-> gamma`, `b <-> d`.
Let `sigma` swap the letters `alpha, gamma`. Running (a)–(c) on `sigma(w_0) in Phi'''` with `d, b, d`
produces `sigma(u_3)`, with `ev(sigma(u_3)) = 1` and exponent sums `(Y, 0)`. So **`alpha^Y in A'`**.

## Step 4 (nonvanishing of `S(u_1)`)

This is the only input that is specific to `w_0`. It is certified by `ladder.py`; see
`ladder-output.txt`.
- **Exact runs, `m = 1, 2, 3, 4` (`P = 2, 4, 8, 16`).** `u_1 = iota_b(w_0)` is built explicitly, of
  length 116, 284, 3644 and 917564. In each case `S(u_1)` has 24 nonzero monomials.
- **Check at `m = 1`.** For `m = 1` and the minimal shift `n = 6`, the script also computes `E(u_2)`
  exactly, with exponents up to 1025 bits. It has 24 nonzero terms, which confirms (b) directly.
- **All `m >= 2` (symbolic).**
  - The `gamma`-letters of `w_0` sit at `alpha`-heights 0 and 1. So in `u_1` the `gamma`-height of an
    `alpha`-letter is `2p + Mq`. Here `M = N_1 = 2^P`, and `p, q` are the net `gamma`-exponents of the
    earlier `gamma`-letters of `w_0` at heights 0 and 1.
  - Each block `gamma^(ε N_j)` carries a constant `kappa`, so it contributes `ε N_j t^kappa`.
  - Hence `S(u_1)` is the pushforward, along `(p, q) -> 2p + Mq`, of a formal sum whose keys are
    functions of pairs `(p, q)` and whose coefficients have the form `2 c_0 + M c_1`.
  - The script finds 24 formal keys, with `p`-range 3. For `M > 6` the map `(p, q) -> 2p + Mq` is
    injective on the occurring pairs: if `q != q'`, then `|M(q - q')| > 6 >= |2(p - p')|`. So
    distinct keys stay distinct.
  - Some coefficient `2 c_0 + M c_1` is nonzero for every `M > 6`.
  - Since `M = 2^(2^m) >= 16` for `m >= 2`, `S(u_1) != 0` for all `m >= 2`.
- **Other choices of `w_0`.** Two other choices, `[[x,y],[x_2,y_2]]` and `[[x_2,y_2],[y,x_2]]` with
  `y_2 = gamma_1^-1 gamma_0 gamma_1^-1 gamma_0`, also give `S(u_1) != 0` at `P = 2`.

## Step 5 (conclusion: item 1)

- **`A/A'` is finite.** It is abelian and generated by the images of `alpha` and `gamma`, both of
  order dividing `|Y|`.
- **`A'` is metabelian.** `(A')'' = A''' = 1`.
- **The metabelian collapse applies.** `<a^(m|Y|), c^(m|Y|)> = <alpha^Y, gamma^Y> <= A'` is
  metabelian. By item 1 of `virtually-metabelian-edge-images-collapse-higman-quotients`, applied with
  exponent `m|Y| >= 1`, `Q = 1`.
- **The pair `<b^m, d^m>`.** The automorphism `theta : a -> b -> c -> d -> a` of `H4` handles it.

## Step 6 (items 2–4)

**Item 2.** Take `Q = H4 / ncl(F''')` and `m = 1`. Then `A''' = 1`, so `Q = 1`.

**Item 3.**
- Let the image of `<a,c>` have a subgroup of finite index with derived length `<= 3`. Its normal
  core `A_0` has finite index `m` and derived length `<= 3`.
- Then `x^m in A_0` for every `x`, so `<a^m, c^m> <= A_0` satisfies `<a^m, c^m>''' = 1`, and item 1
  gives `Q = 1`.
- For `<b,d>`, apply `theta`.

**Item 4.**
- By item 2 (tree gate) of `nilpotent-edge-images-collapse-higman-quotients`, if `Q` acts on a tree
  without inversions and fixes no vertex, some edge stabilizer contains `<a,c>` or `<b,d>`.
- That subgroup is then virtually of derived length `<= 3`, and item 3 gives `Q = 1`.
- A nontrivial amalgam or HNN splitting gives a Bass--Serre tree action without inversions and without
  a global fixed point.

## Calibration

- **`k = 2` (the known metabelian collapse).** Run the chain one step shorter:
  - take `w_0 in Phi''`, for example `[x,y]` or `[x_2,y_2]`;
  - `u_1 = iota_b(w_0)` has `E^d(u_1) != 0` in `P_d/P_d'` (computed for `P = 2, 4, 8`);
  - one `d`-step then gives exponent sums `(X_0, 0)` with `X_0 != 0`, by the dominance argument of (c).

  With the mirror chain, `<alpha^(X_0), gamma^(X_0)> <= A'`, which is abelian. That is a metabelian
  power pair, so `Q = 1`. This reproduces the conclusion of
  `virtually-metabelian-edge-images-collapse-higman-quotients` for the powers `a^(m|X_0|), c^(m|X_0|)`
  by a different mechanism, as a check of the chain.
- **One side alone does not suffice.** A single `b`-step keeps `F'''` inside `P''`, and the `b`-side
  normal closure of `F^(k)` meets `F` inside `P^(k-1)` (`higman-b-side-derived-closure-stays-in-bottom-layer`).
  The `d`-step in (b) is the two-sided ingredient: it turns the formal sum `S(u_1)`, which sees
  `P''`-level structure, into a nonzero element of the abelian layer `P/P'`.
- **The commuting analogue.** With commuting pairs in place of the `BS(1,2)` relations, `N_j = 1` for
  all `j`. Then `iota_b` is the identity, `u_3` stays in `Phi'''`, and the chain yields nothing, as it
  must, since `Z^4` is a nontrivial quotient.

## Toward general derived length

For `A^(k) = 1` the same chain has `k` half-steps: `b, d, b, ...`.
- **Descent.** `u_1 in P^(k-1) <= Phi^(k-1)`. Then `u_2 in P_d^(k-2) <= Phi^(k-2)`, and so on, until
  `u_k` has exponent sums `(0, Y)` or `(Y, 0)`.
- **What is needed.** The step `A^(k) = 1  =>  Q = 1` follows from the case `k - 1`, applied to
  `A' ⊇ <alpha^Y, gamma^Y>`, once `Y != 0`. By repeated use of Lemmas 2–3, `Y != 0` reduces to the
  nonvanishing of an order-`(k-2)` formal invariant of `u_1`.
- **Example (`k = 4`).** The invariant is `sum over alpha-letters lambda of ε_lambda s^(h(lambda)) T^(Gamma(lambda))`,
  where `Gamma(lambda)` records, for each `kappa`, the net `gamma`-exponent of the earlier
  `gamma`-letters with that `kappa`.
- **Open.** This is proved here only for `k = 3`.
