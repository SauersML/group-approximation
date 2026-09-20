---
rg: 2
id: f2-cayley-dominance-size-eight-class-proof
kind: route
title: Replace each subgroup by one inside span(S), normalise S to contain 0 and a basis, certify all 38 size-8 classes by exact rational primal and dual LP solutions, and solve the radius-one balls by a two-type mixture against the uniform law on weight-one-and-two vectors via a clique count
target: f2-cayley-dominance-size-eight-class-is-exactly-22-21
requires: []
---

Notation as in the target. The duality inequality used throughout is the easy
direction. For any weights `w >= 0` on `a != 0` with `sum_a w_a d_S(a) > 0`, and any `p`,

```text
max_a E_p 1[a not in H] / d_S(a)  >=  sum_a w_a E_p 1[a not in H] / sum_a w_a d_S(a)
                                   >=  min_H  sum_a w_a 1[a not in H] / sum_a w_a d_S(a).        (D)
```

With `w` uniform on all `a != 0`, the numerator and denominator of (D) are both
`1 - 1/s`, because each is the fraction of pairs `(x, a)` with `x + a` outside the
set. So `C(S) >= 1` in every ambient group.

## Step 1: span reduction (Lemma 1)

Translate so that `0 in S`. This does not change `d_S`. Let `V = span(S)`. `S` has
`s - 1` nonzero elements, which span `V`, so `dim V <= s - 1`. Also `|V| >= s`.

* `C_k(S) <= C_V(S)`. A law `p` on subgroups of `V` is a law on subgroups of
  `F_2^k`. For `a in V` the constraints are unchanged. For `a not in V`, the set
  `S + a` lies in the coset `V + a`, which is disjoint from `S`. So `d_S(a) = 1` and
  `Pr[a not in H] = 1 <= C_V(S) * 1`, since `C_V(S) >= 1`.
* `C_V(S) <= C_k(S)`. Given `H` of size `s` in `F_2^k`, pick a subgroup `H'` with
  `H cap V <= H' <= V` and `|H'| = s`. This is possible since `|H cap V| <= s <= |V|`.
  For `a in V`, `1[a not in H'] <= 1[a not in H]`. Pushing `p` forward along
  `H -> H'` does not increase any ratio with `a in V`. The ratios with `a not in V`
  are at most `1`.

`GL(k,2)` and translations preserve `d_S` and permute the subgroups of size `s`,
so they preserve `C`. Pick `r = dim V` linearly independent elements of `S` and map
them to `e_1, ..., e_r` in `F_2^r`. The other `s - 1 - r` nonzero elements of `S` are
then vectors other than `0` and the `e_i`, that is, vectors of weight at least `2`.
Coordinate permutations fix the set `{0, e_1, ..., e_r}`, so the sets can be
deduplicated under `S_r`. This proves Lemma 1.

## Step 2: the size-8 census (Theorem 2)

`size_class_census.py census 8` enumerates `r = 3, ..., 7` and every choice `T` of
`7 - r` weight-at-least-2 vectors of `F_2^r`, deduplicated under coordinate
permutations (all of `S_r` for `r <= 6`; for `r = 7` there is only the ball). This
gives 38 sets. For each set it produces two certificates in exact arithmetic
(`Fraction`).

* **Upper certificate.** Column generation solves the LP. Pricing is exact: it
  evaluates `y(H)` on all `[r,3]_2` subgroups, which is `11811` at `r = 7`. The
  primal `p` is rationalised with `limit_denominator` and renormalised. Then
  `max_a Pr_p[a not in H]/d_S(a)` is computed exactly, taking the maximum with `1`.
* **Lower certificate.** The dual `y` is rationalised. The right side of (D) is then
  evaluated with exact integer arithmetic over every subgroup of size `8` of `F_2^r`.

The output `census_s8.out` lists all 38 classes. For every class the lower and
upper certificates coincide, so each `C(S)` is an exact rational. The largest value
is `22/21`. With Step 1, this proves Theorem 2.

## Step 3: the ball family (Proposition 3)

Let `m = s - 1`, `M = C(m,2)` and `S = B_s`. Then `x in S` with `x + a in S` happens
only as follows.

* For `a = e_i`, exactly when `x in {0, e_i}`.
* For `a = e_i + e_l`, exactly when `x in {e_i, e_l}`.
* For `|a| >= 3`, never.

So `d(a) = 1 - 2/s` on the `m + M = C(s,2)` vectors of weight 1 or 2, and `d(a) = 1`
otherwise.

**Clique count.** A `j`-dimensional subspace `H` of `F_2^m` contains at most
`C(j+1,2)` vectors of weight 1 or 2.

* Take the vertex set `[m] u {inf}`. Code `e_i` as the edge `{i, inf}` and
  `e_i + e_l` as the edge `{i, l}`. Let `G` be the set of edges whose vectors lie in
  `H`.
* The sum of the vectors of two edges `{x,y}` and `{y,z}` is the vector of `{x,z}`.
  Since `H` is closed under addition, every component of `G` is a clique.
* Drop the `inf` coordinate, `phi : F_2^([m] u {inf}) -> F_2^m`. Its kernel is
  spanned by `1_inf`, which has odd weight, so `phi` is injective on even-weight
  vectors. The edge vectors of a clique on `n` vertices span the even-weight vectors
  on those vertices, a space of dimension `n - 1`. Cliques on disjoint vertex sets
  give independent spans.
* Hence `sum_l (n_l - 1) <= j`, and the number of edges is `sum_l C(n_l,2)`. Since
  `C(a+b+1,2) - C(a+1,2) - C(b+1,2) = ab >= 0`, the count is at most `C(j+1,2)`.

`ball_family_check.py` confirms this exhaustively for
`(m,j) in {(5,2),(6,3),(7,3),(7,4),(8,3),(8,4)}`.

**Lower bound.** Take `w` uniform on the `C(s,2)` vectors of weight 1 or 2. Then
`Phi_w(S) = 1 - 2/s`. For every `H`, `Phi_w(H) >= 1 - C(j+1,2)/C(s,2) = 1 - v`, with
`v = j(j+1)/(s(s-1))`. By (D), `C(B_s) >= (1-v)/(1-2/s)`.

**Upper bound.** Take `lambda = (j+1)/s`, which is at most `1`. With probability
`lambda`, let `H = span{e_i : i in T}` for a uniform `j`-set `T`. Otherwise let `H`
be the even-weight vectors supported on a uniform `(j+1)`-set `T`. Both have
dimension `j`, and `j + 1 <= m` since `s >= 4`. Then

```text
Pr[e_i in H]       = lambda j / m                              = j(j+1)/(s(s-1)) = v,
Pr[e_i + e_l in H] = (lambda C(j,2) + (1-lambda) C(j+1,2)) / M = (C(j+1,2) - lambda j)/M
                   = j(j+1)(s-2) / (s (s-1)(s-2))               = v.
```

So the ratio is `(1 - v)/(1 - 2/s)` on weight 1 and 2, and at most `1` elsewhere.

The two bounds meet:

```text
C(B_s) = max(1, (1-v)/(1-2/s)) = (s(s-1) - j(j+1)) / ((s-1)(s-2)),
```

because `j(j+1) <= 2(s-1)` for every `j >= 2`, so the maximum is the second term.
The certified LP at `s = 8` returns `22/21 = 22/21` (`ball_family_check.py`).
