---
rg: 2
id: linearly-transitive-groups-without-finite-rank-mif-proof
kind: route
title: Follow one vector through the word, defining the variable only on fresh vectors, then extend by linear high transitivity
target: linearly-transitive-groups-without-finite-rank-elements-are-mif
requires: []
---

Notation as in the target: `F` finite with `q` elements, `dim M = ∞`, and
`G <= GL(M)` satisfying (E), (R) and (Z).

## Lemma 1 (avoidance)

Let `S_1, ..., S_r <= M` be subspaces of infinite codimension. Then
`M != S_1 ∪ ... ∪ S_r`.

*Proof.* Choose `c` with `q^c > r`. For each `j`, `M/S_j` is infinite-dimensional, so
there are vectors `w_(j,1), ..., w_(j,c)` whose images in `M/S_j` are linearly
independent. Let `W` be the span of all the `w_(j,k)`, of dimension `d`. The image of
`W` in `M/S_j` has dimension at least `c`, so `dim(W ∩ S_j) <= d - c`. Then
`|W ∩ (S_1 ∪ ... ∪ S_r)| <= r q^(d-c) < q^d = |W|`, so some vector of `W` avoids
every `S_j`. ∎

Every finite-dimensional subspace has infinite codimension. For `g ∈ G`, `λ ∈ F` with
`g != λ` and `B` finite-dimensional, the subspace `(g - λ)^-1(B)` has infinite
codimension: the map `g - λ` induces an injection
`M/(g - λ)^-1(B) -> M/B`, whose image `((g - λ)M + B)/B` is infinite-dimensional
by (R).

## Lemma 2 (one fresh step)

Let `B <= M` be finite-dimensional, `y ∈ M` and `g ∈ G`. If `g y ∈ B + F y`, then
`y ∈ g^-1(B)` or `y ∈ (g - λ)^-1(B)` for some `λ ∈ F^×`. For `g` not a scalar these
are finitely many subspaces of infinite codimension.

*Proof.* `g y = b + λ y` gives `(g - λ) y = b ∈ B`. For `λ = 0` this is `y ∈ g^-1(B)`. ∎

## The construction

Let `w != 1` in `G * <x>`. If `w ∈ G` there is nothing to prove, so write `w` in
reduced form

```text
w = g_0 x^(ε_1) g_1 x^(ε_2) ... g_(n-1) x^(ε_n) g_n,   n >= 1, ε_i = ±1, g_i ∈ G,
```

with `g_i != 1` whenever `ε_i = -ε_(i+1)` (`1 <= i <= n-1`). By (Z), no such `g_i`
is a scalar, which is what Lemma 2 needs. Evaluation reads right to left:
`w(x)v = g_0 x^(ε_1)(g_1 x^(ε_2)(... x^(ε_n)(g_n v)))`.

Fix `v != 0`. For `i = n, n-1, ..., 1` we choose vectors `y_i` and keep a partial
linear isomorphism `x : A_i -> B_i` between finite-dimensional subspaces, starting from
`A_(n+1) = B_(n+1) = 0`. Put `c_n = g_n v` and `c_i = g_i y_(i+1)` for `i < n`.

**Step i.** Inductively `c_i` is *fresh*: `c_i ∉ A_(i+1)` if `ε_i = +1`, and
`c_i ∉ B_(i+1)` if `ε_i = -1`. For `i = n` this holds because `c_n != 0`. Choose `y_i`
avoiding the finitely many subspaces below, all of infinite codimension, which
Lemma 1 allows:

1. **Injectivity:** `y_i ∉ B_(i+1)` if `ε_i = +1`; `y_i ∉ A_(i+1)` if `ε_i = -1`.
2. **Freshness of `c_(i-1)`**, for `i >= 2`:
   - if `ε_(i-1) = ε_i = +1`: `y_i ∉ g_(i-1)^-1(A_(i+1) + F c_i)`;
   - if `ε_(i-1) = ε_i = -1`: `y_i ∉ g_(i-1)^-1(B_(i+1) + F c_i)`;
   - if `ε_(i-1) = +1`, `ε_i = -1`: the subspaces of Lemma 2 for `g = g_(i-1)` and
     `B = A_(i+1)`;
   - if `ε_(i-1) = -1`, `ε_i = +1`: the subspaces of Lemma 2 for `g = g_(i-1)` and
     `B = B_(i+1)`.
   In the last two cases `g_(i-1) != 1` and is not a scalar.
3. **Final vector**, for `i = 1`: `y_1 ∉ F g_0^-1 v`.

Then set:
- if `ε_i = +1`: `x(c_i) = y_i`, `A_i = A_(i+1) + F c_i`, `B_i = B_(i+1) + F y_i`;
- if `ε_i = -1`: `x(y_i) = c_i`, `A_i = A_(i+1) + F y_i`, `B_i = B_(i+1) + F c_i`.

By freshness and item 1, each step adds a new basis vector on both sides, so `x`
stays a linear isomorphism `A_i -> B_i`. Item 2 is exactly freshness of `c_(i-1)`:
- in the equal-sign cases the domain of the next step is `A_i = A_(i+1) + F c_i`, or
  `B_i = B_(i+1) + F c_i`;
- in the mixed-sign cases it is `B_(i+1) + F y_i` or `A_(i+1) + F y_i`, and
  Lemma 2 excludes `g_(i-1) y_i` from it.

## Extension and conclusion

By (E) there is `g ∈ G` with `g|_(A_1) = x`. For every `i`:
- if `ε_i = +1`, then `c_i ∈ A_1` and `g(c_i) = y_i`;
- if `ε_i = -1`, then `y_i ∈ A_1` and `g(y_i) = c_i`, so `g^-1(c_i) = y_i`.

So `g^(ε_i)(c_i) = y_i` for every `i`, and evaluating `w(g)v` right to left gives
`w(g)v = g_0 y_1`. By item 3, `g_0 y_1 != v`. Hence `w(g) != 1`. ∎
