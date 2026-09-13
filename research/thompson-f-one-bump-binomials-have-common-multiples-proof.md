---
rg: 2
id: thompson-f-one-bump-binomials-have-common-multiples-proof
kind: route
title: Slope 1/2 at 0 absorbs the germ at 0 and conjugation by g is phi^n near 1, so Guba's count runs; a self-similar conjugacy turns slope 2^-m into 1/2 on a normal subgroup of index m
target: thompson-f-one-bump-binomials-have-common-multiples
requires: [thompson-f-rescaled-x0-binomials-have-common-multiples]
---

Notation as in the target and in `thompson-f-rescaled-x0-binomials-have-common-multiples-proof`.
- Composition is right to left, so `t^-1 g t` has support `t^-1(supp g)`. `R` is a domain.
- `M` is the positive monoid, `M_j` its submonoid on letters `>= j`, and `phi(x_i) = x_(i+1)`.
  `x_i` has support `(1 - 2^-i, 1)`, so `M_j ⊆ F_[1-2^-j,1]`.
- `tau(y) = (y + 1)/2`. By Lemma C of that route, `tau h tau^-1 = phi(h)` for all `h` in `F`.
- For `f` in `F`, `e(f)` is the integer with `f(t) = 2^(e(f)) t` near `0`. It is a
  homomorphism `F -> Z`.

**Step 0 (coset test for any `g ≠ 1`).** For `mu` in `K^x` put `J = (g - mu) R`. Then `y` lies
in `J` iff `sum_n y(g^n h) mu^n = 0` for every right coset `<g> h`.
- `F` is torsion-free, so `K[<g>] = K[t, t^-1]`, and `R = ⊕_(cosets) K[<g>] h` as a left
  `K[<g>]`-module. On one coset the ideal is `(t - mu) K[t, t^-1]`, the Laurent polynomials
  vanishing at `mu`.
- *Consequence.* `g^k y - mu^k y` lies in `J` for all `y` in `R` and all `k` in `Z`.

**Proposition 1.** Let `g` be one-bump on `(0,1)` with `g(t) < t` and `g(t) = t/2` near `0`.
Then `(1 + lambda g) R ∩ b R ≠ 0` for every `lambda` in `K^x` and every nonzero `b`.

Put `mu = -1/lambda`, so `J = (g - mu) R = (1 + lambda g) R`. Fix `n >= 1` and dyadic `c_0 < 1`
with `g(t) = A(t) := 1 - 2^n (1 - t)` on `[c_0, 1]`. It suffices to find `v ≠ 0` with `b v`
in `J`, since then `b v ≠ 0`.
- *Step 1 (germ at 0).* `g^e` is `t -> 2^-e t` near `0`, so `g^(e(f)) f` is the identity near
  `0`. By Step 0, `f ≡ mu^(-e(f)) g^(e(f)) f` modulo `J`. So `b ≡ b_1` modulo `J`, where
  `b_1 = sum_f b(f) mu^(-e(f)) g^(e(f)) f` is supported in `F_[eps,1]` for some dyadic `eps > 0`.
  Any `v` with `b_1 v` in `J` has `b v` in `J`.
- *Step 2 (push toward 1).* Fix `j` with `1 - 2^-j >= c_0`. Since `g^-1(t) > t` on `(0,1)`,
  `g^-k(eps) -> 1`, so some `k >= 0` has `g^-k(eps) >= 1 - 2^-j`. Put `b_2 = g^-k b_1 g^k`,
  supported in `F_[1-2^-j,1]`. If `b_2 w` lies in `J`, so does `mu^-k b_1 g^k w` by Step 0,
  and `v = g^k w` works for `b_1`.
- *Step 3 (positive monoid).* Conjugation by `tau^j`, affine of slope `2^-j` from `[0,1]` onto
  `[1 - 2^-j, 1]`, maps `F` onto `F_[1-2^-j,1]` and `M` onto `M_j`. Transporting the survey's
  Lemma 3.8 gives `s` in `F_[1-2^-j,1]` with `supp(b_2 s) ⊆ M_j`. Put `b_3 = b_2 s`. Then
  `b_3 R = b_2 R`, and `b_3 w'` in `J` gives `w = s w'`.
- *Step 4 (shift).* For `h` in `F_[c,1]` with `c >= c_0`, `g^-1 h g = tau^n h tau^-n = phi^n(h)`.
  - Both sides are the identity on `[0, A^-1(c)]`. On `[A^-1(c), 1]`, `g = A` and `h g` lands
    in `[c, 1]`, where `g^-1 = A^-1`, so both equal `A^-1 h A`. And `A^-1 = tau^n`.
  - `phi^n` maps `K[M_i]` into `K[M_(i+n)]`, so by induction `b_3 g^k = g^k phi^(nk)(b_3)` for
    all `k >= 0`.
- *Step 5 (dependence gives a solution).* Let `r_0, ..., r_N` in `K[M_1]` be not all zero with
  `sum_k phi^(nk)(b_3) r_k = 0`, and put `w' = sum_k mu^-k g^k r_k`.
  - `b_3 w' = sum_k mu^-k g^k phi^(nk)(b_3) r_k`, which is congruent to
    `sum_k phi^(nk)(b_3) r_k = 0` modulo `J` by Step 0.
  - `w' ≠ 0`: if `g^k m = g^l m'` with `m, m'` in `M_1 ⊆ F_[1/2,1]`, then `g^(k-l)` fixes
    `[0, 1/2]`, so `k = l`.
- *Step 6 (count).* This is Step 5 of
  `thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof` with the shift `phi^n`.
  Let the monomials of `b_3` have letters `<= I` and degrees `<= D`. Given `L`, put
  `c = floor(L/2)`, `N = floor((L - I - c - D)/n)`, and let `A` be the set of normal forms of
  degree `c` with letters in `[1, L]`.
  - Inserting `x_i` into a word of length `l` gives a normal form whose new letter is at most
    `i + l`, and the other letters are unchanged. So for `k <= N`, `a` in `A` and a monomial `t`
    of `phi^(nk)(b_3)` of degree `d`, `t a` is a normal form of degree `c + d` with letters in
    `[1, I + nN + c + D] ⊆ [1, L]`.
  - Unknowns `(r_k)` with `r_k` in `K[A]`: dimension `(N + 1)|A|`. Target: dimension at most
    `sum_(d=0)^D binom(L + c + d - 1, c + d) <= (4^(D+1)/3) |A|` once `L + 1 >= 2D`, as there.
  - `N + 1 >= (L/2 - I - D)/n` grows with `L`, so the linear map has a nonzero kernel.

**Lemma 2 (slope `2^-m` at 0).** Fix `m >= 1` and let `H_m = {f in F : m | e(f)}`, a normal
subgroup of index `m`. There is an increasing homeomorphism `varphi` of `[0,1]` with
`varphi H_m varphi^-1 = F` and `varphi(2^-m t) = varphi(t)/2`.
- Let `varphi_0 : [2^-m, 1] -> [1/2, 1]` be PL with finitely many dyadic breakpoints and slopes
  in `2^Z`. It exists: send the intervals `[2^-i, 2^(1-i)]`, `i = m, ..., 1`, in increasing
  order and affinely onto `[1 - 2^-i', 1 - 2^-(i'+1)]`, `i' = 1, ..., m - 1`, followed by
  `[1 - 2^-m, 1]`. Both lists consist of `m` intervals whose lengths are powers of `2`.
- Put `varphi(0) = 0` and `varphi(t) = 2^-k varphi_0(2^(mk) t)` on `[2^(-m(k+1)), 2^(-mk)]`,
  `k >= 0`. The pieces agree at the junctions because `varphi_0(2^-m) = 1/2` and
  `varphi_0(1) = 1`. On each `[delta, 1]` with `delta > 0`, `varphi` has finitely many dyadic
  breakpoints and slopes in `2^Z`, and it maps dyadic rationals onto dyadic rationals.
- Let `f` be in `H_m` with `e(f) = mk`. For small `t`, `f(t) = 2^(mk) t` and
  `varphi(2^(mk) t) = 2^k varphi(t)`, so `varphi f varphi^-1(y) = 2^k y` near `0`. Away from `0`
  it is a composite of finitely many dyadic PL pieces. So `varphi f varphi^-1` is in `F`, with
  `e = k`. The same argument puts `varphi^-1 h varphi` in `H_m` for `h` in `F`.
- So conjugation by `varphi` is an isomorphism `psi : H_m -> F` with `e(psi(f)) = e(f)/m`. It
  fixes `0` and `1` and preserves order, so it maps one-bump elements on `(0,1)` below the
  diagonal to one-bump elements on `(0,1)` below the diagonal.

**Proposition 3 (every slope, support `(0,1)`).** Let `g` be one-bump on `(0,1)`. Then
`(1 + lambda g) R ∩ b R ≠ 0` for every `lambda` in `K^x` and every nonzero `b`.
- *`g(t) > t`.* `1 + lambda g = lambda g (1 + lambda^-1 g^-1)`, so
  `(1 + lambda g) R ∩ b R = g [(1 + lambda^-1 g^-1) R ∩ g^-1 b R]`, as in Lemma C of the
  `O_1` route. So assume `g(t) < t`, and put `m = -e(g) >= 1`.
- For `t` in `supp b`, `c_t = t^-1 g t` lies in `H_m`, is one-bump on `(0,1)` below the diagonal,
  and has `e(c_t) = -m`. So `psi(c_t)` is one-bump on `(0,1)` below the diagonal and equals
  `y -> y/2` near `0`.
- List `supp b = {t_1, ..., t_s}`. Put `v'_1 = 1 + lambda psi(c_(t_1))`. Given a nonzero
  `v'_(i-1)`, Proposition 1 gives a nonzero `v'_i` in `(1 + lambda psi(c_(t_i))) R ∩ v'_(i-1) R`.
  Then `v' = v'_s` is nonzero and lies in every `(1 + lambda psi(c_t)) R`.
- `v = psi^-1(v')` lies in `K[H_m] ⊆ R`. From `v' = (1 + lambda psi(c_t)) y_t` we get
  `v = (1 + lambda c_t) psi^-1(y_t)`, so `v` lies in every `(1 + lambda c_t) R`.
- `t (1 + lambda c_t) = (1 + lambda g) t`, so `b v = sum_t b(t) t v` lies in `(1 + lambda g) R`,
  and `b v ≠ 0`.

**Item 1 (every support).** Let `g` be one-bump on `(p, q)`.
- `p` and `q` are dyadic: at `p` the map `g` is the identity on one side and linear of slope
  `≠ 1` on the other, so `p` is a breakpoint or `0`, and likewise `q`.
- Choose `theta : [p, q] -> [0, 1]` PL with finitely many dyadic breakpoints and slopes in `2^Z`,
  by matching dyadic subdivisions as for `varphi_0`. Conjugation by `theta` is an isomorphism
  `F_[p,q] -> F_[0,1] = F`, and `theta g theta^-1` is one-bump on `(0,1)`.
- Proposition 3 is property O for `theta g theta^-1`. Lemma B of the `O_1` route transports it
  to `g`. So `g` is in `O_1`.

**Item 2.** With `O_1` equal to all one-bump elements, items 1–3 of
`thompson-f-rescaled-x0-binomials-have-common-multiples` are items 2(a)–(c).

**Item 3.** `alpha u + beta w = alpha (1 + (beta/alpha) w u^-1) u`, and right unit factors do
not change principal right ideals, so item 2(b) applies.

**Trust surfaces.**
- Quoted: the normal form of `M` and `M ⊆ F`, the survey's Lemma 3.8, left-orderability of
  `F`, and from the `O_1` route Lemma B, `tau h tau^-1 = phi(h)` and the supports of `x_i`.
- Everything else is proved above.
