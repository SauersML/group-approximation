# Classical relator width, part 2: commutator choice, localization, displacement

Lane `ex-weak-sofic-classical-covering`, 2026-09-13. Part 2 of 3. The setting and lemma numbers are
those of `research/artifacts/classical-relator-width-part1-class-sizes-2026-09-13.md`.
`rho(g) = min_(lambda in F) rk(g - lambda)` is the rank distance to the scalars.

## 4. Commutator choice

**Lemma 4.1 (rank of a commutator).** For `h, y in GL(V)` with `K = ker(y - 1)`,
```text
dim K - dim(K ∩ hK) <= rk([h, y] - 1) <= 2 rk(y - 1) .
```

*Proof.* Put `N = y - 1`.
- `[h, y] - 1 = (h y h^-1 - y) y^-1`, and `h y h^-1 - y = h N h^-1 - N`. So both ranks are equal.
- **Lower bound.** On `hK`, `h N h^-1` vanishes, so the operator restricts to `-N|_(hK)`. Its rank is
  `dim hK - dim(hK ∩ K)`.
- **Upper bound.** Each of the two terms has rank `rk N`.

**Lemma 4.2 (commutator choice).** Let `n >= 32`, `h in I(V)`, and `r'` an integer with
`3 <= r' <= min(rho(h)/6, n/16)`. Then there is `y in I(V)'` with `rk(y - 1) = 2r'` and
`r' <= rk([h, y] - 1) <= 4 r'`.

*Proof.*

**Greedy hyperbolic pairs.** We build pairs `(e_j, f_j)`, `j = 1, ..., r'`, such that:
- each `(e_j, f_j)` is a hyperbolic pair orthogonal to all earlier pairs;
- `e_j`, `h e_j` and `f_j` are linearly independent modulo
  `S_(j-1) = span(e_i, f_i, h e_i, h f_i : i < j)`, which has `dim S_(j-1) <= 4(j - 1)`.

Let `R = span(e_i, f_i : i < j)^perp`. It is nondegenerate, of dimension `n - 2(j-1) >= 28`.

- **Choosing `e_j`.**
  - *Failures.* `e in R` fails if `e in S_(j-1)` or `h e in S_(j-1) + F e`. In the second case
    `(h - lambda) e in S_(j-1)` for some `lambda in F`. So `e` lies in `(h - lambda)^-1(S_(j-1))`, of
    dimension at most `dim ker(h - lambda) + dim S_(j-1) <= n - rho(h) + 4(j-1)`. At most
    `q_F^(4(j-1)) + q_F · q_F^(n - rho(h) + 4(j-1)) <= 2 q_F^(n - rho(h) + 4j - 3)` vectors fail.
  - *Singular vectors.* By Lemma 1.4(1), `R` has at least `(1/2) q_F^(n - 2j + 1)` singular vectors.
  - *Comparison.* The exponents differ by `rho(h) - 6j + 4 >= 4`, because `rho(h) >= 6 r' >= 6j`. Since
    `(1/2) q_F^4 > 2`, some singular `e_j in R` does not fail.
- **Choosing `f_j`.** By Lemma 1.4(2), at least `q_F^(n - 2j)` singular `f in R` have
  `beta(e_j, f) = 1`. At most `q_F^(4j - 2)` lie in `B = S_(j-1) + F e_j + F h e_j`. Since
  `j <= n/16`, `n - 2j > 4j - 2`, so some such `f_j` lies outside `B`.

**The subspace.** `Y = span(e_j, f_j : j <= r')` is hyperbolic of dimension `2r'`. Also `Y + hY = S_(r')`
has dimension at least `3r'`, since each step adds the three vectors `e_j`, `h e_j`, `f_j`
independently.

**The element.**
- **Companion matrix.** Pick `a in F_q` with `a != -1 - (-1)^(r')`, and let `C in GL_(r')(F_q)` be the
  companion matrix of `p(t) = t^(r') + a t + (-1)^(r')`. Then `det C = (-1)^(r') p(0) = 1`, and `C` has
  no eigenvalue `1`, since `p(1) != 0`.
- **Definition of `y`.** `y` acts as `C` on `L_Y = span(e_j)` (in the basis `e_j`), as `C^(-dagger)` on
  `L_Y' = span(f_j)`, and as `1` on `Y^perp`. This is the Levi element `m(C)` of Lemma 2.1 for `Y`,
  extended by `1`.
- **Membership.** `m : SL_(r')(q) -> I(Y) x 1 <= I(V)` is a homomorphism, and `SL_(r')(q)` is perfect
  for `r' >= 3`. So `y in m(SL_(r')(q)) = [m(SL), m(SL)] <= I(V)'`.
- **Fixed space.** Neither `C` nor `C^(-dagger)` has eigenvalue `1`, so `ker(y - 1) = Y^perp` and
  `rk(y - 1) = 2r'`.

**Rank.** Apply Lemma 4.1 with `K = Y^perp`. Since `h` is an isometry, `h(Y^perp) = (hY)^perp`, so
`K ∩ hK = (Y + hY)^perp`. Hence
```text
rk([h, y] - 1) >= (n - 2r') - (n - dim(Y + hY)) >= r' ,
```
and `rk([h, y] - 1) <= 4r'` by Lemma 4.1.

## 5. Localization and displacement

**Lemma 5.1 (nearest scalars of isometries).** Let `g in I(V)` and `lambda in F` with
`rk(g - lambda) = rho < n/3`. Then `lambda^dagger lambda = 1`, meaning `lambda^2 = 1` in cases (Sp)
and (O), and `lambda^(q+1) = 1` in case (U). So `lambda^-1 g in I(V)`.

*Proof.*
- Write `g = lambda (1 + B)` with `rk B = rho`. With `†` the adjoint of `beta`, `g^† g = 1` gives
  `(lambda^† lambda - 1) · 1 = -lambda^† lambda (B^† + B + B^† B)`.
- The right side has rank at most `3 rho < n`. A nonzero scalar has rank `n`, so
  `lambda^† lambda = 1`.
- In case (O), `lambda = +-1` and `Q(-v) = Q(v)`.

**Lemma 5.2 (localization).** Let `b in I(V)^X` and `P = max_x rk(b_x - 1)`. There is a nondegenerate
`W <= V` with `dim W <= 2|X| P` such that every word `w(b)` lies in `I(W) x 1_(W^perp)`.

*Proof.*
- **Fixed space.** `U = ∩_x ker(b_x - 1)` has codimension at most `|X| P` and is fixed pointwise by
  every word. By (P0), `im(w(b) - 1) <= U^perp` for every word.
- **Nondegenerate hull.**
  - Let `rad = U^perp ∩ U`. It is totally isotropic for `beta`, since `beta(U, U^perp) = 0`.
  - Let `N_0` be a complement of `rad` in `U^perp`, so `beta|_(N_0)` is nondegenerate. In the
    nondegenerate space `N_0^perp ⊇ rad`, choose `rad'` dual to a basis of `rad`.
  - Then `W = N_0 (+) (rad + rad')`, an orthogonal sum. It is nondegenerate: the Gram matrix of
    `rad + rad'` is `[[0, I], [I, *]]`.
  - `W ⊇ U^perp`, and `dim W = dim U^perp + dim rad <= 2|X| P`.
- **Words.** A word maps `W` into `W + U^perp = W`. It fixes `W^perp <= (U^perp)^perp = U` pointwise.

**Lemma 5.3 (displacement by paired involutions).** Let `W <= V` be nondegenerate of dimension `d_0`,
and `d' >= 0` with `n >= 7 d_0 + 2 d' + 2`. Then there are:
- a nondegenerate `W''' ⊇ W` of dimension `d = 7 d_0 + 2 d'`;
- a subspace `W_1 <= W''' ∩ W^perp` with an isometry `sigma : W -> W_1`;
- an element `y in I(W''')' x 1 <= I(V)'`,

such that for every `h_0 in I(W) x 1`,
```text
[h_0, y] = h_0|_W (+) sigma h_0|_W^-1 sigma^-1 (+) 1     on  W (+) W_1 (+) (W (+) W_1)^perp .
```

*Proof.*
- **Hyperbolic spaces.**
  - Corollary 1.3 applied to `W^perp` (dimension `n - d_0`) gives at least `3 d_0 + d'` mutually
    orthogonal hyperbolic pairs. So `W^perp ⊇ H_1 (+) H_3 (+) H_4 (+) H_5`, an orthogonal sum of
    hyperbolic spaces of dimensions `2d_0, 2d_0, 2d_0, 2d'`.
  - Put `W''' = W (+) H_1 (+) H_3 (+) H_4 (+) H_5`.
- **Copies of `W`.**
  - `W (+) W^-`, with `W^-` carrying `-beta` (and `-Q`), contains the totally singular diagonal of
    dimension `d_0`.
  - A nondegenerate `2d_0`-space with a totally singular `d_0`-subspace `Delta` is hyperbolic. Pick
    `e in Delta` and a partner `f` (Lemma 1.2). Then `Delta ∩ f^perp` is a totally singular
    `(d_0 - 1)`-subspace of `span(e, f)^perp`, and we induct.
  - Hyperbolic spaces of equal dimension are isometric. So `H_i ≅ W (+) W^-` contains an isometric copy
    `W_i` of `W`, via `sigma_i : W -> W_i`, for `i = 1, 3, 4`. Put `sigma = sigma_1`.
- **Involutions.**
  - `s(w + w_1) = sigma^-1 w_1 + sigma w` on `W (+) W_1`, and `s = 1` on the rest of `W'''`. It is an
    isometric involution.
  - `s'` is the same with `(W_3, W_4, sigma' = sigma_4 sigma_3^-1)`.
  - The isometry `g` of `W (+) W_1 (+) W_3 (+) W_4` (identity elsewhere) sends `w -> sigma_3 w`,
    `w_1 -> sigma_4 sigma^-1 w_1`, `w_3 -> sigma_3^-1 w_3` and `w_4 -> sigma sigma_4^-1 w_4`.
    Direct evaluation on `W_3` and `W_4` gives `g s g^-1 = s'`.
- **`y` is a commutator product.** Put `y = s s'`. In the abelian group `I(W''')/I(W''')'`, `s` and
  `s'` have the same image, of order at most `2`. So `y in I(W''')'`.
- **The commutator.** `s'` commutes with `h_0` and with `s` (disjoint supports), so
  `[h_0, y] = h_0 s s' h_0^-1 s' s = h_0 (s h_0^-1 s)`. Then `s h_0^-1 s` is `1` on `W`,
  `sigma h_0^-1 sigma^-1` on `W_1`, and `1` elsewhere.

**Consequence.** If `rk(h_0 - 1) = t`, then `h = [h_0, y]` lies in `I(W''') x 1`, has
`rk(h - 1) = 2t`, and fixes a subspace of `W'''` of dimension at least `d - 2t`.
