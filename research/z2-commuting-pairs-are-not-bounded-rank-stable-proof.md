---
rg: 2
id: z2-commuting-pairs-are-not-bounded-rank-stable-proof
kind: route
title: Telescoping a long commutator loop around one dislocation core bounds the rank distance to commuting pairs below by n/32
target: z2-commuting-pairs-are-not-bounded-rank-stable
requires: []
---

**Setting.** Let `n >= 8` with `4 | n`, `X = Z/n x Z/n` and `d = n^2`. Put `x_1 = n/4`, `x_2 = 3n/4`
and `L = M = n/4`. Define bijections of `X`:

```text
alpha(x, y) = (x + 1, y)
beta(x, y)  = (x, y + 1)          if y != n - 1
beta(x, n-1) = (x + 1, 0)         if x_1 <= x < x_2
beta(x_2, n-1) = (x_1, 0)
beta(x, n-1) = (x, 0)             otherwise.
```

`beta` is a bijection: on row `n-1` it is the vertical map followed by the cycle
`(x_1 x_1+1 ... x_2)` on row 0. Let `A, B` be the permutation matrices `A e_p = e_(alpha p)`,
`B e_p = e_(beta p)`, over any field `F`.

**Step 1: the commutator defect.** For `y != n-1` both `alpha beta` and `beta alpha` send `(x, y)` to
`(x+1, y+1)`. On row `n-1`:
- If `x` is not in `[x_1 - 1, x_2]`, both send `(x, n-1)` to `(x+1, 0)`.
- If `x_1 <= x <= x_2 - 2`, both give `(x+2, 0)`.
- At `x = x_1 - 1`, `alpha beta` gives `(x_1, 0)` and `beta alpha` gives `(x_1 + 1, 0)`.
- At `x = x_2 - 1`, `alpha beta` gives `(x_2 + 1, 0)` and `beta alpha` gives `(x_1, 0)`.
- At `x = x_2`, `alpha beta` gives `(x_1 + 1, 0)` and `beta alpha` gives `(x_2 + 1, 0)`.

So `AB - BA` is supported on 3 columns and `rank(AB - BA) <= 3`. The script computes the exact rank 2.

**Step 2: the loop moves many points.** Let `omega = beta^(-M) alpha^(-L) beta^M alpha^L`, the
permutation read from the word `a^L b^M a^(-L) b^(-M)` (letters applied left to right). Take
`p = (x, y)` with `0 <= x <= x_1 - 2` and `n - M <= y <= n - 1`.
- `alpha^L p = (x + L, y)` with `x + L` in `[x_1, x_1 + L - 2]`, which lies in `[x_1, x_2 - 1]`.
- `beta^M` moves up `M` rows. It crosses the transition `n-1 -> 0` exactly once, in column
  `x + L`, which is twisted by `+1`. The result is `(x + L + 1, y + M - n)`.
- `alpha^(-L)` gives `(x + 1, y + M - n)`.
- `beta^(-M)` moves down `M` rows and crosses the transition `0 -> n-1` once, in column
  `x + 1 <= x_1 - 1`. That column is not in `[x_1, x_2]`, the image of the twisted part, so there
  `beta^(-1)(x+1, 0) = (x+1, n-1)`. The result is `(x + 1, y) != p`.

So `omega` moves at least `(x_1 - 1) M = (L - 1) M` points. For a permutation matrix `P`,
`rank(P - I) = d - #cycles(P)` over every field: the kernel of `P - I` is spanned by the indicators of
the cycles. A moved point lies in a cycle of length at least 2, so `#cycles <= #fixed + #moved / 2`, and

```text
rank( omega(A, B) - I ) >= (L - 1) M / 2.
```

**Step 3: telescoping.** Let `A', B'` in `GL_d(F)` commute with `rank(A - A') <= C` and
`rank(B - B') <= C`. The word `a^L b^M a^(-L) b^(-M)` is trivial in `Z^2`, so `omega(A', B') = I`. Also
`rank(A^(-1) - A'^(-1)) = rank(A'^(-1) (A' - A) A^(-1)) <= C`, and likewise for `B`. For products of
`m = 2(L + M)` letters,

```text
X_1 ... X_m - X'_1 ... X'_m = sum_j X_1 ... X_(j-1) (X_j - X'_j) X'_(j+1) ... X'_m,
```

so `rank(omega(A,B) - I) <= 2 (L + M) C`. With Step 2,

```text
C >= (L - 1) M / (4 (L + M)) = (n/4 - 1)(n/4) / (2n) = (n - 4) / 32.
```

**Step 4: the upper bound.** Let `beta_0` be the vertical shift. Then `A` and `B_0` commute, and
`beta_0` differs from `beta` only at the `x_2 - x_1 + 1 = n/2 + 1` points of the twisted interval in
row `n-1`, so `rank(B - B_0) <= n/2 + 1`.

**Step 5: Z^N.** Put `A_3 = ... = A_N = I`. A commuting `N`-tuple near `(A, B, I, ..., I)` restricts
to a commuting pair near `(A, B)`, so the same bound holds.

**Scope.**
- The same count gives `phi(L) := rank(w_L(A,B) - I) <= 4 L C` for any pair within rank `C` of a
  commuting pair.
- `w_L` is a product of `L^2` conjugates of `[a,b]^(+-1)`. So `phi(L) <= L^2 rank([A,B] - I)` holds
  in general, and the dipole attains order `L^2` for `L <= n/4`.

QED.
