---
rg: 2
id: slit-origami-z2-pair-has-rank-distance-half-l-proof
kind: route
title: Monodromy area over word perimeter bounds the rank distance; cutting the slit attains it
target: slit-origami-z2-pair-has-rank-distance-half-l
requires: []
---

Notation is as in the claim. `L >= 2`, `s = floor(L/2)`, and `S = [0,s)` is the set of slit columns
in `Z/L`. `b delta_q = delta_(sigma q)` and `c delta_q = delta_(tau q)`. All coordinates are mod `L`.
`rank(bcb^(-1)c^(-1) - I) = 2` is item 1 of `slit-origami-z2-pair-needs-logarithmic-rank-to-commute`.
It is also rechecked by the script here, check C0, for `L = 2..40, 64`.

## 1. The rectangle word and its monodromy

For `1 <= a <= s` and `1 <= h <= L-1`, let `W_(a,h) = c^(-h) b^(-a) c^h b^a`. In operator order,
`b^a` is applied first. Its exponent sums are zero.

**`W` is a sheet swap on some base squares.** Project to the base torus, where `sigma` and `tau`
become commuting shifts. The path traced by `W_(a,h)` from `(i,x,y)` then returns to the base
square `(x,y)`. So `W_(a,h)(b,c)` is a permutation matrix that either fixes each square or swaps
its two sheets. Hence `rank(W_(a,h)(b,c) - I)` is the number of base squares whose lifted path ends
on the other sheet.

**When the path swaps sheets.** A letter changes the sheet only in two cases:

- a `tau` step from row `0` to row `1` in a column of `S`;
- its inverse, a `tau^(-1)` step from row `1` to row `0` in a column of `S`.

The path from `(x,y)` has four runs:

- `a` steps right along row `y`, with no sheet changes;
- `h` steps up column `x+a`, through the steps `t -> t+1` for `t = y, ..., y+h-1`;
- `a` steps left along row `y+h`, with no sheet changes;
- `h` steps down column `x`, through the same values of `t`.

Since `h <= L`, the `h` consecutive values `y, ..., y+h-1` contain a multiple of `L` at most once.
They contain one exactly when `y` lies in `{1-h, ..., 0}`, which is `h` residues. When they do, the
up run changes the sheet iff `x+a` is in `S`, and the down run changes the sheet iff `x` is in `S`.
So the path swaps sheets iff

```text
y in {1-h, ..., 0}   and   exactly one of x, x+a lies in S.
```

For an interval `S` of length `s` in `Z/L` and `1 <= a <= min(s, L-s) = s`, we have
`|S symmetric-difference (S - a)| = 2a`. Therefore

```text
rank(W_(a,h)(b,c) - I) = 2ah.                                             (M)
```

The script checks (M) directly for all `L <= 12` and all admissible `(a,h)`, check C3. It also
checks `a = h = s` for `L = 2..40, 64`, check C1.

## 2. The lower bound

Let `H = C^d (+) C^m`, `B = b (+) beta`, `C = c (+) gamma`. Let `b', c'` be commuting unitaries on `H`, and
put `r_b = rank(b' - B)`, `r_c = rank(c' - C)`. Since `b'` and `c'` commute and the exponent sums
are zero, `W_(a,h)(b',c') = I`. Also `W_(a,h)(B,C) = W_(a,h)(b,c) (+) W_(a,h)(beta,gamma)`, so by (M)

```text
rank(W_(a,h)(B,C) - W_(a,h)(b',c')) = rank(W_(a,h)(B,C) - I) >= 2ah.
```

**Telescoping.** Write the word as letters `X_N ... X_1`, with `N = 2a + 2h`, and let `X'_j` be the
same letter at `(b',c')`. Then

```text
W(B,C) - W(b',c') = sum_j X'_N ... X'_(j+1) (X_j - X'_j) X_(j-1) ... X_1.
```

Each term has rank at most `rank(X_j - X'_j)`, which is `r_b` or `r_c`. For the inverse letters,
`B^(-1) - b'^(-1) = b'^(-1) (b' - B) B^(-1)`. There are `2a` letters `B^(+-1)` and `2h` letters
`C^(+-1)`. Hence

```text
2ah <= 2a r_b + 2h r_c.
```

With `a = h = s` this gives `r_b + r_c >= s`.

The general `(a,h)` form gives trade-offs as well. For example, `h = L-1` gives
`s(L-1) <= s r_b + (L-1) r_c`.

## 3. The bound is attained

Let `c'(i,x,y) = (i,x,y+1)` be the unslit shift, and let `b' = b`. Both are shifts of the two
disjoint tori, so `b` and `c'` commute. `c - c'` is nonzero only on the columns `(i,x,0)` with `x`
in `S`, where

```text
(c - c') delta_(i,x,0) = delta_(1-i,x,1) - delta_(i,x,1).
```

For each `x`, the two sheets give opposite columns. Different `x` give disjoint supports. So
`rank(c - c') = s`, and the rank distance is exactly `s = floor(L/2)`. The script checks commutation
and the exact rank for `L = 2..40, 64`, check C2.

Finally, `d = 2L^2` gives `L = sqrt(d/2)`, so `s >= (L-1)/2 = sqrt(d/8) - 1/2`.

## 4. The consequence for (LOC)

Suppose `d <= alpha k + beta C(k) sqrt d`. Put `t = sqrt d`. Then `t^2 - beta C(k) t - alpha k <= 0`,
so `t <= beta C(k) + sqrt(alpha k)`, and `d <= 2 beta^2 C(k)^2 + 2 alpha k`. A rounding loss of
`C(k) sqrt d` would therefore still bound `d`. By Section 2, no loss `o(sqrt d)` is possible at `k = 2`.
