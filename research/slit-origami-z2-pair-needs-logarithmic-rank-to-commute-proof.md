---
rg: 2
id: slit-origami-z2-pair-needs-logarithmic-rank-to-commute-proof
kind: route
title: Ring holonomy, telescoping and extremal length force logarithmic energy; a dipole connection achieves it
target: slit-origami-z2-pair-needs-logarithmic-rank-to-commute
requires: []
---

Notation is as in the claim. `L >= 2`, `s = rho = floor(L/2)`, the squares are `(i,x,y)` with
`i` in `{0,1}` and `x,y` in `Z/L`, `n = 2L^2`, and `b delta_q = delta_(sigma q)`,
`c delta_q = delta_(tau q)`. All row and column arithmetic is mod `L`. `S` is the sheet swap
`(i,x,y) -> (1-i,x,y)`, which commutes with `sigma` and `tau`.

## 1. The defect has rank two

If `y != 0`, then `sigma tau (i,x,y) = (i,x+1,y+1) = tau sigma (i,x,y)`. If `y = 0`, both images lie
over the base square `(x+1,1)`:

- `sigma tau` changes the sheet iff `x` is in `[0,s)`;
- `tau sigma` changes the sheet iff `x+1` is in `[0,s)`.

These conditions differ exactly for `x = s-1` and `x = L-1`, which are distinct residues because
`1 <= s < L`. So `sigma tau != tau sigma` on exactly the four squares `(i,s-1,0)` and `(i,L-1,0)`.

The column of `bc - cb` at `(i,s-1,0)` is `delta_(1-i,s,1) - delta_(i,s,1)`. The column at `(i,L-1,0)`
is `delta_(i,0,1) - delta_(1-i,0,1)`.

- For each `x`, the two sheets give columns that are negatives of each other.
- The columns for `x = s-1` and `x = L-1` have disjoint supports, since `s != 0` mod `L`.

Hence `rank(bc - cb) = 2`. Also `bcb^(-1)c^(-1) - I = (bc - cb) b^(-1) c^(-1)`, so it has the same
rank.

The script checks the four-square support and the rank for `L = 2..40, 64, 101`.

**Rank one is impossible.** Let `U` be unitary with `det U = 1` and `rank(U - I) <= 1`. Write
`U = I + uv^*`. Then `det U = 1 + v^*u`, so `v^*u = 0`. Hence `(U-I)^2 = (v^*u) uv^* = 0`. A unitary
is normal, so `U - I` is normal and nilpotent, hence `0`. A commutator of unitaries has determinant `1`.

## 2. The rings and their holonomy

Fix `1 <= r <= rho`. `R_r` is the set of base squares on the boundary of the `2r x 2r` block with
columns `s-r, ..., s+r-1` and rows `1-r, ..., r`. Two facts about the reduction mod `L`:

- On the union of all these blocks, `x - s` ranges over `[-rho, rho-1]` and `y` over
  `[1-rho, rho]`. These ranges have `2 rho <= L` integers, so reduction mod `L` is injective there.
  Hence `|R_r| = 8r - 4`, and the `R_r` are pairwise disjoint: they are the level sets
  `max(|x - s + 1/2|, |y - 1/2|) = r - 1/2`.
- In operator order (letters applied right to left), the ring word is
  `w_r = c^(-(2r-1)) b^(-(2r-1)) c^(2r-1) b^(2r-1)`. It has length `8r - 4` and zero exponent sums
  in `b` and `c`.

Let `q_0 = (0, s-r, 1-r)`, and let `q_0, q_1, ..., q_(8r-4)` be the path traced by the letters of
`w_r`. It goes right along row `1-r`, up column `s+r-1`, left along row `r`, and down column `s-r`.
Its base squares run once around `R_r`.

**Holonomy.** A step changes the sheet only if it is a `tau^(+-1)` step between rows `0` and `1` in a
column `x` in `[0,s)`. The vertical runs cover the consecutive integer rows `1-r..r`. This range has
`2r <= L` integers and contains `0` and `1`, so each vertical run crosses between rows `0` and `1`
exactly once.

- The right column is `s+r-1`, which lies in `[s, L-1]` because `s + rho <= L`. It does not change
  the sheet.
- The left column is `s-r`, which lies in `[0, s-1]` because `r <= s`. It changes the sheet once.

Therefore

```text
w_r(b,c) delta_(q_0) = delta_(1, s-r, 1-r).                                  (H)
```

The script checks (H), the ring sizes and the disjointness for `L = 2..40, 64, 101`.

## 3. The Hilbert--Schmidt lower bound

Let `H = C^n (+) C^m`, `B = b (+) beta`, `C = c (+) gamma`. Let `b', c'` be commuting unitaries on
`H`, and put `D_b = b' - B`, `D_c = c' - C`, `E_b = ||D_b||_HS^2`, `E_c = ||D_c||_HS^2`. For a square
`q`, put `e_b(q) = ||D_b delta_q||` and `e_c(q) = ||D_c delta_q||`.

**The ring word is trivial at the commuting pair, but not at the origami.** Since `b'` and `c'`
commute and `w_r` has zero exponent sums, `w_r(b',c') = I`. By (H),

```text
||(w_r(b',c') - w_r(B,C)) delta_(q_0)|| = ||delta_(q_0) - delta_(1,s-r,1-r)|| = sqrt 2.   (T0)
```

**Telescoping.** Write `w_r = X_N ... X_1` with `N = 8r - 4`, and let `X'_j` be the same letter
evaluated at `(b',c')`. Then

```text
w_r(b',c') - w_r(B,C) = sum_j X'_N ... X'_(j+1) (X'_j - X_j) X_(j-1) ... X_1,
```

and `X_(j-1) ... X_1 delta_(q_0) = delta_(q_(j-1))`. The `X'` factors are unitary, so

```text
sqrt 2 <= sum_j ||(X'_j - X_j) delta_(q_(j-1))||.                             (T1)
```

Each term of (T1) is bounded as follows.

- If `X_j = B`, the term is `e_b(q_(j-1))`.
- If `X_j = B^(-1)`, then `b'^(-1) - B^(-1) = b'^(-1) (B - b') B^(-1)`. So the term is
  `||D_b B^(-1) delta_(q_(j-1))|| = e_b(q_j)`.
- The letters `C^(+-1)` behave the same way, with `e_c`.

So step `j` is charged `e_b` or `e_c` at one of its endpoints `q_(j-1)` or `q_j`.

**Each square is charged at most twice.** Every square of the lifted path lies over `R_r`. Each
lifted square is an endpoint of at most two steps, because the base path visits each square of
`R_r` once and the start and end lie on different sheets. Put

```text
F(x,y) = sum_(i in {0,1}) ( e_b(i,x,y) + e_c(i,x,y) ).
```

Then the right side of (T1) is at most `2 sum_(R_r) F`, so `sum_(R_r) F >= 1/sqrt 2`. By
Cauchy--Schwarz over the `8r - 4` squares of `R_r`,

```text
sum_(R_r) F^2 >= (1/2) / (8r - 4) >= 1/(16 r).                               (T2)
```

**Summing over the rings.** `F` is a sum of four terms, so `F^2 <= 4 sum_i (e_b^2 + e_c^2)`. Also
`sum_(q in C^n basis) e_b(q)^2 <= ||D_b||_HS^2 = E_b`, and likewise for `c`. The rings are disjoint,
and `sum_(r=1)^rho 1/r >= ln(rho+1)`. Summing (T2) over `r` gives

```text
ln(rho+1)/16 <= sum_(all base squares) F^2 <= 4 (E_b + E_c),
```

that is, `E_b + E_c >= ln(rho+1)/64`. This is item 2.

**Rank.** `||D_b||_op <= 2`, so `E_b <= ||D_b||_op^2 rank(D_b) <= 4 rank(D_b)`, and likewise for `c`.
Hence `rank(D_b) + rank(D_c) >= ln(rho+1)/256`. This is item 3.

## 4. Sharpness: a dipole flat connection

`S` commutes with `b` and `c`, so `C^n = V_+ (+) V_-` with `V_+- = ker(S -+ I)`, and both sectors
are invariant.

- On `V_+`, identify `f` with `f(0,.,.)`. Then `b` and `c` are the commuting torus shifts.
- On `V_-`, identify `f` with `g = f(0,.,.)`, so that `f(1,.,.) = -g`. Then
  `(bg)(x+1,y) = g(x,y)` and `(cg)(x,y+1) = eps(x,y) g(x,y)`. Here `eps(x,0) = -1` for `x` in
  `[0,s)`, and `eps = 1` elsewhere. For example, `(cf)(0,x,1) = f(1,x,0) = -g(x,0)` at the slit.

Let `Delta` be the graph Laplacian on the torus `(Z/L)^2`, and let `p = (s-1,0)`, `q = (L-1,0)`. The
right side of the Poisson equation below has total mass `0`, so a real solution `psi` exists:

```text
Delta psi = pi (delta_p - delta_q).
```

Put `A^x(x,y) = -(psi(x,y) - psi(x,y-1))` and `A^y(x,y) = psi(x,y) - psi(x-1,y)`. Define `b', c'` to
equal `b, c` on `V_+`. On `V_-`, define

```text
(b'g)(x+1,y) = e^(i A^x(x,y)) g(x,y),    (c'g)(x,y+1) = eps(x,y) e^(i A^y(x,y)) g(x,y).
```

These are unitary.

**Commutation.** Both `b'c'` and `c'b'` map `g(x,y)` to position `(x+1,y+1)`. They agree iff

```text
eps(x,y) eps(x+1,y) exp( i [A^x(x,y) + A^y(x+1,y) - A^y(x,y) - A^x(x,y+1)] ) = 1.
```

The bracket is

```text
[psi(x,y+1) - 2 psi(x,y) + psi(x,y-1)] + [psi(x+1,y) - 2 psi(x,y) + psi(x-1,y)] = (Delta psi)(x,y).
```

`eps(x,y) eps(x+1,y) = -1` exactly at `(x,y) = p` and `(x,y) = q`. There the bracket is `+pi` or
`-pi`. Elsewhere it is `0`. So the condition holds everywhere, and `b'c' = c'b'`. The script checks
this with residual `< 1e-9` for `L = 4..512`.

**Energy.** The distance is

```text
||b'-b||_HS^2 + ||c'-c||_HS^2 = sum |e^(iA)-1|^2 <= sum (A^x)^2 + (A^y)^2 = <psi, -Delta psi>,
```

because `A^x` and `A^y` run over the differences of `psi` across all `2L^2` edges once. Take the
Fourier transform `hat f(k) = sum_z f(z) e^(-2 pi i k.z/L)`, with `k` in `(-L/2, L/2]^2`. The
Laplacian symbol is `-lambda(k)`, where `lambda(k) = sum_j (2 - 2cos(2 pi k_j/L))`. For `|t| <= pi`,
`1 - cos t >= 2t^2/pi^2`, so `lambda(k) >= 16|k|^2/L^2`. Also
`|hat(pi(delta_p - delta_q))(k)|^2 <= 4 pi^2`. By Parseval,

```text
<psi, -Delta psi> = L^(-2) sum_(k != 0) |hat(Delta psi)(k)|^2 / lambda(k)
                  <= (pi^2/4) sum_(0 < ||k||_inf <= L/2) |k|^(-2)
                  <= (pi^2/4) sum_(j=1)^(floor(L/2)) 8j / j^2
                  <= 2 pi^2 (1 + ln(L/2)).
```

So `b', c'` commute on `C^n`, and `||b'-b||_HS^2 + ||c'-c||_HS^2 <= 2 pi^2 (1 + ln(L/2)) = O(log L)`.
This is item 4. The script computes the exact value, for example `20.84` at `L = 512`. The upper
and lower bounds are both `Theta(log L)`.

## 5. Consequences used in the claim

**No dimension-free `C(k)`.** Items 1 and 3 give a counterexample at `k = 2` for every `L`, and the
lower bound `ln(rho+1)/256` is unbounded. By Section 1, `k = 1` forces commuting exactly.

**Normalized HS rate.** With `||X||_2 = (tr X^*X / n)^(1/2)`, the matrix `bc - cb` has four nonzero
columns of squared norm `2`. So `eps = ||bc - cb||_2 = sqrt(8/n) = 2/L`. The normalized distance of
`(b,c)` to commuting pairs is at least `sqrt(ln(rho+1)/(64 n))`, which is `>= c eps sqrt(log(1/eps))`
for `L >= 2`, with an absolute constant `c > 0`.

**The log-loss form serves (LOC).** Suppose `C(k) log d` were available. Then (LOC) gives
`d <= (1+A_g)k + N_g C(k) log d`, and so `d = O_g(C(k) log C(k))`.
