---
rg: 2
id: fpbs-hairpin-paths-break-uniform-bridge-ratio-proof
kind: route
title: The exact path formulas on a hairpin in a column-seeded environment factor over columns, the shared middle seed makes each column a rho > 1 bonus that only the fold cut breaks, so TJT/T is summable while the tilted gap count is linear; far parts of an unfolded path are independent and Harris absorbs the near parts
target: fpbs-hairpin-paths-break-uniform-bridge-ratio
requires:
  - fpbs-percolation-spine-path-bridge-ratio-criterion
---

Notation as in the target. We use only Theorem 1(a) of
`fpbs-percolation-spine-path-bridge-ratio-criterion`: on a chordless path,
for every environment `Z` independent of the labels,

```text
T = t(0,n),   TJT = sum_{k=1}^n [ t(0,k-1) t(k,n) + t(0,k) t(k-1,n) ],
Br = E[G r^{N-1}] = (T/r) E*[G],
```

with `N = N(0,n]`, `G` the number of interior gaps, and `P*` the law with
density `r^N / E r^N`. Write `t(I) = E r^{N(I)}` for an edge set `I ⊆ Lambda`,
with `N(I)` the number of edges of `I` not in `Z`.

## 1. Theorem 1

`N(I) <= N(I')` when `I ⊆ I'`, and `r < 1`, so `t` is nonincreasing under
inclusion. In the `k = 1` summand, `t(0,0) t(1,n) = t(1,n) >= t(0,n)`. In
the `k = n` summand, `t(0,n-1) t(n,n) = t(0,n-1) >= t(0,n)`. All summands
are nonnegative, so `TJT >= 2T`, that is `n D_n >= 2`. Every interior gap is
one of `e_2, ..., e_{n-1}`, so `G <= n-2`, and
`Br = (T/r) E*[G] <= (n-2) T / r`. Dividing gives `Br/TJT <= (n-2)/(2r)`.

## 2. The column environment

*Factor, range, monotonicity, invariance.* The indicator of `h(j,y) in Z` is
`max(zeta_{j,y-1}, zeta_{j,y}, zeta_{j,y+1})`. This is an increasing
function of the seeds at the three vertices `(j,y-1), (j,y), (j,y+1)`. Each
of them is within distance `1` of the endpoint `(j,y)` of `h(j,y)`. Vertical
edges are in `Z` deterministically. A translation `tau` of `Z^2` maps
`h(j,y)` to `h(tau(j,y))` and the seed field to a field with the same law,
so the law of `Z` is translation invariant.

*Connectivity and density.* Every vertex lies on a vertical edge, so
`V(Z) = Z^2`, and each vertical line `{x = j}` lies in one component of
`Z`. The lines `{x = j-1}` and `{x = j}` are joined by `h(j,y)` whenever
`zeta_{j,y} = 1`. For fixed `j` this happens for infinitely many `y`, a.s.
(Borel-Cantelli, since the `zeta_{j,y}` are independent with mean `q > 0`).
A countable intersection of almost sure events leaves `(Z^2, Z)` connected
a.s. The spine density is `P(x in V(Z)) = 1`.

*Label independence.* `Z` is a function of `zeta`, taken independent of the
labels `U`. The constant family `Z_r = Z` is nondecreasing in `r`. So it is a
connected label-independent environment in the sense of
`fpbs-annealed-pivotal-factorization-off-spine-bridges`, and the path
formulas above apply to it.

## 3. The hairpin

The vertices of `H_m` are `P_k = (k,0)` for `0 <= k <= m`, then
`P_{m+1} = (m,1)`, then `P_{m+2+i} = (m-i,2)` for `0 <= i <= m`. They are
distinct, and `n = 2m+2`.

*Chordless.* Two path vertices that are adjacent in `Z^2` but not
consecutive on the path would have to be:

* on the same row: consecutive in `x`, so consecutive on the path;
* on rows `0` and `2`: never adjacent;
* `(m,1)` and a row vertex: its neighbours in rows `0` and `2` are `(m,0)`
  and `(m,2)`, both consecutive to it.

So there is no chord.

*Edges.* For `1 <= j <= m`: `e_j = h(j,0) = a_j`. Then `e_{m+1}` and
`e_{m+2}` are the vertical turn edges, and `e_{n+1-j} = h(j,2) = b_j`
(the edge `P_{m+1+i} P_{m+2+i}` with `i = m-j+1` joins `(j,2)` and
`(j-1,2)`). Put

```text
A_j = 1{a_j in Z} = max(zeta_{j,-1}, zeta_{j,0}, zeta_{j,1}),
B_j = 1{b_j in Z} = max(zeta_{j,1}, zeta_{j,2}, zeta_{j,3}).
```

The pair `(A_j, B_j)` depends only on the seeds of column `j`, so the pairs
are i.i.d. over `j`. With `u = 1-q`:

```text
P(A_j = 0) = P(B_j = 0) = u^3,    P(A_j = 0, B_j = 0) = u^5,
P(A_j = 0, B_j = 1) = P(A_j = 1, B_j = 0) = u^3 - u^5,
P(A_j = 1, B_j = 1) = 1 - 2u^3 + u^5.
```

The turn edges are in `Z` surely.

## 4. Proof of Theorem 2

**(a)** For an interval `I`, `N(I) = sum_j [ (1-A_j) 1{a_j in I} +
(1-B_j) 1{b_j in I} ]`, and the columns are independent. So `t(I)` is a
product over `j` of one of three factors:

* `1` if neither `a_j` nor `b_j` is in `I`;
* `E r^{1-A} = 1 - u^3 + r u^3 = lambda` if exactly one of them is (the same
  value for `B`);
* `mu = E r^{2-A-B}` if both are.

The formula for `mu` is

```text
mu = (1 - 2u^3 + u^5) + 2r (u^3 - u^5) + r^2 u^5.
```

Since `lambda^2 = 1 - 2(1-r) u^3 + (1-r)^2 u^6`, we get
`mu - lambda^2 = u^5 (1 - 2r + r^2) - (1-r)^2 u^6 = (1-r)^2 u^5 (1-u) > 0`.
So `t(I) = lambda^{a(I) - 2c(I)} mu^{c(I)} = lambda^{a(I)} rho^{c(I)}`.

**(b)** `T = t(0,n) = lambda^{2m} rho^m`. Removing `e_k` leaves the prefix
`e_1..e_{k-1}` and the suffix `e_{k+1}..e_n`, and we read off `a` and `c`
from (a).

* `k = j <= m` (edge `a_j`).
  * First summand: the prefix `a_1..a_{j-1}` has no full column, giving
    `lambda^{j-1}`. The suffix contains `a_{j+1}..a_m` and all the `b`s, with
    full columns `j+1..m`, giving `lambda^{2m-j} rho^{m-j}`. Divided by `T`:
    `lambda^{-1} rho^{-j}`.
  * Second summand `t(0,j) t(j-1,n)`: the prefix `a_1..a_j` gives
    `lambda^j`. The suffix `a_j..a_m` plus all the `b`s has full columns
    `j..m`, giving `lambda^{2m-j+1} rho^{m-j+1}`. Divided by `T`:
    `lambda rho^{1-j}`.
* `k = n+1-j` (edge `b_j`).
  * First summand: the prefix `e_1..e_{n-j}` holds all the `a`s and
    `b_m..b_{j+1}`, with full columns `j+1..m`, giving
    `lambda^{2m-j} rho^{m-j}`. The suffix `b_{j-1}..b_1` gives
    `lambda^{j-1}`. Divided by `T`: `lambda^{-1} rho^{-j}`.
  * Second summand `t(0,n+1-j) t(n-j,n)`: the prefix holds all the `a`s and
    `b_m..b_j`, with full columns `j..m`, giving
    `lambda^{2m-j+1} rho^{m-j+1}`. The suffix `b_j..b_1` gives `lambda^j`.
    Divided by `T`: `lambda rho^{1-j}`.
* `k = m+1`. Both summands split the arms into `a_1..a_m` and `b_1..b_m`,
  each of which has no full column. Each summand is `lambda^{2m}`, so each
  gives `rho^{-m}`. The case `k = m+2` is the same.

Adding up:

```text
n D_n = TJT/T = 2 sum_{j=1}^m ( lambda^{-1} rho^{-j} + lambda rho^{1-j} ) + 4 rho^{-m}
      <= 2 (lambda^{-1} + lambda rho) / (rho - 1) + 4 = A + 4,
```

using `sum_{j>=1} rho^{-j} = 1/(rho-1)` and `rho > 1`.

**(c)** `r^N = prod_j r^{(1-A_j) + (1-B_j)}` factors over columns. So under
`P*` the pairs are still i.i.d., with
`P*(A=a, B=b) = r^{2-a-b} P(A=a, B=b) / mu`. Hence

```text
P*(A = 0) = ( r^2 u^5 + r (u^3 - u^5) ) / mu = alpha,
```

and `P*(B = 0) = alpha` by the same computation, since `(A_j, B_j)` and
`(B_j, A_j)` have the same law.

The turn edges are in `Z`. So `a_j` is an interior gap iff `A_j = 0` and
some earlier edge is in `Z`. The earlier edges are `a_1..a_{j-1}`, so this
means some `A_i = 1` with `i < j`; the covered turn edge is a later edge.
Symmetrically, `b_j` is an interior gap iff `B_j = 0` and some `B_i = 1`
with `i < j`. Turn edges are never gaps. By independence,

```text
E*[G] = 2 sum_{j=1}^m alpha (1 - alpha^{j-1}) = 2 m alpha - 2 alpha (1 - alpha^m)/(1 - alpha).
```

**(d)** `Br/TJT = (T/r) E*[G] / (T n D_n) = E*[G] / (r n D_n)`. Use (b) in
the denominator and `E*[G] >= 2m alpha - 2 alpha/(1-alpha)` with
`2m = n-2`. Here `0 < alpha < 1` because `0 < r < 1` and `0 < u < 1`. The
limiting slope follows from `n D_n -> A` (the term `4 rho^{-m}` vanishes) and
`E*[G]/n -> alpha`.

**(e)** With `S^- = {a_1..a_m}` before `e_{m+1}` and `S^+ = {b_1..b_m}`
after it:

```text
P(S ⊆ Z) = P(A=1, B=1)^m = (1 - 2u^3 + u^5)^m,
P(S^- ⊆ Z) = P(S^+ ⊆ Z) = (1 - u^3)^m.
```

The ratio is `kappa^m`. Moreover `(1-u^3)^2 = 1 - 2u^3 + u^6`, so
`kappa - 1 = (u^5 - u^6)/(1-u^3)^2 > 0`. The split index `m+1` lies in
`[2, n-1]`, and `m = (n-2)/2`.

**(f)** On the horizontal path `(0,0)..(n,0)` the statuses of its edges are
`A_1, ..., A_n`. These are independent (distinct seed columns), each with
`E r^{1-A} = lambda`. So `t(i,j) = lambda^{j-i}`, every summand of `TJT/T`
is `lambda^{-1}` or `lambda`, and `D_n = lambda + 1/lambda >= 2`. Then
`Br/TJT = gamma_n / (r D_n) <= 1/(r(lambda + 1/lambda))`, with
`gamma_n <= 1`. For any `S`, the events `{S^- ⊆ Z}` and `{S^+ ⊆ Z}` depend
on disjoint columns, so every ratio in `K_n` is `1`. On a vertical path
every edge is in `Z`, so `G = 0` and `Br = 0`.

## 5. Proof of Theorem 3

Write `w = w_R`. For an edge set `F`, let `B(F)` be the set of vertices
within distance `R` of an endpoint of an edge of `F`. Every function of
`Z ∩ F` is a function of the seeds on `B(F)`. If `d(e,e') > 2R` for all
`e in F`, `e' in F'`, then `B(F) ∩ B(F') = ∅`, and functions of `Z ∩ F` and
of `Z ∩ F'` are independent.

Fix a split edge `e_k`. Put

```text
FL = { e_i : i <= k-w-1 },   NL = { e_i : k-w <= i <= k-1 },
NR = { e_i : k+1 <= i <= k+w },   FR = { e_i : i >= k+w+1 },
```

intersected with `Lambda`. `|NL|, |NR| <= w`. For `e_i in FL` and
`e_j in FR` we have `j - i >= 2w+2`, so `d(e_i,e_j) > 2R` by the definition
of `w`. So `FL` and `FR` are independent in the sense above.

*The decorrelation `D_n`.* `N(0,n] >= N(FL) + N(FR)`, so

```text
t(0,n) <= E[ r^{N(FL)} r^{N(FR)} ] = E r^{N(FL)} E r^{N(FR)}.
```

The functions `r^{N(F)} = prod_{e in F} r^{1{e notin Z}}` are nonnegative
and increasing in `Z`, hence increasing in the seeds. So Harris-FKG for the
i.i.d. seeds gives

```text
t(0,k-1) = E[ r^{N(FL)} r^{N(NL)} ] >= E r^{N(FL)} E r^{N(NL)}
         >= E r^{N(FL)} prod_{e in NL} E r^{1{e notin Z}} >= E r^{N(FL)} lambda_min^w,
```

and in the same way `t(k,n) >= E r^{N(FR)} lambda_min^w`. Hence
`t(0,k-1) t(k,n) / t(0,n) >= lambda_min^{2w}` for every `k`. Summing the
first summands of `TJT/T` over `k` gives `n D_n >= n lambda_min^{2w}`. Then
`Br/TJT = gamma_n/(r D_n) <= 1/(r lambda_min^{2w})`, using `gamma_n <= 1`.
Also `lambda_min >= r`, since `E r^{1{e notin Z}} >= r`.

*The constant `K_n`.* Let `S ⊆ Lambda \ {e_k}` with `P(S ⊆ Z) > 0`. Split
`S^- = S_FL ∪ S_NL` and `S^+ = S_NR ∪ S_FR` along the four blocks. Then:

* by monotonicity and independence,
  `P(S ⊆ Z) <= P(S_FL ∪ S_FR ⊆ Z) = P(S_FL ⊆ Z) P(S_FR ⊆ Z)`;
* by Harris-FKG (the events `{F ⊆ Z}` are increasing),
  `P(S^- ⊆ Z) >= P(S_FL ⊆ Z) P(S_NL ⊆ Z)`;
* likewise `P(S^+ ⊆ Z) >= P(S_FR ⊆ Z) P(S_NR ⊆ Z)`.

All these probabilities are positive, since they are at least
`P(S ⊆ Z) > 0`. So

```text
P(S ⊆ Z) / ( P(S^- ⊆ Z) P(S^+ ⊆ Z) ) <= 1 / ( P(S_NL ⊆ Z) P(S_NR ⊆ Z) )
                                    <= prod_{e in S_NL ∪ S_NR} P(e in Z)^{-1} <= pi_+^{-2w},
```

using Harris once more for the product, and `P(e in Z) >= pi_+` for
`e in S`.

*Geodesics.* If `x_0 .. x_n` is a geodesic of `Z^d` and `i < j`, the
closest endpoints of `e_i` and `e_j` are `x_i` and `x_{j-1}`, at distance
`j - 1 - i`. If `j - i >= 2R + 2`, this is `> 2R`. So `w_R <= R`. A geodesic
is an induced path, hence chordless.

*The hairpin.* For the column environment `R = 1`. `d(a_j, b_j) = 2`,
while `a_1 = e_1` and `b_1 = e_n` have index difference `n - 1 = 2m + 1`.
So `2m + 1 < 2 w_1 + 2`, that is `w_1 >= m`. Theorem 3 then gives
`K_n <= (1-u^3)^{-2 w_1}`, and Theorem 2(e) gives `K_n >= kappa^m`. Both are
exponential in `m`.

## 6. Proof of Corollary 4

* The column environment is a connected label-independent environment
  (Section 2). The hairpins are chordless (Section 3), and their edge sets
  are finite plain volumes. By Theorem 2(d),
  `sup_Lambda Br^Lambda_r / TJT = infinity` for every `r in (0,1)`, at
  every pair of path endpoints `u, v`. So no `C(r)` works over plain
  volumes.
* By Theorem 2(e) with `theta = 1`, `K_n theta >= kappa^{(n-2)/2}`, already
  for one run on each side. A proof of `K_n <= C/theta` that uses only the
  listed properties of `Z` would apply to the column environment, which is
  impossible.
* The column environment is an increasing function of i.i.d. seeds, so all
  Harris-FKG inequalities hold for it. `t` is supermultiplicative along
  `H_m` (Harris). Yet `D_n <= (A+4)/n` by Theorem 2(b). So no lower bound on
  `D_n` follows from supermultiplicativity and FKG alone.
* *Boxes.* In `[0,w] x [0,h]` with `h >= 1`, every vertical segment
  `{j} x [0,h]` lies in `Z`. The segments at `x = j-1` and `x = j` are joined
  inside the box by `h(j,y)` whenever `zeta_{j,y} = 1` for some
  `0 <= y <= h`, which fails with probability `u^{h+1}`. A union bound over
  the `w` gaps bounds the probability that `Z ∩ Lambda` is disconnected by
  `w u^{h+1}`. `Br = 0` on the complement, by Theorem 1 of
  `fpbs-annealed-pivotal-factorization-off-spine-bridges`.

The statements about the percolation spine (Conjecture 5 and the
computation) are not used here and are not claimed.
