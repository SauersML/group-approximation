---
rg: 2
id: fpbs-percolation-spine-path-bridge-ratio-criterion-proof
kind: route
title: On a chordless path the bridge mass is the tilted gap count times the two-point function, TJT/T is the coverage decorrelation D_n, and a three-edge bypass closes a spine edge at deletion cost (1-p')/p' while FKG keeps the tilt
target: fpbs-percolation-spine-path-bridge-ratio-criterion
requires:
  - fpbs-annealed-pivotal-factorization-off-spine-bridges
---

Notation as in the target. `r in (0,1)`, `n >= 1`, the volume is the edge set
`Lambda = {e_1,...,e_n}` of a chordless path `x_0 x_1 ... x_n`, with
`e_k = x_{k-1} x_k`, `u = x_0`, `v = x_n`, `W = V(Lambda)`. The environment
`Z` is fixed in `r` and independent of the labels. Write
`N(i,j] = #{ k in (i,j] : e_k notin Z }` and `N = N(0,n]`.

## 1. The two kernels

Given `Z`, the edges of `Lambda ∩ Z` are open and each edge of `Lambda \ Z`
is open with probability `r`, independently. In `omega ∩ Lambda` the only
path from `x_i` to `x_j` (`i < j`) is the segment `e_{i+1} ... e_j`, so

```text
tau^Z(x_i,x_j) = r^{N(i,j]},   T(x_i,x_j) = E r^{N(i,j]} = t(i,j).
```

`W` spans no chord, so `J_W(a,b) = 1` exactly when `ab = e_k` for some `k`,
in either orientation. Hence

```text
(T J T)(u,v) = sum_{k=1}^n [ t(0,k-1) t(k,n) + t(0,k) t(k-1,n) ].
```

**Bridge mass.** Fix `f = e_k notin Z`. With `f` closed, `C'(u)` is the
open initial segment of `x_0,...,x_{k-1}` and `C'(v)` the open final segment
of `x_k,...,x_n`. The event `E^{x_{k-1} x_k}_f` of
`fpbs-annealed-pivotal-factorization-off-spine-bridges-proof` (§1) is
`{every edge of Lambda \ Z other than f is open}`, with probability
`r^{N-1}`. The opposite orientation `E^{x_k x_{k-1}}_f` is empty, because
`x_k` is not in `C'(u)`. On `E^{x_{k-1}x_k}_f` we have
`C'(u) = {x_0,...,x_{k-1}}`. A vertex `x_i` with `i <= k-1` lies in
`Y = V(Z ∩ Lambda)` iff `e_i in Z` or `e_{i+1} in Z`. Since `e_k notin Z`,
this happens for some `i <= k-1` iff some `e_j` with `j < k` lies in `Z`.
Symmetrically, `C'(v)` meets `Y` iff some `e_j` with `j > k` lies in `Z`.
Call `e_k` an **interior gap** of `Z` if `e_k notin Z` and there are `j < k < l`
with `e_j, e_l in Z`, and let `G` be the number of interior gaps. Then

```text
Br(u,v) = E[ G r^{N-1} ].
```

## 2. The identity (Theorem 1(a))

Put `P*` for the tilted law `dP*/dP = r^N / E r^N`, and set
`gamma_n = E*[G] / n` and `D_n = (TJT)(u,v) / (n t(0,n))`. Dividing,

```text
Br / TJT = E[G r^N] / ( r TJT ) = n gamma_n t(0,n) / ( r n D_n t(0,n) ) = gamma_n / (r D_n).
```

Neither `e_1` nor `e_n` can be an interior gap, so `G <= n-2` and
`gamma_n <= 1 - 2/n`. ∎(a)

## 3. The FKG facts (Theorem 1(b))

Assume from here that `Z` is a monotone function of an i.i.d. field: there
is a product measure `P` on `{0,1}^E` and `e in Z` is an increasing event
for every `e`. The infinite cluster of Bernoulli(`p'`) percolation is of
this form, because `{e open and e <-> infinity}` is increasing. Then
`N(i,j]` is decreasing, so `r^{N(i,j]}` is increasing. By Harris-FKG, for
`0 <= i <= k <= j <= n`:

```text
t(i,j) = E[ r^{N(i,k]} r^{N(k,j]} ] >= t(i,k) t(k,j).
```

Thus `t` is supermultiplicative along the path. For a straight path in a
transitive setting (`t(i,j) = t_{j-i}`) Fekete's lemma gives
`lambda = lim t_l^{1/l} = sup t_l^{1/l}`, so `t_l <= lambda^l`.

For the bound on `D_n`, write `t_1 = min_k t(k-1,k)`. We have
`t_1 >= r`, since `r^{N(k-1,k]} >= r`. For each `k`:

* `t(0,n) >= t(0,k-1) t(k-1,k) t(k,n)`, so `t(0,k-1) t(k,n) <= t(0,n) / t_1`;
* `t(k-1,n) <= t(k,n)` pointwise (`N(k-1,n] >= N(k,n]`), so
  `t(0,k) t(k-1,n) <= t(0,k) t(k,n) <= t(0,n)`.

Summing over `k` gives `D_n <= 1 + 1/t_1 <= 1 + 1/r`. ∎(b)

## 4. The bypass lower bound (Theorem 1(c))

Now `G = Z^2`, `P` is Bernoulli(`p'`) bond percolation with `p' > 1/2`,
`Z` is the set of open edges with an endpoint in the infinite cluster, and
the path is straight: `x_i = (i,0)`. Fix `2 <= k <= n-1`. Let
`b_1, b_2, b_3` be the other three sides of the unit square above `e_k`:
`x_{k-1} -> x_{k-1}+(0,1) -> x_k+(0,1) -> x_k`. None of them lies in
`Lambda`. Let

```text
A_k = { e_{k-1}, e_k, e_{k+1} in Z } ∩ { b_1, b_2, b_3 open }.
```

`A_k` is increasing and `A_k ⊆ {e_k open}`. Let `Phi` close `e_k`.

*Claim: on `A_k`, `Z(Phi omega) = Z(omega) \ {e_k}`.* An open path of
`omega` through `e_k` becomes an open path of `Phi omega` after `e_k` is
replaced by `b_1 b_2 b_3`. Closing an edge never creates a connection. So
every vertex has the same connectivity to infinity in `omega` and in
`Phi omega`. Membership of an edge `g ≠ e_k` in `Z` depends only on the
state of `g` and on the connectivity of its endpoints, so it is unchanged,
and `e_k notin Z(Phi omega)`.

Hence on `Phi(A_k)`, `e_k` is an interior gap (`e_{k-1}, e_{k+1}` stay in `Z`)
and `N(omega) = N(Phi^{-1} omega) + 1`. `Phi` is injective on `A_k`, and it
flips one coordinate of a product measure from open to closed. So for every
measurable `F >= 0`,
`E[F ; Phi(A_k)] = ((1-p')/p') E[F∘Phi ; A_k]`. Therefore

```text
E[ 1{e_k gap} r^N ] >= E[ r^N ; Phi(A_k) ] = ((1-p')/p') E[ r^{N+1} ; A_k ]
                    >= r ((1-p')/p') P(A_k) E[r^N],
```

where the last step is Harris-FKG for the increasing `1_{A_k}` and `r^N`.

Finally,
`A_k ⊇ {e_{k-1}, e_k, e_{k+1}, b_1, b_2, b_3 open} ∩ {x_k <-> infinity}`,
because each of `e_{k-1}, e_k, e_{k+1}` is then open with the endpoint `x_k`
in the infinite cluster. By FKG, `P(A_k) >= p'^6 theta(p')`. So

```text
P*(e_k is an interior gap) >= r (1-p') p'^5 theta(p')      (2 <= k <= n-1),
E*[G] >= (n-2) r (1-p') p'^5 theta(p').
```

With §2: `Br/TJT = E*[G] / (r n D_n) >= (1-2/n)(1-p') p'^5 theta(p') / D_n`. ∎(c)

The same argument works for any path and spine in which every interior edge
has an open detour of length `L` that avoids the path. It gives the constant
`(1-p') p'^{L+2} theta` and needs only the product structure and
monotonicity of `Z`.

## 5. Corollary 2

Fix `p' > 1/2` and `r in (0,1)`. By (a), `Br/TJT <= 1/(r D_n)`. By (c),
`Br/TJT >= (1/3)(1-p') p'^5 theta / D_n` for `n >= 3`. The constants
`r` and `(1-p') p'^5 theta` are positive and independent of `n`. So
`sup_n Br/TJT < infinity` iff `inf_n D_n > 0`.

For the `theta` dependence, (a) and (c) give

```text
c theta / D_n  <=  Br/TJT  <=  1/(r D_n),
```

so `Br/TJT >= K/theta` forces `D_n <= theta/(r K)`. ∎
