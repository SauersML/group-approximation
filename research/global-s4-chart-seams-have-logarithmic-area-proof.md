---
rg: 2
id: global-s4-chart-seams-have-logarithmic-area-proof
kind: route
title: Seam loops are centralizer commutators, and Johnson-graph diameter four bounds all chart names
target: global-s4-chart-seams-have-logarithmic-area
requires: [finite-mark-centralizer-commutator-area-is-proper]
---

Suppose every seam loop has area at most `C`.

**One seam gives a bounded name change.** Let `S,S'` be adjacent with shared
edge `{p,q}`, equal to `(p_a p_b)` in `S` and `(p'_(a') p'_(b'))` in `S'`. Put
`h=g_(S')^(-1) g_S`, so `h tau_ab h^(-1)=tau_(a'b')`. Choose `rho`, from a
finite list of depth-three permutation words, with
`rho tau_ab rho^(-1)=tau_(a'b')` in `V`, and let `A_0` bound the areas of these
finitely many identities. Then `z=rho^(-1) h` centralizes `b=(c_a c_b)`, and the
seam loop is a conjugate of

```text
rho [z, tau_ab]' rho^(-1) * (rho tau_ab rho^(-1) tau_(a'b')^(-1)),
```

where `[z,tau_ab]'` is the commutator word written with the word
`rho^(-1) gamma_(S')^(-1) gamma_S` for `z`. By subadditivity of area,
`Area([z,tau_ab]') <= C + A_0`. Theorem `(FMC1)`, with the fixed word `tau_ab`,
gives a word `u` with `|u| <= D=(C+A_0+B)/A` and `Ku=Kz`, `K=<b>`. So
`|h|_V <= H`, where `H=max|rho| + max|tau_ab| + D` does not depend on `n`.

**Counting.** The Johnson graph `J(N,4)` has diameter `4` for `N>=8`. Fix `S_0`.
Every `k_S=g_(S_0)^(-1) g_S` is then a product of at most four name changes, so
`|k_S|_V<=4H`. Since `g_S` maps `c_a` onto `p_a`, `S` is determined by `g_S`,
and the `k_S` are distinct. Hence

```text
binom(N,4) <= #Ball_V(4H) <= (2|X|+1)^(4H).
```

With `N=2^n`, `log binom(N,4) >= 4(n-1) log 2 - log 24`. So
`H >= (4(n-1) log 2 - log 24)/(4 log(2|X|+1))`, and solving for `C` gives
`(GSC)` with `c = A log 2 / log(2|X|+1)`.

The argument uses every adjacent pair along one path of length four. It
therefore says nothing about averaged seam bounds or contextual charts.
