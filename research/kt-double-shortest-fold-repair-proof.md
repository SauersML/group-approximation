---
rg: 2
id: kt-double-shortest-fold-repair-proof
kind: route
title: Collapse exact returns, count repair density, and extract the block swap
target: kt-double-shortest-fold-repair-is-a-bare-wall
requires:
  - infranormal-compact-closure-normal
---

Let `R(g)=rho_0(g)=rho_1(g)` for `g in Gamma`, let
`H=closure(R(Gamma))`, and write `T_epsilon=rho_epsilon(t)`.  Compact
normality makes each `T_epsilon` normalize `H`.  Moreover

```text
T_0 R(delta) T_0^*=R(t delta t^(-1))
                  =T_1 R(delta) T_1^*                  (KFP1)
```

for `delta in Gamma`.  Hence `V=T_1^*T_0` centralizes `H`.  Since
`T_1^*R(gamma)T_1` belongs to `H`,

```text
rho_0(h)=T_0^*R(gamma)T_0
          =V^*T_1^*R(gamma)T_1V
          =T_1^*R(gamma)T_1=rho_1(h).                  (KFP2)
```

This proves exact folding, including the random coset-sign models.

For the density statement let `alpha_n` be the exact-sector fraction,
`beta_(r,n)` the repair fractions, and

```text
z_(r,n)=tr(eta_(0,n)^r(h)eta_(1,n)^r(h)^*).
```

The exact contribution to `(KFR3)` is `alpha_n`, while `|z_(r,n)|<=1`.
Taking real parts gives

```text
o(1)=alpha_n+sum_r beta_(r,n) Re z_(r,n)
     >=alpha_n-sum_r beta_(r,n)
     =1-2 sum_r beta_(r,n).                             (KFP3)
```

Thus the repair density is at least `1/2-o(1)`.  More precisely, normalized
Hilbert--Schmidt orthogonality of the direct sum and `(KFR3)` give

```text
sum_r beta_(r,n)
  ||eta_(0,n)^r(h)-eta_(1,n)^r(h)||_2^2 -> 2.          (KFP4)
```

For fixed `R`, one summand is at least `2/R-o(1)` along a subsequence.  A
unitary distance is at most `4`, so its weight is at least
`1/(2R)-o(1)`; since its weight is at most one, its squared distance is at
least `2/R-o(1)`.  The squared defect of a direct sum is the weighted sum of
the squared block defects.  Global vertex and `Gamma`-agreement defects
tending to zero therefore force every fixed defect of this positive-density
block to tend to zero.

The block-swap calculation is exact:

```text
S diag(eta_0(g),eta_1(g)) S
   =diag(eta_1(g),eta_0(g)).                             (KFP5)
```

It commutes with the `Gamma` image in the ultraproduct and fails to commute
with the `h` image by `(KFR4)`.  This is the bare wall consumed by the
radical-collision route.

Finally choose a residual sequence of finite quotients of the residually
finite actor `G` and let `sigma_n` be their regular representations.  They
are exact and `tr(sigma_n(g))->delta_(g,1)`.  Normalized tensor norms show
that `(KFR6)` preserves all defects.  Its vertex trace is

```text
tr(eta_(epsilon,n)^r(g)) tr(sigma_n(g))->delta_(g,1),
```

and `(KFR7)` preserves the fold, completing the proof.
