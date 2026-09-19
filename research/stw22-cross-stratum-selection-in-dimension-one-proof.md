---
rg: 2
id: stw22-cross-stratum-selection-in-dimension-one-proof
kind: route
title: Use weighted spectral damping and Michael selection across all support strata in dimension one
target: stw22-one-dimensional-trivial-field-trace-continuity
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-one-dimensional-cross-stratum-selection-audit-2026-08-30.md
---

Put `t=tau(e)` and let

```text
P_s={a in R_+ : ||a||<=1, tau(supp(a))<=s},
E_e={w in eR : ||w||<=1}
```

with their `2`-norm metrics.  For `a in P_s` set

```text
F(a)={w in E_e:w^*w=a}.                                 (1D1)
```

Thus `F(a)` is exactly the set of square-root-weighted embeddings of the
support of `a` into `e`.

## The fibres are nonempty, complete, and lower semicontinuous

They are nonempty by finite-factor comparison, because
`tau(supp(a))<=s<t`.  The metric space `E_e` is complete: a `2`-norm
Cauchy sequence with common operator-norm bound one has an affiliated
`L^2` limit, and spectral truncation preserves the bound, so the limit is
again in `eR`.  The fibres are closed in `E_e`: on the operator-norm unit
ball,

```text
||w_n^*w_n-w^*w||_1
 <=(||w_n||_2+||w||_2)||w_n-w||_2,
```

so `2`-norm convergence preserves the exact equation `w^*w=a`.

We use the following weighted Bures lifting fact.

```text
a_n -> a in 2-norm and w in F(a)
imply that some w_n in F(a_n) satisfy w_n -> w in 2-norm.   (1D2)
```

Here is a finite-factor proof.  Write `w=v a^(1/2)`, and choose a spectral
cut `p=1_[eta,infinity)(a)` at a continuity point of the spectral
distribution.  The Powers--Stoermer inequality gives
`a_n^(1/2)->a^(1/2)` in `2`-norm.  Spectral-projection perturbation in a
finite von Neumann algebra gives subprojections

```text
p_n<=supp(a_n),       p'_n<=p,
```

commuting respectively with `a_n` and `a`, and partial isometries
`r_n:p'_n -> p_n`, such that

```text
||p-p'_n||_2+||r_n-p'_n||_2 -> 0                       (1D3)
```

after first discarding an arbitrarily small spectral band about `eta`.
Moreover the `L^1` masses of `a(1-p'_n)` and
`a_n(1-p_n)` are bounded by the mass below the cut, the discarded-band
mass, and a quantity tending to zero.  This is the usual cut proof of the
Bures/Powers--Stoermer lifting estimate: on the cut, polar decomposition
aligns the two spectral submodules; off the cut, the square roots have the
displayed small `2`-norm.

Map `p_n` to `v p'_n v^*` using `v p'_n r_n^*`.  The remaining initial
support has trace

```text
tau(supp(a_n)-p_n)<=s-tau(p_n),
```

whereas the remaining part of `e` has trace

```text
t-tau(p_n)>s-tau(p_n).
```

It therefore contains an orthogonal image of the remaining support.
Adding any implementing partial isometry on that remainder and then
multiplying by `a_n^(1/2)` gives `w_n in F(a_n)`.  Equations `(1D3)`,
Powers--Stoermer on the high part, and the low-mass estimate show first

```text
limsup_n ||w_n-w||_2^2
 <=4 tau(a 1_(0,eta)(a))
```

up to the arbitrarily small discarded-band error.  Letting `eta` decrease
to zero proves `(1D2)`.  Since `P_s` is metric, `(1D2)` says precisely that
the set-valued map `F:P_s->2^(E_e)` is lower semicontinuous.

## Uniform local path connectedness across support jumps

Fix `a in P_s` and `w_0,w_1 in F(a)`.  Write

```text
w_i=v_i a^(1/2),       v_i^*v_i=supp(a).
```

Finite-factor comparison extends `v_1v_0^*` to a unitary `u in eRe`, so
that `uv_0=v_1`.  Choose the principal selfadjoint logarithm `h` of `u`
and put

```text
u_lambda=exp(i lambda h),       w_lambda=u_lambda w_0.
```

This is a path in `F(a)` from `w_0` to `w_1`.  More importantly, scalar
functional calculus on the principal branch, whose arguments lie in
`[-pi,pi]`, gives

```text
(u_lambda-e)^*(u_lambda-e)<=(u-e)^*(u-e).                (1D4)
```

Conjugating this positive inequality by `v_0a^(1/2)` gives the exact
weighted contraction estimate

```text
||w_lambda-w_0||_2<=||w_1-w_0||_2.                     (1D5)
```

The path stays in the exact fibre, rather than merely near it:

```text
w_lambda^*w_lambda=w_0^*u_lambda^*u_lambda w_0=a,
ew_lambda=w_lambda.
```

Formula `(1D5)` is uniform in `a`: any two points less than `delta` apart
in the same fibre can be joined inside the `delta`-ball about the first.
Thus the family

```text
{F(a):a in P_s}
```

is equi-`LC^0`.  More explicitly, after taking `delta<epsilon/2`, any two
points of one fibre in a sufficiently small
ambient ball about an arbitrary point of `E_e` are joined inside the
concentric `epsilon`-ball.  This is precisely uniform equi-`LC^0` for the
family.  Every fibre is path connected by the same unitary path.

Michael's finite-dimensional selection theorem now applies: a lower
semicontinuous map from a paracompact space of covering dimension at most
one into a complete metric space, with nonempty closed path-connected
values forming an equi-`LC^0` family, has a continuous selection.  Applied
to `z |-> F(a(z))`, it proves `(1DS)`.  The theorem used here is the
`n=0` case of E. Michael, [*Continuous Selections II*](https://doi.org/10.2307/1969603),
Annals of Mathematics 64 (1956), Theorem 1.2; the finite-factor strong
Stiefel geometry is also consistent with Andruchow--Varela,
[*States with equivalent supports*](https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-002.pdf),
Theorems 2.10 and 3.3.

Farah--Vaccaro subsequently proved the corresponding trace theorem, in
fact for trivial bundles with an arbitrary `II_1` factor fibre, by a
continuous-comparison version of the same Michael-selection method; see
[*Continuous Selection of Unitaries in II_1 Factors*](https://arxiv.org/abs/2501.01272),
Proc. Amer. Math. Soc. 154 (2026), 1609--1622.

## Replication in the fibre gap

Let `c in K_x` be a positive contraction and fix `epsilon>0`.  Replace it
by `(c-epsilon)_+`.  For any integer `m`, `2`-norm continuity and
Chebyshev give a neighbourhood `V` of `x` on which

```text
tau(supp(c(t)))<1/(2m).                                 (1D6)
```

Choose a continuous scalar cutoff `f` equal to one near `x` and supported
in `V`.  Replacing `c` by `fc` changes its gap class by an element of
`J_x`.  On the compact set `supp(f)`, apply `(1DS)` separately to `fc`
and to `m` pairwise orthogonal factor projections of trace `1/m`.
The selected fields vanish in `2`-norm at the boundary of `supp(f)`, so
extension by zero gives `v_1,...,v_m in K_x` with

```text
v_j^*v_j=fc,
(v_i v_i^*)(v_j v_j^*)=0       (i!=j).
```

Every bounded positive trace `sigma` on `K_x/J_x` therefore satisfies

```text
m sigma(c)<=||sigma||.
```

Letting `m` tend to infinity, and then `epsilon` decrease to zero, shows
that every such trace vanishes.  The abstract fibre-gap criterion gives
the asserted description and uniform-`2`-norm continuity of all traces.
