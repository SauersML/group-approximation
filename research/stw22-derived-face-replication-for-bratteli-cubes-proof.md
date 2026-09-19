---
rg: 2
id: stw22-derived-face-replication-for-bratteli-cubes-proof
kind: route
title: Lift across derived subsets and replicate damped cuts in the exposed stratum
target: stw22-finite-bratteli-cubes-have-only-uniform-traces
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-finite-bratteli-cube-audit-2026-08-30.md
---

Let `E_(i,n):R_i -> F_(i,n)` be the trace-preserving conditional
expectation and put `E_(i,infinity)=id`.  For `x in X`, let
`E_x:R -> N_x` be their tensor product.

## The completion and its fibres

The central copy of `C(K)` makes `A_K` a continuous field whose fibre at
`x in K` is

```text
D_x=tensor_i D_(i,x_i),
D_(i,n)=F_(i,n),       D_(i,infinity)=U_i.
```

Every `D_x` has a unique trace.  Disintegrating a trace over the central
copy of `C(K)` therefore gives

```text
T(A_K)=Prob(K).                                         (BFC0)
```

Indeed, the disintegrated fibre functional is tracial almost everywhere
and hence is the unique trace of `D_x`; conversely integration of the
fibre traces gives a trace for every probability measure on `K`.  Thus the
uniform tracial norm is the supremum of the fibre `2`-norms.

Every uniform `2`-norm limit of bounded elements of `A_K` plainly belongs
to the displayed section algebra `M_K`.  Conversely, take `a in M_K`.
Its image in the Hilbert space `L^2(R)` is compact.  Choose a finite
partition of unity `(f_j)` on `K` and points `x_j` so that

```text
||a(x)-a(x_j)||_2 < epsilon       on supp(f_j).
```

By Kaplansky density choose bounded `u_j in tensor_i U_i` which are
`2`-close to `a(x_j)`.  Since `a(x) in N_x` and `E_x` is the orthogonal
projection in `L^2(R)`,

```text
s(x)=sum_j f_j(x) E_x(u_j)
```

is uniformly `2`-close to `a`.  For an elementary `u_j`, the section
`x |-> E_x(u_j)` on `X` is an elementary tensor of members of the `A_i`;
the general case follows by norm approximation.  Extend each `f_j` from
`K` to `X` and then restrict the resulting element of `A` back to `K`.
This shows `s in A_K` and proves the formula for `M_K`.

## Exact lifting from one derived subset

For `0<=k<=d`, put

```text
Z_k={x in X: at least k coordinates of x equal infinity}.
```

Then `X^(k)=Z_k` and `X^(d+1)=emptyset`: a point with exactly `k`
infinite coordinates is isolated in `Z_k`, whereas a point with at least
`k+1` is approached by making one infinite coordinate finite and tend to
infinity.

Put `K_0=K` and `K_(k+1)=(K_k)^(1)`.  Because `K` is closed in `X`,
induction at these finite stages gives

```text
K_k subset K intersect X^(k)=K intersect Z_k.           (BFC1)
```

In particular `K_(d+1)=emptyset`.  Let `M_k` be the bounded constrained
`2`-continuous section algebra over `K_k`.  Whenever `K_(k+1)` is
nonempty, restriction

```text
res_k:M_k -> M_(k+1)                                    (BFC2)
```

is surjective.  Fix a compatible metric on `X`.  For every isolated point
`t in K_k\K_(k+1)`, choose `r(t) in K_(k+1)` such that

```text
dist(t,r(t)) <= 2 dist(t,K_(k+1)).                       (BFC3)
```

For `b in M_(k+1)`, define

```text
(Lb)(t)=E_t(b(r(t)))       (t in K_k\K_(k+1)),
(Lb)(t)=b(t)               (t in K_(k+1)).               (BFC4)
```

There is no fibre-containment assertion in `(BFC4)`: `E_t` is defined on
the common ambient factor `R` and has range exactly `N_t`.  If a net in
the exposed stratum converges to `y in K_(k+1)`, then `(BFC3)` gives
`r(t)->y`.  Moreover, for every fixed `z in N_y`,

```text
||E_t(z)-z||_2 -> 0             as t -> y.              (BFC5)
```

To see this coordinatewise, a coordinate finite at `y` is eventually
equal to it.  A coordinate infinite at `y` is either infinite or tends to
infinity through its increasing matrix chain, whose trace-preserving
expectations converge strongly, and hence in `2`-norm, to the identity.
There are only finitely many coordinates.  Consequently

```text
||E_t(b(r(t)))-b(y)||_2
 <= ||b(r(t))-b(y)||_2+||E_t(b(y))-b(y)||_2 -> 0.
```

Thus `Lb in M_k`, it has the same operator-norm bound as `b`, and `(BFC2)`
follows.

## The kernel has no bounded trace

Fix `x in K_(k+1)` and write `I_x(K_k)=K_x(K_k)/J_x(K_k)`.  As for every
bounded section algebra over a zero-dimensional compact base,

```text
J_x(K_k)={a in K_x(K_k): ||a(t)|| -> 0 as t -> x}.       (BFC6)
```

Restriction and `(BFC2)` give a surjection

```text
q_k:I_x(K_k) -> I_x(K_(k+1)).                           (BFC7)
```

We prove that `H_k=ker(q_k)` has no nonzero bounded positive trace.  Let
`a` be a positive contraction in `H_k` and lift it positively to
`K_x(K_k)`.  Its restriction to `K_(k+1)` tends to zero in operator norm
at `x` by `(BFC6)`.  Choose a decreasing clopen local base `(V_n)` at `x`.
After a central localization, on each annulus `V_n\V_(n+1)` cut `a` down
by

```text
delta_n=sup{||a(y)||:y in K_(k+1) intersect
                         (V_n\V_(n+1))}.
```

The numbers `delta_n` tend to zero.  Therefore this changes `a` only by an
element of `J_x(K_k)` and yields a positive representative `b` satisfying

```text
b|_(K_(k+1))=0.                                         (BFC8)
```

Fix `epsilon>0`, put `c=(b-epsilon)_+`, and fix `m`.  Since `b(x)=0` in
`2`-norm, Chebyshev's inequality permits another central localization for
which

```text
m tau_t(1_(epsilon,infinity)(b(t))) <= 1                (BFC9)
```

throughout the remaining neighbourhood.  Every point of
`K_k\K_(k+1)` is isolated in `K_k`.  Its fibre `N_t` is a finite factor:
it is a full matrix algebra if all coordinates of `t` are finite, and a
hyperfinite `II_1` factor otherwise.  In either case `(BFC9)` lets us
choose independently unitaries `u_1(t),...,u_m(t)` moving the support of
`c(t)` onto pairwise orthogonal projections.  Define

```text
v_j(t)=u_j(t)c(t)^(1/2)       (t in K_k\K_(k+1)),
v_j(t)=0                      (t in K_(k+1)).            (BFC10)
```

No continuity of the unitaries is needed.  At a point `y` of the next
derived subset, `(BFC8)` and `2`-continuity give

```text
||v_j(t)||_2^2=tau_t(c(t)) <= tau_t(b(t))
                            <= ||b(t)||_2 -> 0.
```

Thus every `v_j` belongs to `M_k`.  In `H_k`, one has `v_j^*v_j=c`, while
the `v_jv_j^*` are pairwise orthogonal.  If `sigma` is a bounded positive
trace on `H_k`, then

```text
m sigma(c)=sigma(sum_j v_jv_j^*) <= ||sigma||.
```

Arbitrariness of `m`, followed by `epsilon->0`, gives `sigma(a)=0`.
Therefore `H_k` is bounded-trace-free.  Bounded traces on the two gaps in
`(BFC7)` consequently correspond bijectively.

## Finite descent and a nonzero gap

Every point of `K` has finite Cantor--Bendixson rank by `(BFC1)`.  Iterating
`(BFC7)` until the point becomes isolated identifies the bounded trace cone
of its original gap with that of the zero terminal gap.  Hence every gap
`K_x/J_x` is bounded-trace-free.  The abstract fibre-gap criterion now
shows that every trace on `M_K` is an integral of the canonical fibre
traces.

For nontriviality in the full field `K=X`, let `k_(i,n)` be the matrix size
of `F_(i,n)`.  Density in an infinite-dimensional UHF algebra gives
`k_(i,n)->infinity`.  Put a rank-one projection in the fibre at
`(n,...,n)` and zero at every other point.  This is a bounded
`2`-continuous section vanishing at the top fibre, because its `2`-norm is

```text
(product_i k_(i,n))^(-1/2) -> 0.
```

Its norm is one on a sequence converging to the top point, so its class in
the top gap is nonzero.
