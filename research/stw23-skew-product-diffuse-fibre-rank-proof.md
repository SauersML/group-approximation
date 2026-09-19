---
rg: 2
id: stw23-skew-product-diffuse-fibre-rank-proof
kind: route
title: Lift affine increments to positive orbit averages and encode them by spectral cuts
target: stw23-skew-product-diffuse-fibres-have-all-ranks
requires: []
artifacts:
  - research/artifacts/stw23-skew-product-rank-realization-audit-2026-08-30.md
---

Write `alpha=h tensor beta` and let `E:D->C(X) tensor B` be the canonical
expectation.  We use the convention
`alpha(f tensor c)=(f composed h^(-1)) tensor beta(c)`.

## 1. The trace simplex is the invariant-measure simplex

Exactness passes from `B` to `C(X) tensor B` and through the amenable integer
crossed product.  Hence every normalized quasitrace on `D` is a trace.

Every trace on `C(X) tensor B` is of the form

```text
eta_mu(f tensor c)=integral_X f(x)tau_B(c)dmu(x).                    (1)
```

Indeed, disintegrate over the central copy of `C(X)`.  Almost every fibre
functional is tracial on `B`, hence is `tau_B` after normalization.  The
trace in (1) is `alpha`-invariant exactly when `mu` is `h`-invariant.

Minimality on the infinite space `X` makes every nonzero power of `h`
fixed-point free.  If `k != 0`, choose a finite partition of unity
`sum_i q_i^2=1` with

```text
supp(q_i) intersect h^k(supp(q_i)) = emptyset.
```

For a trace `sigma` on `D`, `c in C(X) tensor B`, and the implementing
unitary `u`, traciality and centrality of the `q_i` give

```text
sigma(cu^k)
 = sum_i sigma(q_i^2 c u^k)
 = sum_i sigma(q_i c u^k q_i)
 = 0.                                                               (2)
```

Thus every trace on `D` is `eta_mu composed E`, and conversely every
invariant `mu` gives this trace.  Consequently

```text
QT(D)=T(D) is affinely homeomorphic to M_h(X).                       (3)
```

The action on the centre is minimal and free and `B` is simple, so the
standard crossed-product simplicity criterion makes `D` simple.  An
invariant probability measure exists, and the corresponding trace is
faithful by simplicity; hence `D` is stably finite.  The other structural
properties in the claim are immediate.

## 2. Strictly positive representatives of affine increments

Put `K=M_h(X)`.  The integration map

```text
C(X,R) -> Aff(K),       phi |-> (mu |-> integral phi dmu)            (4)
```

is onto.  Here is the point that makes the assertion exact rather than merely
dense.  Let

```text
N={phi in C(X,R): integral phi dmu=0 for every mu in K}.
```

The annihilator `N^perp` consists precisely of the invariant signed measures.
The Jordan positive and negative parts of an invariant signed measure are
again invariant.  It follows that the quotient norm on `C(X,R)/N` is

```text
||phi+N|| = sup_(mu in K) |integral phi dmu|.                       (4a)
```

Thus the range of (4) is closed.  Restrictions of weak-star continuous
affine functions on the full probability-measure simplex are uniformly dense
in `Aff(K)` by the standard affine approximation theorem.  Those restrictions
are exactly the functions in the range of (4), so closedness upgrades density
to surjectivity.

We need the following positivity refinement.  If `g in Aff(K)` is strictly
positive, choose `phi in C(X,R)` representing it under (4).  There is an
`N` for which

```text
s(x)=(1/N) sum_(j=0)^(N-1) phi(h^j(x)) > 0       for every x in X.   (5)
```

Otherwise, empirical measures based at points where the first `N`-term
average is nonpositive have a weak-star limit `mu in K` with
`integral phi dmu <= 0`, contradicting `g(mu)>0`.  Orbit averaging does not
change integrals against invariant measures, so `s` is a strictly positive
continuous representative of `g`.

Now fix `f in LAff(K,(0,infinity])`.  On a compact metrizable simplex an
extended positive lower semicontinuous affine function is the increasing
pointwise supremum of finite continuous affine functions.  Since `f` has a
strictly positive minimum, choose an increasing sequence

```text
q_n in Aff(K),       q_n >= c > 0,       sup_n q_n=f.
```

Set `g_n=(1-2^(-n))q_n`, `g_0=0`, and `delta_n=g_n-g_(n-1)`.  Then

```text
delta_1>0,
delta_n >= 2^(-n)c > 0  for n>=2,
sum_n delta_n=f.                                                   (6)
```

Apply (5) to obtain `s_n in C(X,(0,infinity))` satisfying

```text
integral_X s_n dmu = delta_n(mu)       for every mu in K.           (7)
```

## 3. Encode one positive continuous function by a fibre element

For continuous `s:X->(0,infinity)`, take an integer `m>=||s||` and put

```text
t_l(x)=min(1,max(0,s(x)-l+1)),             1<=l<=m,
c_s(x)=direct_sum_(l=1)^m (b-(1-t_l(x)))_+.
```

This defines a positive contraction in `C(X) tensor B tensor M_m`.
Condition (L) gives

```text
d_(tau_B)((b-(1-t))_+)=t,                  0<=t<=1,
```

and therefore

```text
d_(tau_B)(c_s(x))=sum_l t_l(x)=s(x).                              (8)
```

Let `c_n=c_(s_n)`, place the `c_n` in pairwise orthogonal finite-rank
corners of `K`, and define the norm-convergent block diagonal element

```text
a = direct_sum_(n=1)^infinity 2^(-n)c_n
      in C(X) tensor B tensor K.                                  (9)
```

The factors `2^(-n)` ensure membership in the compact-operator tensor
product and do not change support ranks.  For the trace corresponding to
`mu in K`, orthogonality, (7), (8), and monotone convergence give

```text
d_mu(a)
 = sum_n integral_X d_(tau_B)(c_n(x))dmu(x)
 = sum_n integral_X s_n dmu
 = sum_n delta_n(mu)
 = f(mu).                                                         (10)
```

Via (3), equation (10) is precisely the assertion in the claim.

**Trust boundary.**  Imported standard results are: quasitraces on exact
C*-algebras are traces; disintegration of a trace over a central
`C(X)`-algebra; the trace correspondence and simplicity criterion for a
free minimal integer crossed product; uniform affine approximation on a
compact convex set; and monotone continuous-affine approximation of lower semicontinuous affine
functions on a metrizable Choquet simplex.  The positivity upgrade (5) and
the exact rank construction (6)--(10) are proved above.
