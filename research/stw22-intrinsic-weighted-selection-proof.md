---
rg: 2
id: stw22-intrinsic-weighted-selection-proof
kind: route
title: Lift, correct, and clopen-glue weighted orthogonal copies in an abstract factor bundle
target: stw22-zero-dimensional-factor-bundles-have-uniform-traces
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-intrinsic-zero-dimensional-selection-audit-2026-08-30.md
---

Write `tau_x=ev_x o E`, and use a subscript `x` for the image of an
element of `M` in the finite factor `M_x`.  The proof has three parts.

## 1. Uniform stability of weighted orthogonal-copy relations

We first prove the following lemma, uniformly over all finite factors.

**Weighted correction lemma.**  Fix `m>=1` and `gamma>0`.  For every
`epsilon>0` there is `delta>0` with the following property.  Let `(N,tau)`
be a finite factor, let `0<=a<=1` satisfy

```text
m tau(supp(a)) <= 1-gamma,                              (ZFB2)
```

and let `b_1,...,b_m` lie in the operator-norm ball of radius two.  If

```text
||b_j^*b_j-a||_2 < delta,
||(b_i b_i^*)(b_j b_j^*)||_2 < delta       (i!=j),      (ZFB3)
```

then there are `v_1,...,v_m in N` such that

```text
v_j^*v_j=a,
(v_i v_i^*)(v_j v_j^*)=0                    (i!=j),
||v_j-b_j||_2<epsilon.                                  (ZFB4)
```

Here is a proof which also records why jumping support projections cause
no difficulty.  Choose `eta>0` so small that `4 eta^(1/2)<epsilon/3`, and
put

```text
p=supp(a),       q=1_[eta,1](a),       r=p-q.
```

On `qNq`, the element `a` is invertible with inverse bounded by
`eta^(-1)`.  Thus

```text
d_j=b_j a^(-1/2)q
```

has initial defect `||d_j^*d_j-q||_2` tending uniformly to zero with
`delta`, and its pairwise range-overlap defects tend uniformly to zero as
well.  The latter follows by inserting the bounded factors
`a^(-1/2)q` on both sides of the second inequalities in `(ZFB3)`.  More
explicitly, if `A_j=d_jd_j^*` and `B_j=b_jb_j^*`, then
`0<=A_j<=eta^(-1)B_j` and `||A_j||<=4eta^(-1)`.  Traciality and two
applications of these order bounds give

```text
||A_iA_j||_2^2 <= 16 eta^(-4) tau(B_iB_j)
                 <=16 eta^(-4)||B_iB_j||_2.             (ZFB3a)
```

Successively compress `d_j` by the complement of the ranges already
chosen and take its polar part.  If `z^*z` is `L^2`-close to a projection
`q`, the polar part of `z` misses a subprojection of `q` of trace tending
to zero and is `L^2`-close to `z`; this follows directly by splitting the
spectrum of `z^*z` at `1/2`.  Fill the missing initial subprojection into
the unused range complement.  At the `j`-th step that complement has trace
at least

```text
1-(j-1)tau(q) >= tau(q)+gamma,
```

so the fill is possible.  Induction gives partial isometries
`s_1,...,s_m` with common initial projection `q`, pairwise orthogonal
ranges, and

```text
max_j ||s_j-d_j||_2 -> 0       as delta -> 0.            (ZFB5)
```

For clarity, the induction uses no hidden comparison theorem.  If
`e=1-sum_(i<j)s_is_i^*`, then

```text
||(1-e)d_j||_2^2=sum_(i<j)||s_i^*d_j||_2^2 ->0;
```

each term tends to zero by `(ZFB3a)` and the already obtained
`||s_i-d_i||_2->0`.  Hence `(ed_j)^*(ed_j)->q` in `L^1`.  Spectral
splitting at `1/2`, polar decomposition, and a fill of the missing initial
projection inside `e` produce `s_j` and preserve the convergence in
`(ZFB5)`.

Condition `(ZFB2)` also leaves enough space in the complement of all the
high ranges to choose partial isometries `t_1,...,t_m` with common initial
projection `r` and mutually orthogonal ranges, all orthogonal to the high
ranges.  Set

```text
v_j=(s_j+t_j)a^(1/2).
```

Then the relations in `(ZFB4)` hold exactly.  On the low spectral part,

```text
||t_j a^(1/2)r||_2^2=tau(ar)<=eta,
||b_jr||_2^2
 <= tau(ar)+||r(b_j^*b_j-a)r||_1
 <= eta+delta.                                          (ZFB6)
```

On the high part, `(ZFB5)` and
`b_jq=d_ja^(1/2)q` give convergence in `L^2`.  Taking first `eta` and then
`delta` small proves the lemma; the remaining part outside `p` is bounded
by

```text
||b_j(1-p)||_2^2
 <=||b_j^*b_j-a||_1<=delta.
```

The same proof gives the following local form.  Let `0<=a<=1` be an
element of `M`, let `x in K`, and suppose

```text
m tau_y(supp(a_y)) <= 1-gamma                         (ZFB7)
```

on a neighbourhood of `x`.  If a tuple of sections
`b_1,...,b_m in M` satisfies the exact relations `(ZFB4)` in the fibre at
`x`, then, for every `epsilon>0`, there is a neighbourhood `U` of `x` such
that for every `y in U` the fibre `M_y` contains an exact tuple for `a_y`
within `epsilon` of `(b_1(y),...,b_m(y))` in `L^2`.  Indeed, the defect
functions in `(ZFB3)` are continuous and vanish at `x`, so the weighted
correction lemma applies throughout a smaller neighbourhood.

## 2. Intrinsic clopen selection

Suppose now that `(ZFB7)` holds on all of `K`.  For `x in K`, let
`F_x(a)` be the nonempty closed set of exact tuples `(v_1,...,v_m)` in
`M_x^m` satisfying `(ZFB4)`.  We construct sections
`v_1,...,v_m in M` whose value belongs to `F_x(a)` for every `x`.

Choose a summable sequence of positive numbers `(epsilon_n)` decreasing
to zero.  Inductively construct bounded section-tuples `f_n in M^m` such
that

```text
sup_x dist_(2)(f_n(x),F_x(a)) < epsilon_n,
||f_(n+1)-f_n||_(2,u) < 4 epsilon_n.                    (ZFB8)
```

Start with the zero tuple and an `epsilon_0` larger than the diameter of
the radius-two ball.  Given `f_n`, choose at each `x` an exact tuple
`w_x in F_x(a)` within `epsilon_n` of `f_n(x)`.  The quotient map
`M -> M_x` lifts the components of `w_x` to a section-tuple `g_x` in the
radius-two ball.  Continuity of the fibre `2`-norm makes `g_x-f_n` smaller
than `2 epsilon_n` on a neighbourhood of `x`.  The local form of the
weighted correction lemma, applied to `g_x`, lets us shrink that
neighbourhood so that every nearby fibre contains an exact tuple within
`epsilon_(n+1)` of `g_x`.

Compactness gives a finite such cover.  Since `K` is zero-dimensional, it
has a finite pairwise-disjoint clopen refinement subordinate to this
cover.  On each clopen member use its chosen `g_x`; the central clopen
projections patch these finitely many sections to a tuple `f_(n+1) in
M^m`.  The two estimates just obtained give `(ZFB8)` after harmlessly
rescaling the summable error sequence.

The tuples `f_n` stay in one operator-norm ball and are uniformly
`2`-Cauchy.  Tracial completeness gives a limit tuple
`v=(v_1,...,v_m) in M^m`.  Multiplication is uniformly `2`-continuous on
operator-norm bounded sets, while the first estimate in `(ZFB8)` tends to
zero.  Since every `F_x(a)` is closed, the limit satisfies

```text
v_j^*v_j=a,
(v_i v_i^*)(v_j v_j^*)=0                    (i!=j)       (ZFB9)
```

in every fibre, hence in `M` by faithfulness of the uniform `2`-norm.
This selection used only intrinsic fibre lifts and clopen central
projections; no common ambient factor is present.

## 3. Eliminate every norm/2-norm fibre-gap trace

Fix `x in K` and use the standard ideals

```text
J_x=closure(C_0(K\{x})M),
K_x={b in M:tau_x(b^*b)=0},
I_x=K_x/J_x.
```

Let `sigma` be a bounded positive trace on `I_x`, and let `0<=b<=1` lie in
`K_x`.  Fix `epsilon>0`, put `c=(b-epsilon)_+`, and fix `m`.  Since
`tau_x(b^2)=0` and `y |-> tau_y(b^2)` is continuous, Chebyshev's inequality
gives a clopen neighbourhood `V` of `x` such that

```text
sup_(y in V) tau_y(supp(c_y)) < 1/(2m).                 (ZFB10)
```

Put `d=1_Vc`.  Then `c-d in J_x`, so `[c]=[d]` in `I_x`.  Apply the
selection from Step 2 to `d`, with `gamma=1/2`, to obtain
`v_1,...,v_m in M` satisfying `(ZFB9)`.  Since `v_j^*v_j=d in K_x`, each
`v_j` lies in `K_x`.  Their range elements are orthogonal positive
contractions, and therefore

```text
m sigma([c])
 =sum_j sigma([v_j^*v_j])
 =sigma(sum_j [v_jv_j^*])
 <=||sigma||.                                           (ZFB11)
```

The integer `m` was arbitrary, so `sigma([c])=0`.  Letting
`epsilon->0` gives `sigma([b])=0`.  Thus every gap `I_x` is
bounded-trace-free.

The exact fibre-gap criterion
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` now shows that
every trace on `M` has the form `(ZFB1)`.  Conversely every functional in
`(ZFB1)` is a trace and satisfies

```text
|integral_K E(a)dmu| <= ||a||_(2,u)
```

by Cauchy--Schwarz.  This proves the claim.
