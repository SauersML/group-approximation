---
rg: 2
id: stw99-lxvi-car-projection-comparison-hnn-proof
kind: route
title: Use spectral cutdowns and CAR comparison to make the unit properly infinite
target: stw99-lxvi-car-hnn-trace-balance-dichotomy
requires: []
---

Let `a,b in D` be positive contractions and suppose `b=uau*` for a unitary
`u in A`.  Assume, toward a contradiction to finiteness, that
`tau_D(a)!=tau_D(b)`.  The layer-cake formula

```text
tau_D(a)=integral_0^1 d_tau((a-t)_+) dt
```

and its analogue for `b` provide `t in [0,1)` at which the two dimension
functions differ.  Reverse `a,b` if necessary and put

```text
a_t=(a-t)_+,   b_t=(b-t)_+,
d_tau(a_t)<d_tau(b_t).                                      (4)
```

The two cutdowns are still unitarily conjugate in `A`.  They are both
nonzero: unitary conjugacy gives the same spectrum, and a nonzero cutdown in
one copy is nonzero in the other; faithfulness of `tau_D` then gives positive
dimension.

Choose a nonzero projection `e in D` with

```text
tau_D(e)<d_tau(b_t)-d_tau(a_t).
```

The CAR algebra has projections of arbitrarily small positive dyadic trace.
Strict comparison in `D` now gives

```text
a_t directSum e Cuntz-below_D b_t.
```

Writing `x=[a_t]`, `z=[e]`, and `v=[1_A]` in `Cu(A)`, ambient unitary
equivalence of the cutdowns yields

```text
x+z<=x.                                                     (5)
```

Both `a_t` and `e` are nonzero elements of the unital simple subalgebra `D`,
so they are full in `A`: the ideals they generate contain `D`, hence contain
`1_A`.  Compactness of the unit class gives integers `m,n` with

```text
v<=m x,                 v<=n z.                             (6)
```

Iterating `(5)` and using `(6)` gives `x+v<=x`.  Since `x<=v`, one gets
`2x<=x`; hence every finite multiple of `x` is at most `x`.  Finally

```text
2v<=2m x<=x<=v.
```

Thus `1_A` is properly infinite.  Contrapositively, unitary conjugacy inside
an ambient algebra with finite unit preserves the CAR trace for all positive
elements, not merely projections.

Now let `theta_0,theta_1:C->D` and `u` satisfy the HNN covariance.  If the
induced traces differ, choose a selfadjoint element detecting the difference
and affinely rescale it to a positive contraction `c`.  Then
`theta_0(c)` and `theta_1(c)` satisfy `(1)` and are conjugate by `u`, so the
preceding argument makes `1_A` properly infinite.  This proves the general
trace-balance assertion.

Here is an explicit projectionless pair.  Use the diagonal MASA

```text
C({0,1}^N) subset D
```

with its fair Bernoulli product measure, and let

```text
h(x)=sum_(n>=1) x_n 2^(-n).
```

The continuous map `h:{0,1}^N->[0,1]` is onto and pushes product measure to
Lebesgue measure.  Both `h` and `h^2` have spectrum `[0,1]`, so

```text
theta_0(f)=f(h),                 theta_1(f)=f(h^2)
```

are unital embeddings of `C([0,1])` into `D`.  Their induced traces differ:

```text
tau_D(h)=1/2,                    tau_D(h^2)=1/3.
```

Since `[0,1]` is connected, `C([0,1])` has only the projections `0,1`, so
the two traces agree on every projection.  Nevertheless any unitary
conjugating the two copies sends `h` to `h^2`, and the spectral-cutdown
argument makes the ambient unit properly infinite.

For completeness, the trace-balanced finite-dimensional side is unchanged.
For each finite-dimensional edge image `theta_i(C) subset D`, the
trace-orthogonal projection is a faithful `tau_D`-preserving conditional
expectation.  If the edge traces agree, the standard reduced HNN expectation
`E` onto `D` gives a faithful trace `tau_D after E`, so the reduced HNN
algebra is stably finite.  The full HNN algebra maps onto it and therefore
has a trace; if the full algebra is simple, that quotient is injective and
it is stably finite.  If the edge traces differ, the general argument above
makes both HNN units properly infinite.
