---
rg: 2
id: finite-stencil-folner-atlas-proof
kind: route
title: Realize triangular scale weights by coherent Schur multiplicity matches
target: folner-multiplicity-atlases-have-vanishing-first-exit
requires:
  - fixed-shift-invariance-does-not-force-flat-profile
---

All weights in `(FSM1)` are rational.  Choose a common denominator `D_N`
and integers

```text
n_x=D_N nu_N(x),        sum_x n_x=D_N.                 (FSA1)
```

Choose a finite cyclic group with at least `|T_N|` distinct characters and
label distinct characters `(sigma_x)_(x in T_N)`.  For each `g in F`, take
the exact representation packet whose
type-`x` multiplicity is

```text
n_(x-g).                                                   (FSA2)
```

Thus the packet is literally
`direct_sum_x sigma_x tensor C^(n_(x-g))`, not merely a formal semisimple
object.  Put

```text
r_x=min_(g in F) n_(x-g),
alpha_N=(1/D_N) sum_x r_x.                              (FSA3)
```

Inside the type-`x` multiplicity space of every chamber choose the first
`r_x` coordinate vectors.  Their sum is a projection `R_g` of normalized
trace `alpha_N`, independent of `g`.  Identify those chosen coordinates
between any two chambers, type by type.  The resulting `V_(h,g)` are exact
partial intertwiners, have source `R_g` and range `R_h`, and, because all
identifications use the same labelled coordinates,

```text
V_(k,h)V_(h,g)=V_(k,g).                                 (FSA4)
```

Thus every closed supported gallery has exactly trivial holonomy.  Its only
loss is the literal complement of the common multiplicity reservoir.

For nonnegative numbers `(a_g)`,

```text
a_0-min_g a_g <= sum_g (a_0-a_g)_+.                    (FSA5)
```

Apply this pointwise with `a_g=nu_N(x-g)` and sum over `x`.  Since two
probability measures have equal positive and negative variation,

```text
1-alpha_N
 <= sum_(g in F) sum_x (nu_N(x)-nu_N(x-g))_+
 =  sum_(g in F) TV(nu_N,shift_g(nu_N)).                (FSA6)
```

The one-dimensional computation in
`fixed-shift-invariance-does-not-force-flat-profile` gives

```text
TV(mu_N,shift_r(mu_N))<=2|r|/(N+1).                    (FSA7)
```

Tensorization and a coordinatewise path give, for `g=(a,b)`,

```text
TV(nu_N,shift_g(nu_N))
 <=2(|a|+|b|)/(N+1).                                   (FSA8)
```

Equations `(FSA6)--(FSA8)` prove `(FSM2)`.

Finally tensor every multiplicity space with `C^4`, let

```text
P=diag(1,1,0,0),       Q=diag(1,0,1,0),                (FSA9)
```

and tensor all `R_g,V_(h,g)` with the identity.  On every carrier,
`tr(P)=tr(Q)=1/2` and `tr(PQ)=1/4`, while `(FSA6)` is unchanged.  For any
fixed depth window enlarge `F` by the finitely many partial gallery words
seen in that window; `(FSA8)` still makes the common loss tend to zero.
Hence fixed-depth iteration leaves asymptotically all marked mass alive,
contradicting `(FSM3)` if its fixed `kappa` were inferred only from the
listed transport data.
