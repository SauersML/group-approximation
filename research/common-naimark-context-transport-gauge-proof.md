---
rg: 2
id: common-naimark-context-transport-gauge-proof
kind: route
title: Prove one-atom rigidity for circulant router transport and untwist the raw return
target: common-naimark-context-transport-is-an-inner-full-c-gauge
requires:
  - three-corner-naimark-router-cross-gram-proof
  - bounded-jacobson-q-corner-normal-form-proof
---

## 1. The common Naimark packet has explicit context transports

Let `K` be a finite abelian group, let `D=|K|`, and let
`lambda` be its regular translation representation on
`ell^2(K)`.  With `E_a` the coordinate projection, choose the
sign convention

```text
lambda(t)E_a lambda(t)^*=E_(a+t).                         (NCG9)
```

Let `A` be a unital star algebra represented on a Hilbert space and,
for every context `x`, let `(p_(x,s))_(s in K)` be a PVM.
In `M=A tensor M_D` put

```text
e_a=1 tensor E_a,
c_x=sum_s p_(x,s) tensor lambda(-s),
d_(x,a)=c_x e_a c_x^*.                                  (NCG10)
```

The orthogonality of each context PVM makes `c_x` unitary.  The
operators `d_(x,a)` are the dilated context PVM.  For contexts
`x,y` and `t in K`, define

```text
u=u_(y,t,x)=c_y(1 tensor lambda(t))c_x^*.                 (NCG11)
```

Direct cancellation, with no commutation assumption on the different
context PVMs, gives

```text
u d_(x,a)u^*
 =c_y(1 tensor lambda(t))e_a
    (1 tensor lambda(-t))c_y^*
 =d_(y,a+t).                                             (NCG12)
```

Thus the obvious action which moves one decoded context to another is
not outer.  Its implementer is already a bounded word in the routers
and the fixed qutrit translation.

## 2. Preserving one Fourier atom rigidifies the implementer

Let

```text
mathcal R=A tensor span{lambda(d):d in K}.                (NCG13)
```

This is an algebra, and `c_x`, `1 tensor lambda(t)`, and
`u_(y,t,x)` all lie in it.  Write uniquely

```text
u=sum_(d in K) k_d tensor lambda(d).                      (NCG14)
```

Suppose, more generally, that for some `b,r in K`,

```text
u e_b u^*=e_(b+r).                                       (NCG15)
```

Because `u` is unitary, it maps the range of `e_b` onto the range
of `e_(b+r)`.  Hence

```text
(1-e_(b+r))u e_b
 =sum_(d!=r) k_d tensor |b+d><b|=0.                      (NCG16)
```

The displayed matrix units have mutually orthogonal ranges, so
`k_d=0` for every `d!=r`.  Therefore

```text
u=v tensor lambda(r)                                     (NCG17)
```

for a unitary `v in A`.  In particular, preserving the named atom
itself forces `r=0` and `u=v tensor 1`.

Compare `(NCG12)` with the explicit expansion

```text
d_(x,a)=sum_s p_(x,s) tensor E_(a-s).                    (NCG18)
```

Equations `(NCG12)` and `(NCG17)` imply

```text
v p_(x,s)v^*=p_(y,s+t-r)                 for every s.     (NCG19)
```

For a fixed full-`C` target, `r=0`.  Thus a canonical transport
which preserves that target exists only when the two context PVMs are
already unitarily conjugate, with the prescribed outcome relabelling.
This is a representation-theoretic restriction, not an extraction of
the Lin cross-context loss.

The argument uses only one atom.  Requiring all full-`C` atoms to be
fixed is stronger and yields the same conclusion immediately.

## 3. Inner covariance untwists without changing a fixed target

Consider a raw covariance row on the occurrence algebra,

```text
S z=Ad(u)(z)S=u z u^*S,                  z in M,           (NCG20)
```

with `T=S^*` in a star representation.  Set

```text
S_0=u^*S,                       T_0=Tu.                    (NCG21)
```

Then

```text
S_0z=zS_0,                     T_0z=zT_0,
T_0S_0=TS,
1-S_0T_0=u^*(1-ST)u.                                   (NCG22)
```

Consequently, if `u` fixes the raw defect target `Q=1-ST`, the
change of variables preserves `Q` and turns the proposed action into
the commuting-coefficient case.  Every bounded defect-to-defect return
therefore has the normal form proved in the bounded Jacobson theorem.

There are two relevant ways that `u` fixes `Q`.

1. If the rank-`1/18` head is a separate tensor factor, every router
   implementer commutes with `Q=Q_h tensor 1`.
2. If `Q` is identified with the named same-packet atom `e_b`,
   equation `(NCG15)` with `r=0` forces `u=v tensor 1`.

If `r!=0`, the gauge change sends the defect to a different Fourier
atom.  That does not meet the fixed full-`C` target condition.  Thus
the target condition closes the apparent loophole: the implementer is
either removable while fixing the target, or it moves the target.

This untwisting statement concerns the covariance and return package.
Additional relations which distinguish `S` from `uS_0` could
invalidate it, but those relations would be genuinely new raw
holonomy; none is supplied by the common Naimark router itself.

## 4. Exact rank and singular-value accounting

Let the head Hilbert space have dimension `288` and let
`rank(Q_h)=16`.  Let the occurrence space have dimension `N`.
For any occurrence coefficient `B`,

```text
C=Q_h tensor B,
C^*C=Q_h tensor B^*B,
supp|C|=Q_h tensor supp|B|.                              (NCG23)
```

Therefore

```text
rank(Q_h tensor 1_N)=16N,
rank(supp|C|)=16 rank(supp|B|),
rank(Q_h tensor 1_N)/(288N)=1/18.                        (NCG24)
```

Every nonzero singular value of `B` occurs in `C` with multiplicity
sixteen.  If the Lin gap supplies a spectral projection `R` with

```text
B^*B R>=delta/2 R,                                       (NCG25)
```

then

```text
C^*C(Q_h tensor R)>=delta/2 (Q_h tensor R).              (NCG26)
```

For normalized product traces,

```text
tau(Q_h tensor R)=1/18 tau_occ(R).                       (NCG27)
```

In particular, the corrected three-corner estimate

```text
tau_occ(R)>=delta/(2-delta) tau_occ(e_r)                  (NCG28)
```

becomes exactly

```text
tau(Q_h tensor R)
 >=1/18 delta/(2-delta) tau_occ(e_r).                    (NCG29)
```

The singular floor `sqrt(delta/2)` survives unchanged.  Equations
`(NCG23)--(NCG29)` also show the limitation: there is no second
source/range rank equation.  The head just repeats the same cross-Gram
on sixteen identical rows.

## 5. Effect on the literal full-C coefficient

Write the losing coefficient as

```text
B_(y,b;x,a)=e_b c_y^*e_r c_xe_a.                         (NCG30)
```

Its left and right atoms give its full-`C` type before any raw
letter is added.  Inner transport cannot improve its modulus:

```text
|uBu^*|=u|B|u^*,
supp|uBu^*|=u(supp|B|)u^*,
tau((uBu^*)^*(uBu^*))=tau(B^*B).                         (NCG31)
```

If `u` fixes the named atoms, these conjugated supports remain in the
same full-`C` corners.  If it does not, the coefficient has been
relabelled to a different target.  Neither case turns the zero
compression `B=0` into an ordinary relator or forces the positive
finite-dimensional lower bound to vanish.

Thus no non-Morita invariant survives the canonical context-router
action.  A live continuation must exhibit a bounded raw relation whose
action is not generated by `c_y(1 tensor lambda(t))c_x^*`, yet which
still fixes the rank-`1/18` target and has an exact absorber for the
perfect Lin model.  No such relation, and no proof of a nonhyperlinear
group, is asserted here.
