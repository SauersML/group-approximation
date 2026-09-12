---
rg: 2
id: two-matching-matrix-bridge-orbit-proof
kind: route
title: Alternate Fourier block transport and run a primitive affine orbit
target: two-matchings-force-exponential-dimension-with-multiplicity
requires:
  - two-untwisted-field-matchings-force-complete-cross-commutation
---

Let `(P_x)` and `(Q_y)` be the spectral PVMs of `U,W`.  Put

```text
T_0=I,             T_1=A,
<T_i b,b>=<c_i,b>, d_i=T_i^(-*)c_i.                             (1)
```

Fourier coefficient uniqueness applied to `(PM1)` gives

```text
P_x Q_y P_x'
 =P_x Q_(y+c_i+T_i^*(x+x')) P_x',                              (2)

Q_y P_x Q_y'
 =Q_y P_(x+d_i+T_i^(-*)(y+y')) Q_y'.                           (3)
```

We use the following elementary bridge fact.  If `P,Q,Q',R` are projections,
`QQ'=0`, and

```text
P Q R=P Q' R!=0,                                               (4)
```

then `Q P Q'!=0`.  Indeed, if `Q P Q'=0` and a vector `v` makes the common
value in `(4)` nonzero, the inner product of its two equal values is both its
positive squared norm and

```text
<Q Rv, P Q' Rv>=<Rv,Q P Q' Rv>=0,
```

a contradiction.  The same statement holds with the P and Q roles swapped.

Choose `x,y` with `P_xQ_y!=0`.  The diagonal case of `(3)` says

```text
Q_y P_x Q_y=Q_y P_(x+d_i) Q_y!=0.
```

The common-range version of `(4)` gives a nonzero row bridge

```text
P_x Q_y P_(x+d_i)!=0.                                         (5)
```

For completeness, the common-range assertion follows from
`Q_yP_xQ_y=Q_yP_(x+d_i)Q_y=E!=0`: the squared HS norm of the cross block is
the trace of `E^2`, hence is nonzero.

Suppose more generally that `(5)` holds with difference `d`.  Equation `(2)`
transports the same nonzero block from `Q_y` to the orthogonal spectral block

```text
Q_(y+r_i),                 r_i=c_i+T_i^*d.
```

The bridge fact produces `Q_yP_xQ_(y+r_i)!=0`.  Apply `(3)` with index `j`
and bridge back.  The set of row differences supporting a nonzero block is
therefore closed under

```text
F_(j,i)(d)=d_j+T_j^(-*)c_i+T_j^(-*)T_i^*d.                     (6)
```

Take `(j,i)=(0,1)`.  Self-adjointness gives the affine permutation

```text
F(d)=A d+k,                  k=d_0+c_1.                         (7)
```

Since `A-I` is invertible, `F` has one fixed point `v`.  Conjugating by the
translation `d->d+v` identifies `F` with multiplication by the primitive
element `alpha`.  Hence every non-fixed orbit has size `2^n-1`.

The initial bridge set contains both `d_0` and `d_1`.  Here

```text
d_0=1,              d_1=alpha^(-1/2),                          (8)
```

so they are distinct.  Moreover `F(d_1)=d_0`.  Since an affine permutation's
fixed point has itself as its unique preimage, `d_0` is not fixed.  Starting
at the initial bridge `d_0`, the bridge step is valid until the orbit reaches
`d_1`: its only possible failure is `r_1=c_1+A d=0`, which occurs exactly at
`d=d_1`, and there `F(d_1)=d_0` merely closes the orbit already traversed.
Iterating `(7)` therefore gives `2^n-1` distinct labels `x+d` with nonzero spectral
projections `P_(x+d)`.  These projections are mutually orthogonal, giving
the older bound `dim(H)>=2^n-1` directly.

The target's stronger conclusion now follows without losing the fixed label.
Tensor `U,W` with a canonical Weyl pair for the trace pairing.  Both sampled
signs cancel, so `two-untwisted-field-matchings-force-complete-cross-commutation`
makes the tensor-product copies commute on every pair.  Cancelling the
canonical Weyl commutator gives `(PM2)`.  Conjugation by `W(b)` then acts
freely and transitively on the `2^n` character atoms of `U`; all nonzero atom
ranks agree, proving `2^n | dim(H)`.  Thus the bridge orbit remains an
independent exact support check, while the tensor argument proves the full
claim.
