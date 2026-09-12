---
rg: 2
id: stw84-crossed-product-symbol-and-coherent-stage-proof
kind: route
title: Use finite coefficient crossed products and average residual unitaries into commutants
target: stw84-invariant-coefficient-stages-restore-two-fourier-colours
requires:
  - stw84-scalar-fourier-row-two-colour
artifacts:
  - research/artifacts/stw84-invariant-coefficient-two-colour-audit-2026-08-30.md
---

## 1. The correct coefficient symbol

Let

```text
w=n^(-1/2)(1,U,...,U^(n-1))
```

be a row over `C*(D,U)`.  Then `(ICF1)` is `c |-> w c w^*`, so it is
c.p.c.  Invariance of `D` is exactly what ensures that every entry of this
row compression remains in `C*(D,U)`.

The restriction `beta=alpha|D` permutes the finitely many matrix summands
of `D`.  Some power `beta^q` fixes every summand and is inner there.  Thus,
after multiplying `U^q` by a unitary of `D`, one obtains a unitary commuting
with `D`.  It follows that `D rtimes_beta Z` is a subhomogeneous algebra
finite over `C(T)`; equivalently its irreducible dimensions are uniformly
bounded and its primitive strata have dimension at most one.  Hence

```text
dim_nuc(D rtimes_beta Z)<=1.
```

The canonical covariant representation embeds this crossed product as
`C*(D,U)`: injectivity follows from the faithful conditional expectations
for the amenable group `Z`.  This proves `(ICF2)`.

## 2. Cut the two coefficient colours by the carrier

Approximate the finite set `Sigma_(D,n)(E)` inside `C*(D,U)` using the two
nuclear-dimension colours from `(ICF2)`.  Postcomposing each outgoing
order-zero map with the inclusion into `A` preserves order zero.

The unit ball of each finite-dimensional outgoing range is uniformly
approximable by finite Fourier polynomials

```text
sum_(|k|<=L) d_k U^k,       d_k in D.
```

Because `[h,D]=0` and

```text
||[h,U^k]||<=|k| ||[h,U]||,
```

condition `(ICF3)` makes `h` uniformly quasicentral on both outgoing
ranges.  Cutting them by `h^(1/2)` therefore gives c.p.c. maps with
arbitrarily small order-zero defect.  Uniform stability of order-zero maps
on finite-dimensional domains repairs the two cut maps to exact c.p.c.
order-zero maps.  Contractivity of the cutdown and the original
approximation prove `(ICF4)`, exactly as in the scalar-row proof.

## 3. Correct a coherently inner stage

Assume `(ICF5)` and put

```text
W=v^*U.
```

For every contraction `d in D`, covariance gives

```text
||W d W^*-d||
 =||v^*alpha(d)v-d||<delta.                            (ICF7)
```

In particular `W` almost commutes uniformly with the unitary group of
`D`.  Average over its normalized Haar measure:

```text
x=integral_(u in U(D)) u W u^* du.                    (ICF8)
```

Then `x in D' intersection A` and `||x-W||<delta`.  For `delta<1`, `x` is
invertible.  Its polar unitary

```text
W'=x(x^*x)^(-1/2)
```

also belongs to `D' intersection A`, and

```text
||W'-W|| ->0       as delta->0.                        (ICF9)
```

Therefore `U=vW` is close to `vW'`, while `vW'` belongs to

```text
C*(D,W'),
```

which is a quotient of `D tensor C(T)` and has nuclear dimension at most
one.

Given a finite subset of `A`, first approximate it by Fourier polynomials.
Use `(ICF5)` on their finitely many coefficients, and then choose `delta`
so small that replacing every coefficient by an element of `D` and every
power of `U` by the corresponding power of `vW'` changes those polynomials
by less than the requested tolerance.  Thus `A` is locally approximated by
subalgebras of nuclear dimension at most one.

Local approximation gives `(ICF6)`.  Explicitly, after approximating the
finite set into one `C*(D,W')`, extend the incoming c.p.c. maps of its
two-colour approximation to `A` coordinatewise by Arveson's theorem, and
compose the outgoing maps with the inclusion.  This argument needs no
separability or directed choice beyond the finite-set hypothesis.

The proof shows why ordinary approximate innerness is insufficient:
pointwise implementation on a prescribed finite set does not make `W`
uniformly close to the commutant of an entire finite-dimensional stage.
Condition `(ICF5)` supplies exactly that missing uniform coherence.
