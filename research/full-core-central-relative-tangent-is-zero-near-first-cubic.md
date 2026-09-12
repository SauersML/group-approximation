---
rg: 2
id: full-core-central-relative-tangent-is-zero-near-first-cubic
kind: claim
title: A relative tangent centralizing the full BS core vanishes below the first-cubic operator threshold
distinct_from:
  relative-tangent-spectral-cuts-can-have-full-bs-hull: that constructs a genuine fixed-R tangent whose spectral cut has full BS hull; this proves why imposing the missing S-commutator cannot repair that hull explosion.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for a splitting on the genuine fixed-R tangent manifold; this refutes only a full-core-central ansatz for its correction.
  same-core-involution-cubic-gauge-coercivity: that is a nonlinear estimate after a nearby exact extender is selected; this is the elementary linear obstruction before any endpoint is selected.
---

**ESTABLISHED; FULL-CORE-CENTRAL CORRECTIONS ARE ZERO.**  Use the old
half-parabolic coordinates

```text
<x,r,s | x^2, (xr)^2, (xs^2)^3,
          rsr^(-1)=s^4, (xrs)^3>.
```

Let `(R,S)` be an exact `BS(1,4)` core, let `X` be an involution, and put

```text
A=XS^2,                   U=A^3.
```

Suppose an anti-Hermitian matrix `h` satisfies

```text
[h,R]=[h,S]=0,                    XhX=-h.               (FCT1)
```

Then

```text
Ad_A(h)=XS^2hS^(-2)X=XhX=-h,
Ad_U(h)=Ad_A^3(h)=-h.                                  (FCT2)
```

Consequently, for `p=2` or `p=infinity`,

```text
2||h||_p
 =||UhU^*-h||_p
 <=2||U-I||_op ||h||_p.                                (FCT3)
```

If

```text
||(XS^2)^3-I||_op<1,                                   (FCT4)
```

then `(FCT3)` forces `h=0`.  In square-free coordinates `T=S^2`, this is
the identical calculation with `A=XT` and `[h,T]=0`.

The actual fixed-core relative rows are

```text
X^2=I,                       XRX=R^(-1).
```

Their tangent equations are only

```text
XhX=-h,                      [h,R]=0.                  (FCT5)
```

There is no defining row prescribing conjugation of `S` or `T` by `X`.
Thus adding `[h,S]=0` does not select a well-behaved normal correction: it
deletes every correction direction once the first cubic has operator defect
below one.  In particular, no right inverse for a nonzero cubic residual can
take values in the full BS-core commutant in the passive regime.

This closes the most tempting repair of
`relative-tangent-spectral-cuts-can-have-full-bs-hull`.  Requiring the
correction's spectral projections to reduce `S` would require precisely the
extra commutator which forces the correction itself to vanish.  A genuine
cb splitting must instead control operator norm while allowing
`[h,S] != 0`; a genuine L2 splitting cannot be upgraded by exact reducing
spectral cuts.

