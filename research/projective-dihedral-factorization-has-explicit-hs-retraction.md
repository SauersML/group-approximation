---
rg: 2
id: projective-dihedral-factorization-has-explicit-hs-retraction
kind: claim
title: Projective-dihedral factorization has an explicit dimension-free Hilbert--Schmidt retraction
distinct_from:
  bs14-relative-involution-extension-stability: that asks for simultaneous flexible repair of the reflection and both modular cubic rows over an exact BS14 core; this solves only the factorization/reflection row and quantifies exactly how projecting back to it reintroduces the other residuals.
  bs14-two-cubic-strict-repair-constants-diverge: that proves same-dimensional simultaneous repair is impossible on compressed Weil packets; this gives a positive strict retraction for the virtually cyclic factorization locus and locates the divergence entirely in its intersection with the BS and cubic loci.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for an energy-paid global completion of all packet types; this proves no multiplicity or packet obstruction is attached to splitting the stable letter into the two Weyl factors once one factor is retained.
---

**ESTABLISHED.** Fix `epsilon in {1,-1}`. Let `A,C in U(d)` satisfy

```text
A^2=epsilon I
```

and put

```text
eta=||A^(-1) C A-C^(-1)||_2.                         (PDF1)
```

There is a unitary `C_0` such that

```text
A^(-1) C_0 A=C_0^(-1),
||C_0-C||_2<=eta/sqrt(2).                             (PDF2)
```

More precisely, set `D=A^(-1)C`. Then

```text
||D^2-epsilon I||_2=eta.                              (PDF3)
```

Spectrally round `D` to the nearer root of `z^2=epsilon`, obtaining `D_0`.
Pointwise on the circle,

```text
dist(z,{roots of z^2=epsilon})
 <= |z^2-epsilon|/sqrt(2),                            (PDF4)
```

so `D_0^2=epsilon I` and `||D_0-D||_2<=eta/sqrt(2)`. Put

```text
B_0=D_0,                  C_0=A B_0.                  (PDF5)
```

Then

```text
A^2=B_0^2=epsilon I,       C_0=A B_0,                 (PDF6)
```

and `(PDF2)` follows. Thus the second Weyl factor and the reflection relation
have a same-dimensional, dimension-free retraction while `A` is held fixed.

This remains useful after standalone `BS(1,4)` repair. Suppose the original
`C` obeys the reflection relation exactly and a corrected unitary `C'`
satisfies `||C'-C||_2<=delta`. Applying the retraction to `C'` gives

```text
||C_0'-C'||_2<=sqrt(2) delta,
||C_0'-C||_2<=(1+sqrt(2))delta.                       (PDF7)
```

If `(C',X')` is an exact `BS(1,4)` pair, projection back to the factorized
locus has fourth-power residual at most

```text
||C_0' X' (C_0')^(-1)-(X')^4||_2
 <=2||C_0'-C'||_2
 <=2sqrt(2)delta.                                    (PDF8)
```

Likewise, the modular word `W(C)=A^(-1) C X'` changes by
`||C_0'-C'||_2`, so its cubic residual changes by at most
`3||C_0'-C'||_2`.

Consequently the literal factorization `C=AB` is not an independent repair
gate. It can always be restored with an absolute constant and no padding.
What remains is simultaneous intersection: the retraction need not preserve
the exact `BS(1,4)` dynamics or the two order-three modular relators. An
alternating-retraction proof would require a dimension-uniform positive angle
between those exact loci. The slow regular Koopman modes and compressed Weil
packets show that such an angle is not supplied by the skeleton or strict
same-dimensional geometry alone.

DERIVATION
projective-dihedral-retraction-proof
