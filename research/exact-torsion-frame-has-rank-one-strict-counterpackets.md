---
rg: 2
id: exact-torsion-frame-has-rank-one-strict-counterpackets
kind: claim
title: Exact C2 star C3 star C3 torsion frames still have rank-one strict Iwahori counterpackets
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that constructs the compressed Weil packet with approximate cubic rows in square-free Iwahori coordinates; this exactifies all three torsion rows and locates the surviving defect in the two explicit free-product words.
  iwahori-two-triangle-torsion-normal-form: that normalizes an arbitrary tuple but does not prove that a normalized tuple can remain uniformly far from the quotient representation variety; this applies it to the arithmetic rank-one packet.
  bs14-two-cubic-strict-repair-constants-diverge: that keeps the BS and dihedral rows exact while the cubic rows are approximate; this moves the same obstruction across the Tietze chart so the torsion rows are exact and the structural rows are approximate.
---

Let

```text
F=<X,A,B | X^2=A^3=B^3=1> = C_2*C_3*C_3.
```

Under

```text
T=XA,                 R=A^2 X A^2 B,                 (ETF1)
```

the two remaining Iwahori relators are the freely reduced words

```text
u=(XR)^2
 =X A^2 X A^2 B X A^2 X A^2 B,                     (ETF2)

v=R T R^(-1) T^(-4)
 =A^2 X A^2 B X A B^2 X A^2 X A^2 X.               (ETF3)
```

There are constants `c,C>0` and, for every prime `p=1 mod 4`, exact
`d_p=(p-1)/2` dimensional representations

```text
rho_p:F -> U(d_p)
```

such that

```text
max(||rho_p(u)-1||_2,||rho_p(v)-1||_2)<=C/sqrt(p),   (ETF4)
```

but for every exact representation `sigma` of the Iwahori quotient
`F/<<u,v>>` in the same dimension,

```text
max_(g in {X,A,B}) ||rho_p(g)-sigma(g)||_2 >= c.     (ETF5)
```

Allowing one additional dimension removes the obstruction: the exact even
Weil representation of dimension `(p+1)/2` is at generalized flexible
distance `O(p^(-1/2))` from `rho_p`.

On the subfamily `p=5 mod 8`,
`five-mod-eight-torsion-normalization-retains-a-padding-charge` proves the
matching post-normalization estimate

```text
||rho_p(u)-1||_F^2+||rho_p(v)-1||_F^2 >= 2/23.
```

Thus the restored line is paid by the structural energy even after every
torsion row has been made exact.

Thus no dimension-free global error bound on the exact torsion-frame variety
can turn the two word defects into same-dimensional distance from the exact
quotient, even qualitatively.  In particular a global SOS or cocycle
certificate whose conclusion is strict normalized-HS rounding cannot exist.
This does not contradict the congruence near-stratum infinitesimal gap or the
open flexible endpoint: the counterpacket is repaired by precisely one
boundary line.
