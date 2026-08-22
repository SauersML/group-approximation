---
rg: 2
id: scalar-bs14-exit-angle-energy-dichotomy
kind: claim
title: Scalar BS14 phases can flatten the exit angle but cannot hide active boundary energy
distinct_from:
  even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two: that computes a uniformly transverse arithmetic phase; this classifies the phase dependence for a general scalar cycle.
  positive-fixed-corner-cubic-energy-charges-deleted-rank: that gives the phase-blind energy identity; this combines it with the two-carrier Gram matrix and an active/passive coupling bound.
  two-cubic-residual-carriers-recover-the-deleted-source: that assumes a uniform angle; this proves such an angle is false for general long scalar phases and gives the replacement dichotomy.
---

In a one-line positive-corner dilation, let `q` be fixed by both
`U_1=S^2` and `U_2=RS`, put `Y_i=XU_i`, and assume `Y_i^3=1`.  Write

```text
a=<q,Xq> in (0,1),
Xq=a q+sqrt(1-a^2) z,          z in PH,
g=U_1^*U_2=S^(-2)RS,
c=<z,gz>.                                             (SAE1)
```

Let `Z_i` be the two compressed cubic residual carriers and remove their
common source line `Cz`.  Their remaining one-dimensional exit cosine is

```text
kappa(a,c)=|(1+a)^2 c-a^2|/(1+2a).                   (SAE2)
```

The residual Gram matrix on the two unnormalized exit vectors is

```text
[ n(a)^2                 d(a,c) ]
[ conjugate(d(a,c))      n(a)^2 ],                    (SAE3)

n(a)^2=(1-a)(1+2a)/(1+a),
d(a,c)=(1-a)((1+a)c-a^2/(1+a)).
```

Thus the scalar return phase enters only through the numerical-range
coordinate `c` of the packet operator `g`.

For a multiplicity-one scalar BS packet

```text
O={lambda,lambda^4,...,lambda^(4^(m-1))},
R^m=v,
```

the operator `g` is a weighted cyclic shift and

```text
g^m=chi(O,v)1,
chi(O,v)=v (product_(mu in O) mu)^2                  (SAE4)
```

up to replacing `v` by `v^(-1)` under the opposite shift convention.  Its
spectrum is therefore the complete set of `m`th roots of `chi(O,v)`, and
`c` is a convex combination of those roots.

There is no phase-uniform angle gap.  Choose `chi(O,v)=1` on cycles with
`m->infinity` and put equal spectral weight on the two `g`-eigenvalues
`exp(+-2 pi i/m)`.  Then

```text
c_m=cos(2 pi/m)->1,
kappa(a,c_m)->1                                       (SAE5)
```

for every fixed `a`.  Hence general scalar phases can make the two exits
asymptotically parallel.  This is an exact packet Gram counterfamily; it
does not by itself assert that every such Gram datum extends to a full exact
Iwahori representation.

Nevertheless parallelism does not dilute the boundary energy.  Each cubic
has the phase-independent deleted-line energy

```text
f(a)=4(1-a)^2(1+2a)/(1+a)^3,
f(a)>= (3/8)(1-a^2)^2.                                (SAE6)
```

The squared source coupling is `1-a^2`.  Thus if the energy per missing
direction tends to zero, the source coupling itself tends to zero.  On a
rank-`k` positive corner with eigenvalues `a_j`, for every threshold
`tau>0` the directions with

```text
1-a_j^2>=tau
```

have rank at most

```text
(8/(3 tau^2)) ||first cubic residual||_F^2,            (SAE7)
```

while the complementary directions have total squared off-diagonal source
coupling at most `tau k<=tau d`.  Hence a proof may discard the passive
parallel sector at normalized-HS cost at most `sqrt(tau)`; every active
parallel direction is still paid for by Frobenius energy.

The correct replacement for a uniform carrier-angle theorem is therefore
an **energy-angle dichotomy**: transverse carriers authenticate the source,
whereas nearly parallel carriers must either be energy-paid active boundary
directions or HS-negligible passive directions.

