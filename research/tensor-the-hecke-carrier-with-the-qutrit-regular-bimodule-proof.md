---
rg: 2
id: tensor-the-hecke-carrier-with-the-qutrit-regular-bimodule-proof
kind: route
title: Put Hecke motion on the left and the authenticated head on the right
target: raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel
requires:
  - two-raw-roots-have-a-uniform-full-carrier-gap
  - rectangular-commutant-and-qutrit-bimodule-absorber-proof
---

Let `K=ell^2(F_0)`, let `lambda` denote left translation, and
identify `K` with the Hilbert space completion of `C[F_0]`. Put

```text
P=R(q_b),                       P(x)=x q_b.
```

Since `q_b` is a self-adjoint idempotent, `P` is an orthogonal
projection. Left and right multiplication commute, so

```text
P lambda(u)=lambda(u)P                  for every u in F_0. (THQ1)
```

The normalized regular trace calculation gives

```text
rank(P)=|F_0| tau_(F_0)(q_b)=288/18=16.                  (THQ2)
```

Let `K_0=(I-P)K` and let `j:K_0->K` be the inclusion. For a
representation `beta:F_N->U(V)`, define

```text
H_T=V tensor K,                  H_S=V tensor K_0,

Pi_T(g,u)=beta(g) tensor lambda(u),
Pi_S(g,u)=(beta(g) tensor lambda(u)) restricted to H_S,

S=I_V tensor j,                  T=S^*,
Q=I_V tensor P.                                           (THQ3)
```

Equation `(THQ1)` makes `H_S` invariant and gives

```text
Pi_T(g,u)S=S Pi_S(g,u).
```

The inclusion identities give

```text
TS=I_(H_S),                 ST=I_(H_T)-Q.                 (THQ4)
```

Finally, by `(THQ2)`,

```text
tr_(H_T)(Q)
 =dim(V)rank(P)/(dim(V)|F_0|)
 =16/288
 =1/18.                                                     (THQ5)
```

This proves `(HQH1)`. The target `F_0`-representation is
`dim(V)` copies of the left regular representation, so tensoring has
not changed any normalized qutrit trace.

Every member of the constant-core plus two-raw-root control set
`Q_N` is an element of the first factor `F_N`. Substituting
`u=1` in the exact intertwining equation gives

```text
(Pi_T(r,1))S-S(Pi_S(r,1))=0              for every r in Q_N. (THQ6)
```

Therefore the right side of the property-T inequality `(TRG4)` is
zero. Its conclusion is exactly correct: `S` already belongs to the
full `F_N)-intertwiner space. Property T controls representation type,
not the excess multiplicity in `K`.

To see that this is one finite packet rather than a formal tensor
calculation, pass to `H_T direct-sum H_S` and define

```text
z=diag(I_(H_T),-I_(H_S)),
a=[ Q  S ].
  [ T  0 ]
```

From `(THQ4)`,

```text
a^2=z^2=I,                       (az)^4=I.                 (THQ7)
```

The projection `Q` commutes with `Pi_T`, and `S` intertwines
`Pi_S` with `Pi_T`. Hence both `a` and `z` commute with the
diagonal image of `F_N times F_0`. The group `<a,z>` is a quotient
of `D_8`; the other image is finite because both factors are finite.
This proves `(HQH3)`.

There are two useful readings of the same construction.

1. Replace `F_0` by the abelian head torus
   `B=<H> times C`. Then `q_b=Ee_b` is central, left and right
   multiplication agree, and `Q` is literally the named qutrit packet
   atom.

2. Keep the full `F_0`. Then `Q=R(q_b)` is the commutant copy of
   the natural left atom. Both have rank sixteen, but only the right copy
   can be a full-`F_0)-covariant cokernel. An equality router between
   the two exists by rank, yet cannot be an `F_0` intertwiner.

Thus adjoining the entire two-root Hecke control set to either finite
same-trace model leaves an exact positive-density head. The next relation
must mix the left-right equality router with a nonfinite Jacobson
coefficient; no further finite carrier spectral estimate can remove this
model.
