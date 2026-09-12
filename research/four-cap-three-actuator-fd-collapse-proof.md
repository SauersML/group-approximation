---
rg: 2
id: four-cap-three-actuator-fd-collapse-proof
kind: route
title: Amalgamate a Thompson-V involution with the cross-chart D8 seed
target: four-cap-three-actuator-destroys-all-fd-packet-evaluations
requires:
  - four-cap-two-chart-mixer-has-finite-clifford-evaluator
  - thompson-v-not-lef
---

Thompson's group `V` contains an involution: in the standard action on the
Cantor set, interchange two disjoint basic clopen cylinders and fix the
complement.  Since `u` is nontrivial, the subgroup `<u,J>` in
`V times <J>` is `C_2^2`; it is the same subgroup of the displayed `D_8`.
The amalgam normal form for `(TCA3)` embeds both factors.  In particular its
`D_8` is genuine and `J` is nontrivial.

Every finite-dimensional unitary representation of `V` is trivial.  If its
kernel were not all of `V`, simplicity would make the representation
faithful.  But `V` is finitely generated and every finitely generated linear
group is residually finite, contradicting the non-residual-finiteness
already used in `thompson-v-not-lef`.

In `Gamma_2`, `(TCM3)` makes `z_2` and `b=t z_2 t` involutions with
commutator `J`.  The explicit representation `(TCM5)--(TCM6)` restricts to

```text
z_2 -> I tensor Z,
b   -> I tensor X,
J   -> -I_4,                                             (TAP1)
```

which is the faithful Pauli representation of `D_8`, with a harmless tensor
multiplicity.  Hence `(TCA2)` is an embedded `D_8`.  Applying the amalgam
normal form a second time to `(TCA5)` embeds `Gamma_2`, `Lambda`, and
therefore `K`.

The identified `J` commutes with every generator of both vertex groups, so
it is central in `Gamma_3`.  Its nontriviality and nonvanishing of `q` follow
from either vertex-group embedding.

Finally let `pi` be finite-dimensional.  Its restriction to the embedded
copy of `V` is trivial, so `pi(u)=1`.  The D8 relation gives

```text
pi(J)=pi([u,s])=[1,pi(s)]=1.
```

This proves `(TCA7)` and `pi(q)=0`.  No residual-finiteness or classification
of representations of the amalgam is used beyond the Malcev argument for
the simple vertex group.
