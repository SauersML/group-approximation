---
rg: 2
id: hecke-and-zero-compression-has-a-fixed-density-bass-serre-absorber
kind: claim
title: The Hecke AND zero-compression cell has a fixed-density Bass--Serre absorber
distinct_from:
  central-marked-two-cycle-zero-compression-cell: that gives the abstract selected two-cycle and its zero-compression estimate; this identifies the forbidden Boolean AND atom explicitly and proves that the cell remains exactly satisfiable at quarter mass in matrices.
  verifier-controlled-two-cycle-is-existentially-loss-blind: that gives a two-dimensional completion for an arbitrary verifier reflection; this proves the stronger finite-quotient obstruction for every finite Bass--Serre assembly and every algebraic source corner.
  common-corner-literal-contexts-stop-at-bass-serre: that pulls back a Connes-embeddable canonical corner trace; this produces an exact finite-dimensional representation and needs only that the source algebra have no matrix model.
  mark-relative-finite-packet-decoder-is-impossible: that rules out a qualitative mark-relative decoder in residually finite packets; this rules out a unital source-to-corner star homomorphism and quantifies the local AND absorber.
---

**ESTABLISHED LOCAL CELL AND SHARP ASSEMBLY FIREWALL; NO ROOT CLAIM.**
Let

```text
D=<x,y,t | x^2=y^2=t^2=1, [x,y]=[x,t]=1,
             t y t^(-1)=x y>.                           (HAZ1)
```

This is the order-eight dihedral group.  Put

```text
P_x=(1-x)/2,       P_y=(1-y)/2,
p=P_x P_y=(1-x)(1-y)/4.                                (HAZ2)
```

Thus `p` is exactly the Boolean atom on which both input projections are
one.  Nevertheless the ordinary group relations imply

```text
t p t^(-1)=(1-x)(1-xy)/4,       p t p=0,               (HAZ3)
```

while the normalized regular trace satisfies

```text
tau_D(p)=1/4.                                           (HAZ4)
```

So a finite-subgroup Hecke mismatch wordizes the zero compression of one
forbidden AND cell, but it does not make the forbidden atom small.  It has an
exact finite-dimensional model at fixed positive density.

The zero compression is dimension-independently robust, but in the wrong
direction for soundness.  Let `X,Y` be exact commuting reflections and `T`
a unitary in a matrix algebra.  Set

```text
P=(1-X)(1-Y)/4,
P'=(1-X)(1-XY)/4,
delta_x=||T X T^*-X||_2,
delta_y=||T Y T^*-XY||_2.                              (HAZ5)
```

Then `PP'=0` and

```text
||P T P||_2 <=(delta_x+delta_y)/2.                      (HAZ6)
```

There is no converse estimate of `tr(P)` by the right side of `(HAZ6)`,
even after adding the exact zero-compression defect: the regular
representation in `(HAZ1)--(HAZ4)` has both sides zero and `tr(P)=1/4`.

There is a general exact obstruction behind this example.  Let `Gamma` be a
residually finite group, let

```text
0!=q=q^*=q^2 in C[Gamma],                               (HAZ7)
```

and let `A` be a unital star algebra.  If there is a unit-preserving star
homomorphism

```text
Phi:A -> q C^*(Gamma) q,              Phi(1_A)=q,       (HAZ8)
```

then `A` has a nonzero unital finite-dimensional star representation.
No injectivity of `Phi` is required.

Indeed, one finite quotient of `Gamma` can be chosen injective on the finite
support of `q`; the image of `q` is then a nonzero projection.  Compose
`Phi` with that quotient and restrict its regular representation to the
range of the image of `q`.

Consequently `(HAZ8)` is impossible when `A` is the finite perfect-qc
SynchBCS algebra from
`perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model`.
In particular it is impossible when `Gamma` is the fundamental group of a
finite graph of finite groups, because such a group is virtually free and
residually finite.

More locally, if a finite Bass--Serre assembly contains the packet `(HAZ1)`
as a vertex group, the detecting finite quotient may simultaneously be
chosen injective on `D` and on `supp(q)`.  Its regular representation retains

```text
tr(p)=1/4,          p t p=0                             (HAZ9)
```

and satisfies every defining group relator exactly.  Hence adjoining any
finite collection of finite-subgroup amalgams, HNN consistency ports, or
finite central-type blocks cannot turn the one-cell Hecke compression into
a dimension-independent AND-mass decoder.

A surviving assembly must leave residual finiteness already on the
algebraic corner, placing that corner in the finite-dimensional radical, or
add a genuinely non-Bass--Serre occurrence relation with a matrix-only
return modulus.  Another finite character mismatch, finite graph-of-groups
cycle, or finite central-type packet cannot close the gate.

DERIVATION
hecke-and-absorber-and-rf-corner-proof
