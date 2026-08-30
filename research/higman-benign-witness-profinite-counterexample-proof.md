---
rg: 2
id: higman-benign-witness-profinite-counterexample-proof
kind: route
title: Put the trivial subgroup in Higman's finite-quotient-free group
target: arbitrary-benign-witness-need-not-refine-fold-quotients
requires:
  - linear-sterility-does-not-obstruct-division-embedding
---

First verify the displayed free subgroup without using an abstract
acylindrical-hyperbolicity theorem.  Split Higman's presentation as

```text
A=<a,b,c | b^a=b^2,c^b=c^2>,
B=<a,c,d | d^c=d^2,a^d=a^2>,
H=A *_(<a,c>) B.                                      (BWC1)
```

The group `A` is an HNN extension of
`<b,c | c^b=c^2>=BS(1,2)` with stable letter `a` carrying `<b>` to
`<b^2>`.  The cyclic subgroup `<c>` meets both associated cyclic subgroups
trivially, so Britton normal form makes `<a,c>=<a>*<c>`.  The symmetric
argument in `B`, now using `c` as the stable letter over
`<d,a | a^d=a^2>`, gives the same free subgroup.  Amalgam normal form in
`(BWC1)` therefore embeds

```text
F=<a,c> ~= F_2                                             (BWC2)
```

in `H`.

Set `N=L={1}` and `K=H`.  The trivial subgroup is finitely generated, and
the preimage of `L` under `(BWC2)` is exactly `N`; hence this is a benign
witness in the precise sense of `Higman.BenignWitness`.  Higman's group has
no nontrivial finite quotient, while `F/N=F_2` is residually finite.

Because `L` is trivial, the associated centralizer HNN extension and its
symmetric subgroup have the free-product normal forms

```text
Gamma=H*<v>,                    S=F_1*F_2,
F_1=F,                          F_2=vFv^(-1).          (BWC3)
```

Let `F'` be the kernel of the epimorphism

```text
F=<a,c> -> C_2,                 a |-> 1, c |-> 0.
```

It is finite-index and normal.  Every homomorphism `theta:Gamma->Q` with
`Q` finite kills `H`, hence kills `F_1` and its conjugate `F_2`.  In
particular `a` lies in `S cap ker(theta)` for every such `theta`.  On the
other hand, if

```text
D=<<F'_1,F_2>>_S,
```

then free-product normal form gives

```text
S/D ~= F/F' ~= C_2,
```

and the image of `a` is nontrivial.  Thus `a` is not in `D`, disproving
`(BW1)(ii)`.

The same example disproves `(BW1)(i)`.  Equation `(BWC3)` gives
`S cap H=F`.  The subgroup `F` is proper in `H`: otherwise the
finite-quotient-free group `H` would be the free group `F_2`.  Choose
`h in H minus F`.  Then `h` is not in `S`, but every finite quotient sends
`h` to `1`, which lies in the image of `S`.  Hence `h` belongs to the
profinite closure of `S` in `Gamma`, so `S` is not profinitely closed.

