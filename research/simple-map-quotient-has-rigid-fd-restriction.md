---
rg: 2
id: simple-map-quotient-has-rigid-fd-restriction
kind: claim
title: A finitely generated simple nonsofic quotient makes finite-dimensional restriction to its kernel injective
distinct_from:
  compression-defect-dies-in-finite-dimensions: that kills a particular compression defect in finite-dimensional representations; this is a general restriction-rigidity theorem for a free presentation of any finitely generated infinite simple nonsofic quotient.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that proves minimal almost periodicity for one named group; this derives it from finite generation, simplicity and nonsoficity and then applies it to a presentation kernel.
---

**ESTABLISHED.** Let `Q=F/K`, where `F` is finitely generated and `Q` is
infinite, simple and nonsofic. For every `d`, restriction is injective:

```text
Hom(F,U(d)) -> Hom(K,U(d)).                              (PRR1)
```

Indeed, `Q` has no nontrivial finite-dimensional unitary representation. A
nontrivial representation is faithful by simplicity, and would make `Q` a
finitely generated linear group; Mal'cev then makes it residually finite and
hence sofic, a contradiction.

If `u,v:F->U(d)` agree on `K`, let

```text
V=Hom_K(v,u)={T : u(k)T=T v(k) for all k in K}.          (PRR2)
```

Normality of `K` makes `V` invariant under the left-right representation
`Pi(f)T=u(f)T v(f)^*`, and `K` acts trivially there. Thus `Pi|V` factors
through a finite-dimensional representation of `Q`, hence is trivial. Since
the identity operator belongs to `V`,

```text
u(f)v(f)^*=Pi(f)(I)=I
```

for every `f in F`, proving `(PRR1)`.

DERIVATION
simple-map-restriction-rigidity-proof
