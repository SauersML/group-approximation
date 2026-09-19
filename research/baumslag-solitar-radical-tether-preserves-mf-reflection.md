---
rg: 2
id: baumslag-solitar-radical-tether-preserves-mf-reflection
kind: claim
title: A Baumslag--Solitar tether preserves the MF reflection and forces torsion-free acylindrical geometry
artifacts:
  - research/baumslag-solitar-radical-tether-proof.md
distinct_from:
  torsion-free-fp-ah-mf-radical-seed: that asks for the initial MF-invisible word; this takes any torsion-free finitely presented MF-radical word and adds acylindrical geometry without changing the universal MF quotient.
  two-generated-single-element-hull-router: that produces a two-generated quotient by small cancellation; this is an explicit one-relator amalgam which remains an overgroup and does not reduce the number of generators.
---

**ESTABLISHED, WITH NO PROPERTY `(T)`.**  Let `E` be finitely presented and
torsion-free and let

```text
1 != d in Rad_MF(E).
```

Put

```text
A=<E,t | d t d^(-1)=t^2>.
```

Then `E->A` is injective, `A` is finitely presented, torsion-free and
acylindrically hyperbolic, and, for the natural epimorphism

```text
p:A->E/Rad_MF(E),        p(t)=1,
```

one has

```text
Rad_MF(A)=ker(p),
A/Rad_MF(A) ~= E/Rad_MF(E).
```

In particular `d,t in Rad_MF(A)`.  Thus the tether adds an explicit
acylindrically hyperbolic direction while leaving the universal MF quotient
unchanged.

DERIVATION
baumslag-solitar-radical-tether-proof
