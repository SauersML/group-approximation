---
rg: 2
id: finite-residual-quotients-are-universal-linear-reflections
kind: claim
title: The finite-residual quotient is the universal finitely presented linear reflection
root: true
artifacts:
  - research/finite-residual-universal-linear-reflection-proof.md
distinct_from:
  grothendieck-profinite-representation-equivalence: that records Grothendieck's comparison theorem for an arbitrary map inducing an isomorphism of profinite completions; this identifies the canonical quotient reflection and computes its kernel intrinsically.
  grothendieck-free-representation-category-equivalence: that asks for one earlier family to satisfy Grothendieck's criterion; this is the quotient theorem that applies whenever the kernel lies in the finite residual.
---

Let `Gamma` be a finitely generated group and let

```text
R_fin(Gamma)=intersection{ker(f): f:Gamma->F, F finite}
```

be its finite residual.  If `N normal Gamma`, the quotient map
`q:Gamma->Gamma/N` has the following equivalent properties.

1. `N <= R_fin(Gamma)`.
2. `q` induces an isomorphism of profinite completions.
3. For every nonzero commutative ring `A`, restriction along `q` is an
   equivalence

   ```text
   q_A^*:Rep_A^fp(Gamma/N) ~= Rep_A^fp(Gamma),       (ULR1)
   ```

   where an object is a finitely presented `A`-module equipped with a group
   action and a morphism is an equivariant `A`-linear map.

Because `q` is onto, `(ULR1)` is more rigid than an abstract equivalence:
every action of `Gamma` kills `N` and therefore descends uniquely to
`Gamma/N`, while the underlying module and every intertwiner remain
unchanged.  The equivalences commute with extension of scalars, finite direct
sums, tensor products, and every exact sequence whose terms are finitely
presented.

Consequently the finite residual has the intrinsic description

```text
R_fin(Gamma)
 = intersection ker(rho),                            (ULR2)
```

where `rho` ranges over all actions of `Gamma` on all finitely presented
modules over all nonzero commutative rings.  Thus finite quotients already
determine the complete finitely presented linear representation theory over
every coefficient ring.
