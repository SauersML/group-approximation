---
rg: 2
id: mf-radical-saturation-along-any-homomorphism
kind: claim
title: A radical word whose image normally generates the target saturates the target, with no surjectivity
artifacts:
  - research/mf-radical-saturation-along-any-homomorphism-proof.md
distinct_from:
  torsion-free-mf-radical-routing-saturation: that assumes the routing map is surjective; this assumes only a homomorphism, which lets an embedding (or any map) replace the small-cancellation quotient.
---

**ESTABLISHED, NO PROPERTY `(T)`.**  Let `f:E->Q` be any group homomorphism,
and let `d in Rad_MF(E)` satisfy

```text
f(d) != 1,        normalClosure_Q(f(d)) = Q.
```

Then `Rad_MF(Q)=Q`, `Q` is nontrivial, and every nontrivial quotient `L` of
`Q` satisfies `Rad_MF(L)=L`.

So the routing obligation in the torsion-free manuscript lane can be met by
a map that is injective rather than surjective.  In particular
`torsion-free-embedding-normal-generation-router` already supplies it for
every finitely presented torsion-free `E`, with `f` an embedding.
