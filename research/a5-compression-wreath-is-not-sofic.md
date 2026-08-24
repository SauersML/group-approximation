---
rg: 2
id: a5-compression-wreath-is-not-sofic
kind: claim
title: The A5 compression wreath is not sofic
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
distinct_from:
  wreath-not-sofic: that states nonsoficity of the binary wreath candidate directly from the Kun--Thom theorem on infranormal Kazhdan pairs; this transports the same conclusion to the A5 lamp by subgroup heredity, which is the form the invisible-quotient results need and which is the clause a paper plan got backwards.
  a5-wreath-contains-binary-kun-thom-wreath: that supplies only the subgroup inclusion; this draws the soficity conclusion from it.
---

`W_(A_5) = A_5^(G*/Gamma*) x| G*` is **not** sofic.

Soficity passes to subgroups, and `W_(A_5)` contains the binary Kun--Thom
wreath as a subgroup -- take the involution subgroup of `A_5` at each site.
That subgroup is nonsofic, so `W_(A_5)` is nonsofic.

This is worth stating on its own because the neighbouring established node
`wreath-sofic-not-mf` reads "sofic and not MF" for a *different* group -- the
sign-free mod-two quotient -- and the two are easy to conflate.  For the A5
compression wreath itself the correct statement of its approximation status is:

```text
not sofic;  hyperlinearity OPEN;  not MF (its MF radical is A_5^(X) != 1).
```

The non-MF clause needs no separate argument: `Rad_MF(W) = 1` for any MF group,
since the identity is then a homomorphism to an MF group, so a nontrivial MF
radical is by itself a proof of non-MF-ness.

Note the standing interest in the hyperlinear clause.  The open route
`nonhyperlinear-via-simple-lamp-action-recovery` aims to prove `W_(A_5)` is
**non**-hyperlinear, which would answer the program goal.  Anything that
asserts hyperlinearity of this group is asserting the negation of a live
target, not a background fact.
