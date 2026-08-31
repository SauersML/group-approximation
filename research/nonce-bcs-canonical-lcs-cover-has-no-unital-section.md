---
rg: 2
id: nonce-bcs-canonical-lcs-cover-has-no-unital-section
kind: claim
title: The canonical LCS cover of the non-RU BCS has no unital section
distinct_from:
  every-bcs-is-a-trace-pullback-quotient-of-an-lcs: that constructs the reverse quotient and pulls every trace back; this proves that the quotient cannot be reversed for the separated MIP-star source.
  trace-extending-bcs-to-lcs-maps-are-already-terminal: that says a trace-extending forward map would solve the group problem; this gives a concrete tame LCS cover for which even a forward unital map is impossible.
  property-t-trace-envelope-has-rigid-coequalizers: that obstructs trace-preserving quotients after faithful GNS reduction; this is an elementary pre-GNS nonsplitting theorem detected by a scalar LCS representation.
---

**ESTABLISHED MULTIPLICATIVE-LIFT FIREWALL.** Let `B_*` be the finite
tracially satisfiable but non-`R^U`-satisfiable BCS, and let

```text
q:A_(L_*)->A_(B_*)                                      (NSL1)
```

be its right-angled-Coxeter LCS cover from
`every-bcs-is-a-trace-pullback-quotient-of-an-lcs`.
There is no unital star-homomorphism

```text
i:A_(B_*)->A_(L_*).                                     (NSL2)
```

In particular, (NSL1) has no unital star-homomorphic section.

Consequently `A_(B_*)` is not projective in the category of unital
C-star algebras: the identity map does not lift through the explicit
surjection (NSL1).

This is the exact limitation of an LLP, local-reflexivity, or
finite-dimensional operator-system argument at this cover. Such properties
may produce local ucp lifts. They do not make those lifts compatible and
multiplicative on the full BCS algebra. Any claimed upgrade to a unital
star-homomorphism would contradict the scalar perfect model of `L_*` and
would already prove the terminal non-`R^U` transfer.

DERIVATION
scalar-lcs-character-forbids-a-bcs-section-proof
