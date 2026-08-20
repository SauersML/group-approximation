---
rg: 2
id: bcs-projective-kernel-phase-compilation
kind: claim
title: A tracial non-RU BCS can be compiled so one predicate commutator is a negative projective-kernel phase
distinct_from:
  phase-safe-toric-gap-game-exists: that asks for the finished toric game and normal-closure certificate; this is the source-engineering step that puts a designated finite-gadget word in the tracial GNS projective kernel.
  boolean-predicate-central-phase-word: that supplies the local finite phase reader for any predicate; this must couple it equivariantly to the violation structure without adjoining selector shifts that destroy the BCS constraints.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Engineer the fixed Fanizza/Paddock--Slofstra BCS and attach the finite gadget
of `boolean-predicate-central-phase-word` so that one designated word `W`
satisfies, in a perfect tracial model,

```text
pi_tau(W)=-I,                                               (PKP1)
```

while every finite-dimensional approximate model with `W` near `-I` pays a
uniform BCS/LCS energy gap.  The completion must be equivariant for the
**violation projection family**: conjugate partners may permute or count
forbidden atoms, but may not map a satisfied context relation to a violated
one while that relation is imposed as zero.

The compiled presentation must also prove that the central phase survives the
normal closure of the game clauses.  A perfect tracial representation of the
full universal algebra is an acceptable certificate.  No selector sector is
deleted; violation density is read through the projective phase.

## Attempts

- Insert the unitriangular phase word into the fixed Fanizza predicate menu and
  search its tracial GNS representation for a central `-1` lift.
- Permit conjugate partners only when they permute forbidden atoms and preserve
  total violation projection. A naive Weyl selector shift fails this test.
- A candidate satisfying `(PKP1)` without a full universal-algebra model does
  not certify normal-closure survival and is rejected before toric compilation.
