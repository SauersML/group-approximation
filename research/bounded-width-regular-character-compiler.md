---
rg: 2
id: bounded-width-regular-character-compiler
kind: claim
title: Regular-character group-table losses have a quantum-sound bounded-width CSP compilation
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

**High-risk positive target.** Compile every fixed finite regular-character
Q3.4 loss instance into a finite-domain bounded-width CSP so that:

1. sufficiently small unitary/HS loss gives operator satisfiability (or a
   robust near-satisfying operator assignment) of the compiled instance;
2. the compilation is quantum-sound -- noncommuting assignments cannot exploit
   a classical pp-reduction that silently assumes commutativity;
3. a classical satisfying/near-satisfying assignment decodes to a finite action
   with the original multiplication and fixed-point loss small.

Combined with `bounded-width-operator-csp-no-gap`, such a compiler would give
the required quantum-to-classical zero-loss transfer without pointwise rounding.

## Attempts

- **Declare group multiplication a Mal'tsev/bounded-width relation.** False in
  the needed form: coordinatewise `m(a,b,c)=ab^{-1}c` does not preserve
  `xy=z` in a nonabelian group without reordering factors; even abelian affine
  equation CSPs live in the unbounded-width regime where contextual operator
  gaps occur.
- **Use an arbitrary classical CSP reduction.** Classical pp-definitions need
  not be quantum-sound. Any serious compiler must use commutativity gadgets or
  the modern quantum-polymorphism/Galois machinery and must remain robust in
  the approximate model.
- **Decode only an abstract subgroup.** Insufficient: Q3.4 requires finite
  action/fixed-point statistics, not merely a subgroup satisfying finitely many
  memberships. Finite-action decoding is part of the claim.
