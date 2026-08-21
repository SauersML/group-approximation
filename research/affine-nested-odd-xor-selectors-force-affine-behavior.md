---
rg: 2
id: affine-nested-odd-xor-selectors-force-affine-behavior
kind: claim
title: Affine nested odd-XOR selectors can aggregate only an affine family of scalar behaviors
distinct_from:
  affine-auxiliary-control-flow-barrier: that rules out an affine selector gadget realizing a nonaffine support predicate; this allows arbitrary refinements, duplicate labels, and nested auxiliary selectors, and rules out the different proposal of decoding by the odd XOR of active payloads.
  priority-decoded-contexts-are-not-glued-by-raw-gate-equality: that gives operator countermodels to raw gate gluing after priority decoding; this is a scalar exact obstruction to replacing priority decoding by an aggregate product which is automatically context-independent.
  tensor-affine-selector-pattern-barrier: that concerns tensor patterns of controlled operators; this is the ternary-closure obstruction for the accepted payload behaviors themselves.
---

Let `B` be a nonempty subset of `F_2^n`.  Think of `B` as the set of
unreadable scalar assignments accepted by at least one readable branch of one
fixed tailored-game context.  Consider any finite shared-label compiler of the
following form.

1. There is a finite label set `Lambda`.  Its commuting scalar selector bits
   `s_lambda` and any finite collection of nested or auxiliary commuting
   selector bits obey only affine `F_2` equations.
2. After eliminating the auxiliary bits, every singleton activation
   `e_lambda` is feasible.  This is the branch-completeness condition: every
   labelled branch can occur alone in an exact completeness model.
3. An active label carries a scalar payload `x_lambda in B`, and the proposed
   common decoded payload is the odd-XOR aggregate

   ```text
   X(s)=sum_(lambda: s_lambda=1) x_lambda.                 (AOX1)
   ```

   In involution notation this is the product of the active payload
   involutions.  Vertex-local master labels, refinements of a context label,
   and a finite nested binary selector tree are included whenever their
   scalar selector constraints flatten to affine equations.

If the compiler is required to return an element of `B` for every exact scalar
output model and it contains three distinct complete labels whose payloads
may independently be any prescribed `x,y,z in B`, then

```text
x+y+z in B.                                               (AOX2)
```

Consequently, a branch-complete aggregate compiler with three independently
duplicable labels can work for all payloads in `B` only if `B` is an affine
subspace coset.  In particular, whenever one finite source context has a
nonaffine accepted-behavior union `B`, none of the following repairs the
cross-context alignment problem:

- replacing priority decoding by the product of all active gates;
- refining an edge label to a vertex-star label and taking parity marginals;
- duplicating labels to synchronize different occurrences; or
- inserting finitely many levels of commuting affine nested selectors.

This is an exact scalar obstruction, so operator stability cannot repair it.
It does **not** rule out a noncommutative selector gadget, a source context
whose accepted-behavior union happens to be affine, or a compiler whose
relations couple selector and payload so strongly that the three payload
copies are not independently realizable.

For the TailoredMIP route the resulting source-specific audit is finite and
sharp: compute, for each context of the chosen witness, the union `B` of its
accepted unreadable assignments.  A nonaffine `B` kills every aggregate
odd-XOR/master-label construction above.  If all such unions are affine, that
special structure must be used explicitly; it does not follow merely from
the controlled-linear definition of a tailored game.
