---
rg: 2
id: simple-alternating-limit-excludes-standard-self-similar-shifts
kind: claim
title: Faithful rooted-tree self-similarity and exact alternating-coordinate shifts cannot produce the desired simple LEF kernel
distinct_from:
  torsion-free-kazhdan-alternating-mother-limit-gate: That isolates torsion and bounded normal-generation conditions for a simple marked limit; this rules out the two standard mechanisms for adding the automorphic presentation after such a limit is chosen.
  fp-mapping-torus-iff-finite-automorphic-presentation: That identifies the abstract finite-presentation datum needed; this shows why the familiar automaton and coordinate-shift sources of that datum do not apply to the alternating-limit program.
---

Two standard ways of obtaining finite `L`-presentations cannot supply the
automorphism needed by the torsion-free simple alternating-limit program.

1. An infinite simple group admits no faithful action on a locally finite
   rooted tree.  Consequently it cannot be a faithful self-similar or finite-
   state automaton group in the usual sense.  The familiar finite
   `L`-presentations of contracting branch groups therefore cannot simply be
   combined with simplicity, irrespective of property `(T)` or
   torsion-freeness.

2. Let

```text
q_i : Gamma ->> Alt(n_i),             n_i>=7,
```

where the degrees are unbounded.  There is no automorphism `alpha` of the
mother group which realizes an exact shift of the quotient kernels

```text
alpha^(-1)(ker q_i)=ker q_(i+1)                         (SAS1)
```

along an unbounded-degree subsequence.  Likewise, no coordinate-permuting
automorphism of the product or direct sum of the finite simple factors shifts
`Alt(n_i)` to `Alt(n_(i+1))` when the degrees differ.

Thus any successful finite automorphic presentation for a simple alternating
marked limit must be a genuinely new relation-level symmetry of the limit.  It
cannot be inherited from a faithful rooted-tree recursion or from the obvious
shift of the finite alternating approximants.  This does not rule out an
abstract automorphism preserving the stable marked-limit kernel.

DERIVATION
simple-alternating-shift-no-go-proof
