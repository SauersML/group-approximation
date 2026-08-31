---
rg: 2
id: deligne-twisted-fibres-have-no-amenable-trace
kind: claim
title: The two nontrivial Deligne twisted fibres have no amenable trace
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: LLP is a local lifting property and remains open for these fibres; amenable traces are ruled out here by C-star property T and finite-dimensional invisibility.
  deligne-sector-gap-is-exactly-nonhyperlinearity: a Connes-embeddable trace need not be amenable, so excluding amenable traces does not exclude arbitrary matrix-ultraproduct models and does not prove the sector gap.
---

Let `alpha` be either nontrivial mod-three Deligne multiplier on
`Gamma = Sp_4(Z)`.  Then the full twisted group C-star algebra

```text
A_alpha = C^*(Gamma; alpha)
```

has no amenable tracial state.

Indeed, `E_3` is a finite central extension of the property-(T) group
`Sp_4(Z)`, hence has property (T).  Therefore `C^*(E_3)` has C-star property
(T).  The central-character fibre `A_alpha` is a unital quotient (equivalently
a central summand) of `C^*(E_3)`, so it also has property (T).  By
`property-t-cstar-amenable-trace-forces-fd-quotient`, an amenable trace on
`A_alpha` would give a nonzero finite-dimensional representation of
`A_alpha`, equivalently a finite-dimensional representation of `E_3` on
which the central generator is `omega I` or `omega^2 I`.  This contradicts
`deligne-triple-cover-fd-central-invisibility`.

This rules out all Følner/quasidiagonal compressions of a fixed exact
projective representation.  It does not rule out arbitrary tracial
matrix-ultraproduct embeddings: amenable traces form a strictly smaller class
than Connes-embeddable traces.

The direct compression fence is
`deligne-fixed-projective-representation-folner-compression-no-go`.
