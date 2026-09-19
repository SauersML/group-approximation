---
rg: 2
id: centralizing-hnn-is-residually-finite-iff-edge-is-separable
kind: claim
title: A centralizing HNN extension of a residually finite base is residually finite exactly when its edge subgroup is separable
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that is the instance where the base is free and the edge is spanned by conjugates of one generator, where the closure is computed explicitly; this is the general theorem, whose content is the equivalence itself rather than any closure computation.
  shift-raag-family-is-rf-iff-symmetrized-index-set-closed: that is the two-generator instance inside a right-angled Artin group; this is the general statement it specializes.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that is about finite models for soficity and shows the quotient route is equivalent to separability; this is the exact residual-finiteness statement, where separability is not merely necessary for the method but for the conclusion.
---

ESTABLISHED.  Let `K` be a residually finite group, `L <= K` a subgroup,
and

```text
Gamma = < K, v | [v, L] = 1 > = K *_L (L x Z).
```

Then

```text
Gamma is residually finite   iff   L is closed in the profinite topology of K.  (CS1)
```

Both instances proved earlier are special cases: the conjugate-basis
family [[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]]
and the two-generator shift family
[[shift-raag-family-is-rf-iff-symmetrized-index-set-closed]], where the
closure of the edge is computed explicitly and the criterion becomes a
statement about an index set.  Combined with the `Pi^0_3`-completeness of
profinite closedness ([[index-set-profinitely-closed-is-pi3-complete]]),
this is why residual finiteness sits one level above the approximation
properties.

**Consequences.**

* Taking `L` to be a Mikhailova subgroup of `K = F x F` (finitely
  generated, with undecidable membership, hence non-separable) gives a
  finitely presented non-residually-finite group whose base is a product
  of free groups --- the shape used by the MF-safe compiler.
* Residual finiteness of centralizing HNN extensions is exactly as hard as
  subgroup separability in the base, so no permanence theorem can do
  better than the separability hypothesis.
