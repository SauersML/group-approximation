---
rg: 2
id: culf-mastel-one3-central-tagged-perfect-gap-family
kind: claim
title: Preserve the Culf--Mastel perfect gap while globally centralizing one tag per ONE3 clause
distinct_from:
  culf-mastel-rstar-halt-model-has-fano-cap-support: that seeks affine-safe supports after a one-ghost reduction; this uses a different fixed NP-hard language whose two fibers are affine and asks for a central selector invariant.
  perfect-completeness-constant-soundness-lcs-compiler: that allows any LCS compiler; this isolates the sole completeness condition after the central ONE3 profile decomposition.
---

OPEN.
Use Culf--Mastel's fixed-language theorem for positive one-in-three and choose
one designated coordinate `t_c` in every output clause.  Add fixed-language
commutativity gadgets making `t_c` commute with every variable, with:

```text
HALT:    some perfect CE model survives all added gadgets,
NONHALT: the original constant matrix/CE soundness gap is retained.       (C13)
```

The NONHALT direction is monotone at exact soundness and quantitative under
the published bounded-cost gadget maps.  The HALT direction is the gap: a
generic oracular strategy makes variables commute only inside a queried
context.  It need not make one existing coordinate of every clause commute
with the entire instance, and adding those empty-context requirements can
destroy perfect completeness.

## Attempts

- Choosing a different irreducible block does not centralize a noncentral
  clause observable; irreducibility makes genuinely central observables
  scalar but does not enlarge the center.
- Replacing `t_c` by a fresh central selector loses the equation connecting
  the selector to which ONE3 affine fiber contains the payload.  Enforcing
  that connection is the original nonlinear predicate.
- Culf--Mastel's ONE3 commutativity gadget exactly implements an empty
  context only when the two visible observables are intended to commute in
  the completeness model.  Its existence does not prove the new global
  commutations in `(C13)`.
- A constraintwise classical lift cannot make all designated tags scalar on
  a full nonaffine source support.  By
  `central-one3-tag-sections-force-source-affine-safety`, the selected affine
  fibers would give an affine relation sandwiched between that support and
  the source predicate.  Thus the positive route must again exploit a proper
  affine-safe HALT support or global contextual structure.

If `(C13)` is established, no support selection remains:
`central-tagged-one-in-three-is-a-finite-lcs-or` decomposes every exact model
into finitely many affine profile sectors.
