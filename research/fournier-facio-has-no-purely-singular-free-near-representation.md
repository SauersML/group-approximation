---
rg: 2
id: fournier-facio-has-no-purely-singular-free-near-representation
kind: claim
title: The Fournier--Facio group has no purely singular essentially free amenable near representation
distinct_from:
  fournier-facio-purely-singular-free-near-representation: That is the positive branch and is exactly the negation of this claim.
  near-representation-amenability-dichotomy: That asks for a general charge-visible Kazhdan theorem; this asks only for exclusion of the canonical witness for one explicit group.
---

There do not exist `H`, a purely singular invariant state `phi` on `B(H)`,
and a `phi`-near representation `pi:G -> U(H)` in the Kahl--Schneider state
sense with

```text
phi(pi(g))=0                    for every g != 1.
```

By `fournier-facio-hyperlinear-iff-singular-near`, this is the negative
hyperlinearity branch for the explicit finitely presented torsion-free
Fournier--Facio group.

## Attempts

Because `G` is non-residually-finite and Kazhdan, the established
`non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` theorem would prove this claim
from weak ucp-stability (or from LLP of the full group C-star algebra).  No
such stability or LLP theorem is known for this group.  Its operator-norm and
unnormalized-Frobenius stability do not imply weak ucp-stability, and the
compression defect alone is trace-blind in normalized HS.  Thus the direct
attack is deferred to a genuinely normalized-HS/ucp argument.

**One compressor reduces to `Gamma` (2026-09-11).**
`fournier-facio-one-compressor-subgroup-reduces-to-gamma` puts the whole
compression triple into `<Gamma, t_1>`: `J`, every `J_k`, `S wr Z`, and the
proper commutant shift of `fournier-facio-regular-models-carry-commutant-shift`.
That subgroup has no property (T) and is hyperlinear exactly when `Gamma` is.
So an obstruction using one compressor and not property (T) of `G` proves the
stronger `fournier-facio-compression-subgroup-not-hyperlinear`, and the route
through it is `fournier-facio-no-go-via-compression-subgroup`.  A no-go that
does not pass through `Gamma` must spend property (T) of `G` on both
compressors.  In OpenAI's permutation proof that is the median size-matching
step, which needs a component-size function monotone along the compressors.
In normalized HS the missing object is a finite-level positive element of the
approximate `Gamma`-commutant that is almost monotone under `Ad pi(t_i)^*` and
encodes a component frame.  The charged-basis fences already forbid taking it
from a normalized basis.  Details:
`research/artifacts/fournier-facio-one-compressor-reduction-2026-09-11.md`.
