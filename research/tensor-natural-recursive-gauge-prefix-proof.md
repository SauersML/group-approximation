---
rg: 2
id: tensor-natural-recursive-gauge-prefix-proof
kind: route
title: Iterate the tensor extension and multiply the independent carrier traces
target: recursive-gauge-verifier-has-product-density-escape
requires:
  - exact-code-prefixes-have-matrix-ultraproduct-model
---

Start from an exact finite-dimensional seed model `U^(0)` with

```text
||w(U^(0))-1||_2 >= beta>0.
```

Iterate the assumed extension operation.  At depth `N` the carrier is
`H_0 tensor V^(tensor N)`.  Exactness is preserved by hypothesis, while
`(TRG1)` and invariance of normalized trace under tensoring with an identity
give

```text
||w(U^(N))-1||_2
 = ||(w(U^(0))-1) tensor I_(V^(tensor N))||_2
 = ||w(U^(0))-1||_2 >= beta.                            (TRP1)
```

Hence these are exact marked models for all finite prefixes.  Applying
`exact-code-prefixes-have-matrix-ultraproduct-model` gives a representation of
the full recursive relation library in a tracial matrix ultraproduct with the
mark still separated by `beta`.

For the density statement, the level projections lie in different tensor
factors.  They therefore commute and normalized tensor trace factorizes:

```text
tau(e_1 ... e_N)=product_(j=1)^N tau_V(e)=alpha^N.       (TRP2)
```

Replacing a level packet by a simultaneous gauge conjugate replaces `e_j` by
`G_j e G_j^*` in that factor and preserves its trace, exactness, and the same
factorization.  Thus gauge self-reference creates no coherence between the
level carriers.

For `alpha<1`, `(TRP2)` excludes a uniform positive lower bound for their
common meet.  For `alpha=1`, `(TRP1)` is already a zero-relator-energy marked
finite-prefix family, so no positive relator-energy lower bound follows from
repetition.  A union or sum of the local carrier densities does not repair the
argument: it is realized inside these exact models and is not a common
reducing carrier for the simultaneous recursive payload.  This is exactly the
distinction between extensive local mass and bounded-overlap syndrome **energy
payment**.
