---
rg: 2
id: linton-radical-has-equivariant-sofic-halo
kind: claim
title: The Linton radical is an equivariant set halo with sofic finite pieces
distinct_from:
  linton-radical-sofic: that asks only whether the abstract radical is sofic; this asks for a functorial finite-support decomposition intertwining the free-shell action, and therefore also controls the action.
  linton-radical-free-action-sofic: that asks directly for automorphic microstates; this asks for a concrete halo structure from which those microstates follow by Alekseev--Bradford.
  linton-radical-abelianization-is-truncated-group-ring: that identifies only the first derived quotient as a finite-lamp module; this demands a nonabelian finite-support model of the full radical, including its perfect derived core.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that constructs compatible finite models after quotienting by R prime; this asks for the exact lift across R prime and cannot be inferred from the quotient.
---

Let

```text
E = R semidirect_alpha F0
```

be the finite rational-derived shell of a one-relator group.  There exist a
countable `F0`-set `X`, a set-theoretic halo functor `L` in the sense of
Alekseev--Bradford, and an isomorphism

```text
theta : L(X) -> R
```

such that:

1. `L(Y)` is sofic for every finite subset `Y` of `X`; and
2. `theta` intertwines the action on `L(X)` induced functorially from
   `F0` acting on `X` with `alpha : F0 -> Aut(R)`.

This is the exact nonabelian finite-support statement that the first-order
Fox--Magnus model does not supply.  Modulo `R'`, the conjugates of the Linton
generator form a finite-lamp module and the analogous assertion is already
implicit in
[[one-relator-fox-magnus-descent-to-derived-linton-radical]].  The present
claim requires the halo intersection and functoriality laws before taking that
quotient; neither follows from the relation-module computation.

The point of naming this stronger structure is that it is one common missing
input rather than two unrelated approximation guesses.  The routes
`linton-halo-gives-radical-sofic` and `linton-halo-gives-action-sofic` prove
that it implies both open prerequisites of
`linton-shell-sofic-via-sofic-action`, and therefore closes the Linton shell.

## Attempts

1. **Use the conjugacy orbit of the Linton generator as the site set.**  This
   is the canonical candidate, but the obvious assignment
   `Y |-> <r^y : y in Y>` has not been shown to satisfy the halo intersection
   law.  More importantly, a bijection of finite site sets need not respect
   the nonabelian relations among the corresponding conjugates, so it does not
   yet define the functor on injections required by Alekseev--Bradford.
2. **Pass to the relation module.**  Modulo `R'` the construction works: the
   site coordinates become the truncated permutation module computed in
   [[linton-radical-abelianization-is-truncated-group-ring]], and the entire
   shell quotient is residually finite.  This cannot establish the present
   claim because the quotient erases exactly the intersection and functoriality
   data of the nonabelian derived core.
3. **Use a graph halo to remember relative positions.**  A Cayley- or
   Schreier-graph halo is a plausible weakening of full set functoriality, but
   the cited action-lifting theorem would then also require a sofic action on
   that graph with the relevant induced-subgraph embeddings.  No such graph
   presentation of the perfect core is currently available, so this remains a
   separate possible refinement rather than part of the stated route.
