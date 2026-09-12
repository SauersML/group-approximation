---
rg: 2
id: maslov-generator-complete-order-model-proof
kind: route
title: Promote generator-system LP through enough unitaries and compare C-star envelopes
target: maslov-generator-complete-order-model-is-llp-strength
requires:
  - deligne-triple-cover-fd-central-invisibility
artifacts:
  - research/artifacts/maslov-generator-operator-system-lp-sources-2026-08-22.md
---

The canonical elements `u_s` are unitaries in `S_alpha` and generate
`A_alpha`.  Hence `S_alpha` contains enough unitaries.  The multiplicative-
domain/enough-unitaries lemma gives

```text
C_e^*(S_alpha)=A_alpha.                                  (MCO3)
```

Suppose now that `S_alpha` has LP.  The operator-system tensor
characterization of LP gives, for every Hilbert space `H`,

```text
S_alpha tensor_min B(H)=S_alpha tensor_max B(H).         (MCO4)
```

The enough-unitaries promotion theorem applies to the inclusion
`S_alpha subset A_alpha`: the identity on `(MCO4)` extends, by the
multiplicative domain of the generating unitaries, to

```text
A_alpha tensor_min B(H)=A_alpha tensor_max B(H).         (MCO5)
```

Kirchberg's tensor characterization identifies `(MCO5)` with LLP of
`A_alpha`.  This proves assertion 2.

The model consequences are formal.  LP is invariant under complete-order
isomorphism, passes from a finite-dimensional LP system to its quotient by a
null subspace, and passes to a ucp retract: if `i:S->T` and `r:T->S` are ucp
with `ri=id`, lift `phi r` on `T` and restrict the lift along `i`.  Finite
coproducts of LP systems again have LP.  Thus every model listed in assertion
3 gives LP of `S_alpha`, and hence `(MCO5)`.

For the direct coproduct obstruction, let

```text
T=T_1 coproduct_1 ... coproduct_1 T_k,
```

where each `T_i` contains its rank-one generating unitary in the cyclic
envelope `B_i`.  The coproduct contains enough unitaries in

```text
B=B_1 *_1 ... *_1 B_k,
```

so `C_e^*(T)=B`.  Choosing compatible scalar characters on the cyclic factors
gives a character of `B`.  The same argument applies along a clique tree when
the clique characters agree on every amalgam.

On the other hand a character of `A_alpha` would be a one-dimensional
projective representation with multiplier `alpha`; equivalently it would
give a one-dimensional representation of the Deligne triple cover on which
the central generator acts by the nontrivial scalar.  This contradicts
`deligne-triple-cover-fd-central-invisibility`.  Complete-order isomorphisms
preserve the C-star envelope, so `(MCO2)` follows.

