---
rg: 2
id: property-t-trace-envelope-has-rigid-coequalizers
kind: claim
title: A property-T interface extends the chosen trace, but its faithful coequalizers are rigid
distinct_from:
  trace-extending-bcs-to-lcs-maps-are-already-terminal: that identifies a trace-extending BCS-to-LCS arrow as the final theorem; this constructs a genuine property-T trace envelope and proves that quotienting it cannot supply that arrow after GNS reduction.
  non-ce-property-t-equivalence-relation-exists: that embeds a non-CE algebra into a property-T relation factor; this is a C-star crossed-product statement with explicit unital maps and an exact quotient/coequalizer obstruction.
  standard-character-envelopes-do-not-supply-signed-bcs-quotient: that audits particular group-character envelopes; this gives a general faithful-trace theorem for every quotient or coequalizer.
---

**ESTABLISHED PROPERTY-T FIREWALL.** Let `A_B` be the unital C-star
algebra of a finite BCS and let `tau` be a specified non-Connes-embeddable
tracial state. Let a discrete group `Gamma` act on `A_B` by
`tau`-preserving automorphisms. Then the reduced crossed product

```text
B_r=A_B crossed-product_(alpha,r) Gamma                 (PTE1)
```

has a canonical unital inclusion `i:A_B->B_r` and the trace

```text
tau_r=tau after E,                                      (PTE2)
```

where `E:B_r->A_B` is the coefficient-at-the-identity conditional
expectation. It satisfies

```text
tau_r after i=tau.                                      (PTE3)
```

The trace `tau_r` is non-CE. If `A_B` admits no unital
star-homomorphism to `R^U`, then neither does `B_r).

This gives an entirely explicit nonamenable property-`(T)` interface:
take `Gamma=SL_3(Z)` with the trivial action. Then

```text
B_r=A_B tensor_min C*_r(SL_3(Z)),                       (PTE4)
```

and the group unitaries commute with the BCS copy and satisfy a finite
presentation of `SL_3(Z)`. Thus property `(T)` creates no
trace-extension problem.

It also creates no quotient solution to the BCS-to-LCS problem. Replace
`A_B` by its trace-GNS image so that `tau` is faithful. Then
`tau_r` is faithful, and every unital quotient

```text
q:B_r->D
```

which carries the specified trace, meaning that some trace `sigma` on
`D` obeys

```text
tau_r=sigma after q,                                    (PTE5)
```

is an isomorphism. More generally, a trace-preserving C-star coequalizer
of two arrows into `B_r` is nontrivial only if the two arrows were
already equal.

Consequently, if `D` in (PTE5) is the solution algebra of a finite LCS,
then `B_r` was already isomorphic to that LCS algebra. A proper
trace-preserving quotient cannot linearize even one trace-visible BCS
relation.

For the full crossed product `B_u`, the only possible quotient kernel is
contained in the null ideal of its canonical trace. Equivalently, every
trace-preserving quotient of `B_u` has trace-GNS algebra exactly `B_r`.
Thus passing from full to reduced may discard a trace-invisible universal
kernel, but no further coequalizer can alter the represented BCS algebra.

This is a sharp no-go for the proposed property-`(T))
quotient/coequalizer route, not a no-go for all LCS embeddings. A unital
map from this envelope into an LCS algebra carrying an extending trace
would still be the terminal BCS-to-LCS theorem. The abstract group
interface supplies rigidity and the trace; it does not convert the
non-binomial BCS ideal into solution-group relators.

DERIVATION
crossed-product-trace-and-coequalizer-rigidity-proof
