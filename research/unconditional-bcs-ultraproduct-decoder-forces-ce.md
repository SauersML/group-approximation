---
rg: 2
id: unconditional-bcs-ultraproduct-decoder-forces-ce
kind: claim
title: An unconditional group-to-BCS matrix-ultraproduct decoder forces a Connes-embeddable BCS trace
distinct_from:
  trace-functorial-bcs-signal-groupification-impossible: that uses the regular trace to rule out a marked lower bound functorial on all tracial group representations; this uses the trivial group homomorphism and already rules out unconditional decoding only on tracial matrix ultraproducts.
  fanizza-native-signal-ultraproduct-groupification: that needs mark death only on NONHALT instances; this shows its decoder must be mark-relative or must come with a proved mark-dead Connes-embeddable base representation of every source BCS.
  non-ce-trace-on-sofic-racg: that pulls one non-CE trace back to a sofic group; this rules out reconstructing a BCS with no CE trace from every homomorphism of any group.
---

Let `B` be a unital star-algebra.  Suppose a group `Gamma` has the following
unconditional decoder property:

```text
for every tracial matrix ultraproduct M and every homomorphism
rho: Gamma -> U(M),
the tuple Dec(rho) is a unital star-representation B -> M              (UCD1)
```

(allowing a nonzero corner or a fixed matrix amplification of `M` makes no
difference).  Then `B` has a Connes-embeddable tracial state.

Consequently no BCS algebra with no Connes-embeddable trace can admit such a
group envelope.  This remains true if an exact non-CE tracial representation
of `B` induces a representation of `Gamma` preserving a native marked
involution: exact completeness does not repair the unconditional decoder.

## Proof

Choose any nonzero tracial matrix ultraproduct `M`.  Every group has the
trivial homomorphism

```text
rho_0(g)=1  for every g in Gamma.                                  (UCD2)
```

Apply `(UCD1)` to `rho_0`.  The normalized trace of `M`, composed with the
unital representation `Dec(rho_0):B->M`, is a tracial state on `B` realized
in a tracial matrix ultraproduct.  It is Connes embeddable.

If the decoder lands in a nonzero corner `pMp`, use its normalized corner
trace.  If it lands in `M_k(M)`, use the amplified normalized trace.  Thus
neither standard block-unitary dilation convention changes the conclusion.

## Correct interface for reverse Kleene

The viable statement is necessarily **mark-relative**.  For a BCS mark
`d=(1-x_D)/2` and group word `w`, one may ask that:

```text
rho(w) != 1  => Dec(rho) exists and Dec(rho)(d) != 0,              (UCD3)
```

or more generally that a decoded representation always exists only after a
nonzero marked-corner extraction.  The trivial homomorphism then has zero
marked corner and creates no BCS trace.

An alternative is to prove uniformly that every source BCS has a specified
Connes-embeddable mark-dead representation and let `(UCD2)` decode to it.
That extra basepoint is a real compiler obligation; it is not supplied merely
by an exact mark-alive tracial witness.

For `fanizza-native-signal-ultraproduct-groupification`, the needed semantic
coupling is therefore not just “every group homomorphism yields some BCS
tuple.”  It must ensure that survival of the group word forces survival of
the native BCS mark in the decoded tuple.
