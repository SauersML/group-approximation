---
rg: 2
id: kt-one-compressor-normalizer-split-proof
kind: route
title: Combine the full one-compressor action charts with finitary-extension permanence
target: kt-one-compressor-normalizer-cocycle-splits
requires:
  - kt-one-compressor-full-coset-action-is-sofic
  - sofic-set-action-finitary-extension-is-sofic
  - finitary-extension-ce-iff-action-lifts-to-normalizer
  - kt-finitary-action-is-outer-mod-scalar-core
---

The first prerequisite makes `H_A action Y` sofic.  The group `H_A` is
sofic: its telescope kernel is an increasing union of conjugates of the
residually finite group `Gamma`, and the quotient by that kernel is cyclic.
The finitary-extension theorem therefore gives soficity of

```text
Sym_fin(Y) rtimes H_A.
```

Its left regular representation gives a trace-preserving embedding of its
group von Neumann algebra

```text
L(Sym_fin(Y) rtimes H_A)=R rtimes_(alpha|H_A) H_A
```

into a tracial matrix ultraproduct.  The normalizer criterion supplies the
trace-correct homomorphic lift.  When `q=2`,
`kt-finitary-action-is-outer-mod-scalar-core` says every nonidentity actor
induces an outer automorphism, so the trace condition follows from outerity.
