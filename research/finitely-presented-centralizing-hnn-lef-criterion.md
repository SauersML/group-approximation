---
rg: 2
id: finitely-presented-centralizing-hnn-lef-criterion
kind: claim
title: A finitely presented centralizing HNN extension is LEF exactly when its edge is profinitely closed
distinct_from:
  centralizing-hnn-is-residually-finite-iff-edge-is-separable: that is the residual-finiteness theorem for an arbitrary edge in a residually finite base; this identifies the LEF boundary when finite presentability turns local finite models into genuine finite quotients.
  centralizing-hnn-over-conjugate-basis-is-always-lef: that family permits infinitely generated edges and generally infinitely presented HNN groups, so it can be LEF without being residually finite; finite generation of the edge is load-bearing here.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that analyzes approximate permutation models and leaves genuinely non-quotient sofic models alive; this rules out exact local embeddings only and makes no nonsoficity assertion.
---

ESTABLISHED.  Let `K` be a finitely presented residually finite group,
let `L <= K` be finitely generated, and put

```text
Gamma = < K, v | [v,L]=1 > = K *_L (L x Z).                 (LHC1)
```

Then

```text
Gamma is LEF
  iff Gamma is residually finite
  iff L is closed in the profinite topology of K.           (LHC2)
```

The first equivalence is special to the finite-presentation regime.  The
display `(LHC1)` is finitely presented because `K` is finitely presented and
commuting `v` with a finite generating set of `L` implies that it commutes
with all of `L`.  Every residually finite group is LEF.  Conversely every
finitely presented LEF group is residually finite: put the generators, the
relator-prefix products and the prefixes of a chosen nontrivial word into one
LEF window.  A local embedding of that window into a finite group sends the
generators to a tuple satisfying every defining relator and hence extends to
a genuine homomorphism of the presented group; injectivity on the word and
the identity makes the word survive.  The second equivalence is
[[centralizing-hnn-is-residually-finite-iff-edge-is-separable]].

Thus a finitely generated nonseparable edge does more than defeat quotient
models for a proposed proof: it forbids **every** exact finite local model of
the centralizing HNN extension.  Approximate Hamming models can still exist,
so `(LHC2)` does not decide soficity.

DERIVATION
[[finitely-presented-centralizing-hnn-lef-criterion-proof]]
