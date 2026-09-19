---
rg: 2
id: stw10-finite-crossed-products-preserve-amenable-and-qd-traces
kind: claim
title: Finite crossed products preserve and reflect amenability and quasidiagonality of canonical traces
distinct_from:
  stw08-finite-group-crossed-products-preserve-af-embeddability: that transports a pre-existing AF embedding of the algebra and, in its traced version, a trace extending across that embedding; this directly transports the two finite-dimensional approximation properties of one invariant trace and assumes no AF model.
  directed-unions-preserve-trace-approximations: that is locality under dense inclusions; this is permanence across a finite crossed product and uses the regular covariant matrix representation.
  stw10-factorialize-amenable-nonqd-witnesses: that reduces hypothetical counterexamples to factorial traces; this proves a positive permanence theorem and a new Rokhlin crossed-product class.
---

Let a finite group `G` act on a unital C\*-algebra `A`, let `tau` be a
`G`-invariant tracial state, let

```text
B=A rtimes G,
sigma=tau compose E:B->C,
```

where `E:B->A` is the coefficient expectation.  Then

```text
tau is amenable       iff sigma is amenable,
tau is quasidiagonal  iff sigma is quasidiagonal.             (1)
```

Consequently, if every amenable trace on `A` is quasidiagonal, then every
amenable canonical trace `tau compose E` on `A rtimes G` is quasidiagonal.

If the action has the Rokhlin property, every tracial state on `A rtimes G`
is canonical.  Hence in this case

```text
all amenable traces on A are QD
    implies
all amenable traces on A rtimes G are QD.                      (2)
```

No exactness, nuclearity, UCT assumption, or faithfulness of the trace is
required.
