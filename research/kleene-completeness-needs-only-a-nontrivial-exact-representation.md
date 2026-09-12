---
rg: 2
id: kleene-completeness-needs-only-a-nontrivial-exact-representation
kind: claim
title: Kleene completeness may use a properly infinite exact witness while soundness remains matrix-only
distinct_from:
  kleene-self-destroying-microstate-lemma: that consumes the algebraic conclusion that the marked word is nontrivial; this weakens the upstream way of proving that conclusion to one arbitrary exact unitary representation.
  regular-trace-blocks-exact-local-predicate-return: that forbids a universal tracial return law by applying it to the regular representation; this permits representation-specific infinite multiplicity only for completeness and asserts no such trace law.
  finite-packet-cannot-realize-absorbing-contraction: that refutes a contraction theorem certified entirely by a finite packet character table; this allows the exact witness to absorb branching through infinite cardinal multiplicity while requiring a separate finite-matrix quantitative theorem.
---

In a machine-indexed presentation `Gamma_M=<S_M|R_M>` with marked word
`w_M`, the completeness input needed by
`kleene-self-destroying-microstate-lemma` is only

```text
w_M != 1 in Gamma_M.                                      (PIC1)
```

It is sufficient to prove `(PIC1)` by exhibiting **any** exact unitary
representation

```text
pi_M:Gamma_M -> U(H_M),       pi_M(w_M)!=I.                (PIC2)
```

The Hilbert space in `(PIC2)` need not be finite-dimensional, tracial, or a
finite-factor standard form.  In particular its multiplicity spaces may be
properly infinite and may absorb a branching equation such as

```text
H_M ~= H_M directSum H_M.                                  (PIC3)
```

This does not weaken the finite-matrix soundness obligation.  Soundness must
still say that sufficiently accurate finite-dimensional tuples collapse the
mark below a fixed cutoff.  Combining `(PIC2)` with that matrix-only theorem
is legitimate: `(PIC2)` proves algebraic nontriviality, whereas finite-matrix
soundness excludes the microstates that hyperlinearity would require.

There is an essential scope distinction.  `(PIC3)` may be a statement about
the multiplicity decomposition of the chosen representation.  It may **not**
be promoted to a universal group-algebra proper-isometry identity or an exact
trace inequality.  Such an identity would also hold in the left regular
representation, whose canonical finite trace triggers
`regular-trace-blocks-exact-local-predicate-return`.  Thus the live
Toeplitz/Cuntz-style design has two deliberately asymmetric halves:

1. one exact, possibly properly infinite representation proving the mark
   survives; and
2. a finite-dimensional-only rank or HS-loss theorem derived from the group
   relations, with no claim that the same inequality holds in every tracial
   representation.

This relaxation removes any requirement that a groupifier preserve a
particular tracial BCS state on the completeness side.  It does not by itself
construct the unitary-word corner compressor or its robust finite-matrix
loss estimate.
