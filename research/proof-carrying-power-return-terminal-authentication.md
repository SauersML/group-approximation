---
rg: 2
id: proof-carrying-power-return-terminal-authentication
kind: claim
title: A finite cursor machine authenticates every exponent return through one constant-size terminal port
distinct_from:
  conjugacy-addressed-opnorm-challenges-are-lossless: that transports a check already known to be a conjugate of a root relator; this must build the terminal semantic equality to the addressed power.
---

Construct finite syntax which executes repeated squaring for every exponent
`m`, emits a terminal certificate for `w^m`, and makes the discrepancy between
that certificate and an addressed conjugate of `w` a literal conjugate of one
of finitely many root checks.  The certification constant must be independent
of the exponent and execution depth, and an exact infinite model must keep the
cursor nontrivial.

## Attempts

Ordinary derivations through a repeated-squaring circuit have logarithmic but
still unbounded area, which is not enough because the recurrent exponent grows
with matrix dimension.  The deferred attack is a proof-carrying terminal port:
the verifier checks a constant-size authenticated object rather than replaying
the execution.  No such finite group syntax is currently constructed.
