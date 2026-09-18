---
rg: 2
id: a5-arithmetic-shell-envelope-is-not-finitely-presented
kind: claim
title: The specified bijective-base A5 free-product shell envelope is not finitely presented
distinct_from:
  a5-arithmetic-shell-envelope-is-finitely-presented: that is the OPEN positive benchmark assertion for the same group; this is its negation and refutes it.
  arithmetic-a5-near-group-is-not-finitely-presented: that kills R_nu, Q and A_1 for this enumeration and says it "does not decide" the envelope; this decides the envelope, using the new necessity theorem.
  a5-arithmetic-shell-envelope-embeds-in-fp-simple-group: that gives a finitely presented simple overgroup of this envelope, which remains valid; this says the envelope itself is not finitely presented.
artifacts:
  - research/artifacts/shell-envelope-germ-necessity-2026-09-18.md
---

**ESTABLISHED** by `a5-arithmetic-shell-envelope-not-fp-proof` (written proof,
not independently reviewed).

Let nu be the bijective-base enumeration of P = A_5*A_5 from
`a5-free-product-has-simple-arithmetic-shell-envelope`. Then the simple,
finitely generated, decidable shell envelope E_nu is NOT finitely presented.

This refutes the OPEN benchmark `a5-arithmetic-shell-envelope-is-finitely-presented`.
The imported near-group proof says it applies verbatim to A*A for finite A with
|A| >= 4; for those enumerations the same one-line argument applies, but only the
A_5 case is claimed here.

Consequence. The only explicit perfect candidate in the graph for the envelope
route is dead. A successful enumeration for
`perfect-decidable-inputs-have-fp-shell-envelopes` or
`decidable-inputs-have-fp-shell-envelopes` must avoid near groups that act on a
tree with locally virtually abelian vertex stabilizers and contain Z^infinity.
The finitely presented simple overgroup of
`a5-arithmetic-shell-envelope-embeds-in-fp-simple-group` is unaffected.
