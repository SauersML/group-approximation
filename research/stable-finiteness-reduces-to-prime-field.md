---
rg: 2
id: stable-finiteness-reduces-to-prime-field
kind: claim
title: Kaplansky stable finiteness over every field reduces to the prime fields
distinct_from:
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that is an imported computer-assisted result bounding the supports of a witness over `F_2`; this is a coefficient-field reduction, holds for every group with no support restriction, and is what says the `F_2` restriction costs nothing.
  leavitt-group-algebra-not-stably-finite: that asks for an explicit one-sided inverse pair over `F_2` for one group; this fixes which coefficient fields any such search has to cover, for every group at once.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
  - c1168433:official/counterexample.tex
---

For every group `Gamma`:

1. `F[Gamma]` is stably finite for every field `F` of characteristic `0`, and
   `Z[Gamma]` is stably finite;
2. for every prime `p` and every field `F` of characteristic `p`,
   `F[Gamma]` is stably finite **iff** `F_p[Gamma]` is stably finite.

Hence Kaplansky's stable finiteness conjecture for `Gamma` over *all* fields
is equivalent to the conjecture over the prime fields `F_p` alone, and a
counterexample over any field of characteristic `p` yields one over `F_p`.

Imported from H. Bradford and F. Fournier-Facio, *Hopfian wreath products and
the stable finiteness conjecture*, Math. Z. 308 (2024), art. 58,
arXiv:2211.01510: their Theorem 3.4 and Corollary 3.5 are (1), their
Corollary 3.15 is (2).  Part (1) is classical, Kaplansky's own; the trace
argument through the group von Neumann algebra is standard and is rehearsed
in the audit artifact.

## Why the graph wants this stated

Two uses, both operational.

*The search may stay over the prime field.*  The witness lane for the
Leavitt unit group works over `F_2` throughout
(`leavitt-group-algebra-not-stably-finite`,
`left-invertible-lift-of-s0-in-leavitt-group-algebra`,
`dykema-heister-juschenko-bounded-rank-direct-finiteness`).  Part (2) says
this is not a convenience: enlarging the coefficient field can never produce
a witness that `F_2` does not already have, so a negative search over `F_2`
is a negative search over every field of characteristic two, and a positive
one settles the whole characteristic.

*Only positive characteristic is open, and only for prime fields.*  Part (1)
rules out any characteristic-zero counterexample for **every** group, so no
construction — Leavitt, Kun--Thom, or otherwise — can produce one.  Anything
claiming a characteristic-zero Kaplansky counterexample is wrong before it is
read.

A weaker form of (2), reducing only to *some* finite field of characteristic
`p` by a Nullstellensatz argument, is re-derived independently in the audit
artifact; it is recorded there because it makes (2) checkable without reading
the source paper's proof.
