---
rg: 2
id: exact-gns-kernel-amenability-reduction-proof
kind: route
title: Locally lift the exact GNS quotient and pull QD maps back by composition
target: exact-gns-kernel-amenability-reduction
requires:
  - amenable-trace-descends-through-locally-liftable-quotient
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Exactness passes from `A` to its ideal `J` and quotient `A/J`, and exact
C*-algebras are locally reflexive.  The Effros--Haagerup local-lifting theorem
for an exact sequence then makes the quotient map

```text
q:A -> A/J
```

locally liftable.  Since `tau=bar_tau o q`, the amenable-trace descent theorem
gives the forward implication in (1).  The reverse implication is immediate:
compose amenability u.c.p. maps for `bar_tau` with the *-homomorphism `q`.

The identical composition argument works in operator norm: if
`psi_n:A/J -> M_{k(n)}` witness that `bar_tau` is QD, then `psi_n o q` witness
that `tau` is QD.  Combining this with (1) proves the reduction.

**Trust boundary.**  Exactness/local reflexivity and the Effros--Haagerup
local-lifting theorem are imported, as is the prerequisite amenable-descent
lemma.  The pullback implications are direct compositions.  In particular,
the proof never tries to descend norm-multiplicative maps through `q`.
