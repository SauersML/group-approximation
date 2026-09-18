---
rg: 2
id: capacity-chain-presentation-is-not-simple
kind: claim
title: The finite presentation of the capacity-chain ring has a bi-infinite chain module, so the presented ring is not simple
distinct_from:
  capacity-chain-resolvent-ring-has-rational-k0: that is the candidate, claiming the presented ring is simple; this refutes it.
  resolvent-vacuum-rings-have-no-k0-state: that is an obstruction on K_0 for any resolvent-vacuum ring; this is an obstruction on one finite presentation, from hidden positivity identities.
---

**ESTABLISHED** through `capacity-chain-presentation-is-not-simple-proof` (lane proof, not
independently reviewed; referee requests sent).

**Statement.** Let `R_abs` be the ring presented by the finitely many relations (CK),
(Avail), (Cov), (Pos) of `capacity-chain-resolvent-ring-has-rational-k0`, with or without
the letter `a_u`. Let `R_conc` be its image in the concrete model on legal words with tail
`b^∞`. Then:
1. for every `k >= 1` the element `X_k = [L = k]·(1 − Σ_(i=0)^k [Δ = i])` of `R_abs` is
   nonzero, but it is `0` in `R_conc`;
2. hence `ker(R_abs -> R_conc)` is a nonzero proper ideal, and `R_abs` is not simple.

The same holds for the variant without `a_u`. The letter `a_u` transports (Pos) only to
the `a_u`-part of each level. On the `c`-part the defect satisfies `X_k = s_c X_k t_c`, and
nothing in the relations forces a `c`-invariant element of `B` to vanish.

**Lesson.** The multiplicity `k+1` needs a comparison `j <= L` between two unbounded
registers. In the concrete base this creates hidden positivity identities: products of
level idempotents with capacity idempotents that vanish on the reachable set but not
generically.
- Finitely many polynomial and idempotent relations cannot enforce integrality of `Δ`.
- The bi-infinite chains below satisfy every such relation.
- With one unbounded register there are no hidden identities: a nonzero function of one
  register cannot vanish on all of `Z_(>=0)`. But then the multiplicities are bounded, and
  the heuristic `K_0` is periodic, not divisible.

So a host for `fp-simple-resolvent-ring-with-divisible-unit-class` must get its unbounded
multiplicities without an inequality between unbounded registers, or must encode
well-foundedness noncommutatively.
