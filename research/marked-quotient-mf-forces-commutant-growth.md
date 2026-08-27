---
rg: 2
id: marked-quotient-mf-forces-commutant-growth
kind: claim
title: MF of either marked quotient forces operator-norm commutant growth
distinct_from:
  corona-commutant-no-growth: That open claim asserts growth never happens; this proved claim says growth is necessary for either quotient to be MF, so the two together make the open claim an exact hinge rather than one implication.
  commutant-no-growth: That is the finite-dimensional collapse; this is a necessity statement about corona representations, with no finiteness hypothesis.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Let `Theta` be a corona representation of `W/<zeta>` or of `E/<w>` that is
injective, and put `C = Theta(Gbar)' cap Q`.  Then

```text
C  strictly contained in  Theta(tau) C Theta(tau)^*  =  Theta(abar(Gbar))' cap Q ,
```

witnessed by the single lamp `Theta(c_{tau o})`.

So `corona-commutant-no-growth` is not merely sufficient to refute the two
open quotient claims: its negation is *necessary* for either of them.  Any
proof that either quotient is MF must exhibit a corona representation whose
relative commutant grows under the compression, and the growth is realized by
a lamp, not by an exotic operator.
