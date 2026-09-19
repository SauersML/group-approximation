---
rg: 2
id: perera-rordam-rr0-approximately-divisible
kind: claim
title: Simple nuclear real rank zero algebras are approximately divisible (Perera-Rordam question)
root: true
distinct_from:
  stw27-real-rank-zero-almost-divisibility: that established theorem produces almost divisibility of the CUNTZ SEMIGROUP from real rank zero, a non-central condition; this asks for approximate divisibility, the unital central-sequence embedding of M_n + M_(n+1), which is strictly stronger and is what Z-stability needs without a comparison hypothesis.
  stw99-problem-xxx-rr0-z-stable: that asks for Z-stability; this central-divisibility question is strictly stronger by Toms--Winter (CJM Thm 2.3) and is the form Perera and Rordam posed.
artifacts:
  - research/artifacts/stw99-rr0-cluster-2026-08-30.md
  - research/artifacts/stw30-quantum-expander-centralization-firewall-audit-2026-08-30.md
---

Perera--Rordam (JFA, after Thm 5.8): is every unital simple separable
nuclear non-elementary C\*-algebra of real rank zero approximately
divisible, i.e. does `M_n ⊕ M_{n+1}` embed unitally into
`A_ω ∩ A'` for every `n`?  They prove the NON-central version: every
non-type-I separable RR0 algebra is weakly divisible (`M_n ⊕ M_{n+1}`
embeds unitally into `A` itself, Thm 5.8).

## Attempts

* The gap to close is pure centralization of the weak-divisibility
  embeddings — the same missing glueing as in
  `stw99-problem-xxviii-tracial-divisibility-gamma` (order-zero
  centralization) and `stw99-problem-xxi-tracial-rr0-implies-gamma`
  (projection selection), but here the input is an honest unital
  embedding at every scale and RR0 gives projection-valued spectral
  cutting to move it; no argument converting scale-wise embeddings
  into approximately central ones without a dimension or Γ-type
  hypothesis is known.  STW's warning stands: approximate divisibility
  is a CENTRAL condition, unrelated to the almost-divisibility of the
  Cuntz semigroup discussed at Problem XXVII.
* There is now a sharp abstract no-go for using only that noncentral data.
  A real-rank-zero norm matrix corona contains exact unital
  `M_n direct_sum M_(n+1)` blocks for every `n`, while a fixed finite
  quantum-expander packet has relative commutant containing no unital
  `M_2 direct_sum M_3`
  (`stw30-quantum-expander-weak-divisibility-centralization-no-go`).  Thus
  projection refinement and the existence of blocks do not centralize them,
  even locally against one finite packet.  The countermodel is deliberately
  nonseparable and non-simple and makes no nuclearity assertion, so the
  remaining positive route needs an additional structural or uniform
  selection input beyond weak divisibility; this example does not identify
  which of the missing hypotheses is decisive.
