---
rg: 2
id: stw99-xcix-raw-transport-iteration
kind: claim
title: Alternating raw embedding transport has a noncontractive certified error recurrence
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
---

Let `d(A,B)<gamma`, where `0<gamma<1/12600000`, and let `D` be strongly
self-absorbing.  Fix finite `Y` in the unit ball of `D` and paired finite
families `(a_i)` in the unit ball of `A` and `(b_i)` in the unit ball of `B`
such that `||a_i-b_i||<gamma` for every `i`.  Start with an embedding
`psi_0:D -> A`, and alternately apply Christensen--Sinclair--Smith--White--
Winter, Corollary 4.7, across `A subset_gamma B` and
`B subset_gamma A`.  The embeddings can be chosen so that

```text
||psi_(j+1)(y)-psi_j(y)|| < 152 sqrt(gamma)    (y in Y).
```

If `e_j` denotes the maximum commutator norm against `(a_i)` on even steps
and against `(b_i)` on odd steps, then, with

```text
Delta = 304 sqrt(gamma) + 2 gamma,
```

one has for every number of transport legs `n`

```text
e_(j+1) < e_j + Delta,
e_n     < e_0 + n Delta.
```

Consequently the norm estimate furnished by raw alternating transport is
not an error-improvement iteration: its affine update has coefficient one,
not a coefficient below one.  Both commutator Lipschitz constants `2` used
to obtain `Delta` are sharp for arbitrary contraction perturbations.  This
statement concerns exactly what follows from the transport proximity bound
and triangle inequalities; it does not say that the embeddings cannot be
chosen more centrally by an argument using additional structure of `D`.
