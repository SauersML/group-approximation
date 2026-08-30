---
rg: 2
id: stw99-problem-vi-qd-traces-gtr-one
kind: claim
title: Quasidiagonal traces force generalised tracial rank one for Q-stable algebras (STW Problem VI)
root: true
artifacts:
  - research/artifacts/stw99-master-ledger-2026-08-30.md
---

**Problem VI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  If
`A` is unital simple separable nuclear `Q`-stable stably finite and
every trace on `A` is quasidiagonal, does `A` have generalised tracial
rank at most one?

## Attempts

* Under the UCT this is the Gong--Lin--Niu / classification-era
  theorem (the TAS/TAI characterisation of classifiable `Q`-stable
  algebras with QD traces), so the problem is exactly a UCT-removal
  question: route `stw99-ii-implies-vi`.  Without the UCT the missing
  step is existence of tracially large AI-subalgebras, which the
  classification proof extracts from KK-existence against interval
  building blocks — the same UCT-existence wall as LVII; any
  UCT-free progress on existence theorems (post-Szabo uniqueness)
  hits VI first because `Q`-stability erases all torsion K-data,
  leaving `(K_0 ⊗ Q, traces, pairing)` where the `R^ω`-UCT problem
  (III) is the precise remaining obstruction.  Recorded: VI is
  sandwiched between II and III in strength on its invariant side.
