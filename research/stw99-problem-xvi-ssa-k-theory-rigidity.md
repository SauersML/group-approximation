---
rg: 2
id: stw99-problem-xvi-ssa-k-theory-rigidity
kind: claim
title: Ordered K-theory determines embeddable strongly self-absorbing algebras (STW Problem XVI)
root: true
distinct_from:
  stw99-problem-xv-ssa-k-theory-range: that asks the K-theory to be of known type; this asks the stronger rigidity that matching ordered K-theory with a known SSA algebra forces isomorphism.
artifacts:
  - research/artifacts/stw99-master-ledger-2026-08-30.md
---

**Problem XVI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  If
a strongly self-absorbing `D` is `(Q ⊗ O_∞)_ω`-embeddable (or even
quasidiagonal) and has the same ordered `K`-theory as a known
strongly self-absorbing `E`, must `D ≅ E`?

## Attempts

* Implied by XIII.  The UCT-free content: classification of SSA
  algebras by ordered K-theory WITHOUT assuming they are classifiable
  — the natural attack is one-sided intertwining: known `E` are
  inductive limits with excellent existence theorems, so a unital map
  `E → D` exists whenever `D`'s invariant receives `E`'s
  (self-absorption gives approximate divisibility of everything in
  sight), and `D ⊗ E ≅ D` then needs only `E`-absorption of `D`:
  i.e. XVI reduces for each fixed known `E` to "`K`-compatible SSA
  `D` is `E`-absorbing", which for `E = Z` is automatic
  (Winter: SSA implies `Z`-stable for `D ≠` matrix... all
  infinite-dimensional SSA are `Z`-stable — Winter's theorem), for
  `E` UHF is the `M_{p^∞}`-absorption question decided by
  `K_0(D)`-divisibility plus quasidiagonality (embeddability),
  and for `E = O_∞` by tracelessness.  Recorded: XVI is equivalent
  to the family of absorption statements "`K_0`-divisibility ⟹
  UHF-absorption" for embeddable SSA algebras — a McDuff-type
  transfer with no UCT content, plausibly the easiest of the SSA
  cluster.
