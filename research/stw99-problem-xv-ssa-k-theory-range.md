---
rg: 2
id: stw99-problem-xv-ssa-k-theory-range
kind: claim
title: Embeddable strongly self-absorbing algebras have known K-theory (STW Problem XV)
root: true
distinct_from:
  stw99-problem-xiii-ssa-uct: that asks for the full UCT identification; this asks only that the K-groups match a known strongly self-absorbing algebra, for the (Q tensor O-infinity)-omega-embeddable ones.
artifacts:
  - research/artifacts/stw99-master-ledger-2026-08-30.md
---

**Problem XV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Must a strongly self-absorbing `D` which embeds into
`(Q ⊗ O_∞)_ω` have the same `K`-theory as a known strongly
self-absorbing algebra?

## Attempts

* Implied by XIII (route `stw99-xiii-implies-xv`).  Unconditionally:
  the KK-ring structure forces `K_0(D)` to be a unital commutative
  ring, `[1_D]` idempotent-generating, and `K_0(D) ⊗ K_0(D) → K_0(D)`
  surjective-ish by self-absorption; the known possible rings
  (`Z`, `Z[1/n]`-types, `Q`, `0`-augmented torsion patterns of
  `O_{n+1}`... which are excluded here by `(Q⊗O_∞)_ω`-embeddability
  killing torsion against `Q`) — the recorded sharp subproblem:
  show `K_0(D)` is a localization of `Z` and `K_1(D) = 0`.  The
  `K_1 = 0` half may be accessible: a nonzero `K_1` class of an SSA
  algebra squares to a `K_0 ⊗ K_1`-graded piece under the
  self-absorption isomorphism, and graded-commutativity plus
  idempotence of the flip on `K_1(D ⊗ D)` is a finite computation in
  the Künneth range — flagged as the plausibly closable fragment
  (under the Künneth formula, available here since embeddability
  gives... Künneth needs UCT-free input, so state it as: `K_1 = 0`
  follows whenever `D` satisfies the Künneth formula, which is
  Problem IV's territory).
