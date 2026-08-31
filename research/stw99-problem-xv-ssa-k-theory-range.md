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
  - research/artifacts/stw99-xv-solid-ring-reduction-2026-08-30.md
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
  killing torsion against `Q`) — UPDATE (this session): the invariant side is now
  closed on the torsion-free locus —
  `ssa-kunneth-forces-solid-k-theory` proves `K_1(D) = 0`
  unconditionally (Toms--Winter flip + Winter + Jiang) and, under
  Künneth-against-itself, that `K_0(D)` is a Bousfield--Kan SOLID
  ring; torsion-free solids are exactly the localizations `Z[J^{-1}]`
  realized by the known list, giving the route
  `stw99-iv-implies-xv-torsion-free`.  UPGRADE: the degree-one Künneth
  sequence kills ALL torsion (`K_1(D⊗D) ≅ Tor(K_0,K_0) = 0` via the
  first-factor isomorphism), so the problem is CLOSED IN FULL modulo
  self-Künneth: the K-theory is `(Z[J^{-1}],0)` or `(0,0)`, always
  that of a known algebra; a counterexample must break the Künneth
  sequence for `(D,D)` itself.
