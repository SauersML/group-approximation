---
rg: 2
id: fpbs-self-commensurated-positive-farber-gradient
kind: claim
title: Some finitely generated group with isomorphic finite-index subgroups of unequal index has a Farber chain of positive gradient in one of them
distinct_from:
  fpbs-kazhdan-positive-rank-gradient: that asks for positive gradient in a Kazhdan group; this asks for it in a group that is self-commensurated with unequal index, where the second action comes from the index ratio instead of a cheap-action theorem.
  fpbs-positive-gradient-torsion-group-cheap-action: that group has positive infimal rank gradient, which forbids unequal-index self-commensuration; here the infimal gradient is forced to vanish and only a Farber gradient may be positive.
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

**OPEN.** There are a finitely generated group `G`, finite-index subgroups
`H_1 ≅ H_2` with `[G:H_1] != [G:H_2]`, and a Farber chain in `H_1` with
positive rank gradient.

**Necessary invariants.** Every finite multiplicative invariant vanishes:
Euler characteristic, all `l2`-Betti numbers, and the infimal rank gradient.
Covolume rigidity excludes lattices.

## Attempts

* **Known members** (swarm-0917 w5 heretic, 2026-09-17). `Z^d`, `BS(1,n)`, lamplighters and
`Gamma(3) ltimes Z^3` have infinite normal amenable subgroups. That gives
fixed price one, and so zero gradient on every Farber chain.
* **Force maximal cost one by restriction and induction.** This is circular:
  it needs `cost(a x G/H) = cost(a)` for finite extensions, which is open
  (`fpbs-finite-fiber-cost-bound`). See Section 1.1 of the note.

Fixed price predicts that this claim is false.
