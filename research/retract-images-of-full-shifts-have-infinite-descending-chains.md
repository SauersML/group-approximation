---
rg: 2
id: retract-images-of-full-shifts-have-infinite-descending-chains
kind: claim
title: On every infinite group the retract images of a full shift contain an infinite strictly descending chain
distinct_from:
  surjunctivity-iff-automaton-monoid-directly-finite: that node's descending images tau^n(A^G) exist only for a strict automaton; these chains of retract images exist on every infinite group, surjunctive or not, so chain height can never serve as the size that drops.
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Let `G` be an infinite group and `A` a finite alphabet with `|A| >= 2`. Call a subshift of `A^G` a
*retract image* when it is the image of an idempotent cellular automaton.

For finite `F` containing `1`, the opening `gamma_F(S) = ⋃ { gF : gF <= S }` of the support is an
idempotent automaton with memory `F^-1 F`. With `F_0 = {1}`, `F_(n+1) = F_n ∪ c_n F_n` and
`c_n notin F_n F_n^-1`, the images `X_(F_n)` form a strictly descending chain of retract images of
`A^G`, all containing the constant configurations `0` and `1`.

Consequences:
- No function from retract images to a well-ordered set is strictly monotone along proper inclusions.
  So chain heights and well-founded ranks of retract images are infinite at `A^G` on every infinite
  group, including `Z` and every amenable group.
- Such sizes cannot supply the drop on proper retracts that
  `surjunctivity-iff-automaton-monoid-directly-finite` asks for, on any host.
- Real-valued sizes survive this: over amenable groups topological entropy is one, but it is built
  from Følner sets.

Proof: artifact Section 1, route `retract-image-descending-chains-proof`.
