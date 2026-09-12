---
rg: 2
id: peeling-to-surjunctive-memory-tail-forces-surjectivity-proof
kind: route
title: Peel to the tail, then read it coset by coset over the surjunctive subgroup
target: peeling-to-surjunctive-memory-tail-forces-surjectivity
requires:
  - own-block-local-bijection-rows-peel
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Section 2, Theorem 2.1 of the artifact. Apply `own-block-local-bijection-rows-peel`
down the peeling chain: each corrected tail is injective, and `F` is surjective
iff the final tail `F^{(k)}` is. `F^{(k)}` is a cellular automaton over `G` whose
memory lies in the subgroup `H`. By `surjunctivity-passes-to-subgroups`, such an
automaton acts on each left coset of `H` as a copy of an automaton over `H`, so
it is injective iff its `H`-copy is and surjective iff its `H`-copy is. The
`H`-copy is injective, hence surjective because `H` is surjunctive; therefore
`F^{(k)}` is surjective, and so is `F`. The empty-tail case is the trivial
subgroup; the residually finite, free, polycyclic, amenable and sofic cases use
that those groups are surjunctive.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 7.2 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
