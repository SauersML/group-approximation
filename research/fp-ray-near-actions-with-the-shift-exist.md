---
rg: 2
id: fp-ray-near-actions-with-the-shift-exist
kind: claim
title: Some finitely presented group has a faithful near action on N in which one element is the shift and the index kernel is finitely generated, acts with infinite supports, not virtually abelian, and is realizable
distinct_from:
  subshift-full-groups-give-infinite-order-twisted-near-shells: that gives the natural examples, whose near groups (topological full groups of minimal subshifts) are not finitely presented; this asks for a finitely presented one.
  decidable-inputs-have-fp-genuine-action-shell-envelopes: that is the universal shell claim; this is one test case whose success passes both germ gates for an input that is not virtually abelian, which is not yet known for any input.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**OPEN.** There are a finitely presented group `R`, an element `t ∈ R`, and an injective homomorphism
`nu: R -> NearSym(N)` with the following properties:
- `nu(t) = s`;
- `P = ker(index ∘ nu)` is finitely generated and not virtually abelian;
- every `g ∈ P ∖ {1}` has infinite support;
- `nu|P` is realized by a genuine action `rho`.

Then `R = P ⋊ <t>`. By `twisted-genuine-shell-actions-pass-both-germ-gates`, `rho` passes both germ
gates of the genuine-action shell. It would be the first input that is not virtually abelian to do so.

## Notes

- Topological full groups of minimal subshifts give everything except finite presentation
  (`subshift-full-groups-give-infinite-order-twisted-near-shells`).
- By `automorphism-twisted-shell-actions-have-finitely-many-orbits`, `rho(P)` has finitely many
  orbits up to a finite set.
- Candidates to test: full groups of non-minimal Cantor systems with a single dense forward orbit;
  groupoids mixing a Z-action with a contracting self-similar part (to break the LEF obstruction); and
  Houghton-type groups with their finitary part replaced by infinite-support elements.

## Attempts

- **Two-radix odometer host (bh-shell-arith, 2026-09-18).** `two-radix-host-meets-the-fp-ray-conditions-except-realizability`:
  the `F_infinity` host `H` of `two-radix-odometer-host-is-f-infinity-with-fg-charge-kernel` acts
  genuinely on `{0,1} x Z` with `s` the translation. Its restriction to the nonnegative ray gives a
  finitely presented `R = H` with `t = s`, a finitely generated, not virtually abelian index kernel `P`,
  and infinite supports. So this is the "mixed `Z`-action plus self-similar" candidate, and it escapes
  the LEF obstruction. It fails at realizability:
  `commuting-translations-sharing-an-inflow-ray-are-not-realizable` applies to the commuting pair
  `a_(d_0) a_(c')^-1`, `a_(d_1) a_(c')^-1` in `P`, and to all finite-index subgroups. So a positive
  candidate must have no two commuting index-zero elements that drain a common ray into different rays.
