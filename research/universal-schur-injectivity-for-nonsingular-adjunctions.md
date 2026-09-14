---
rg: 2
id: universal-schur-injectivity-for-nonsingular-adjunctions
kind: claim
title: Every nonsingular one-variable adjunction injects the Schur multiplier of its coefficient group
refuted_by: [some-nonsingular-equation-has-nonzero-schur-kernel]
distinct_from:
  some-nonsingular-equation-has-nonzero-schur-kernel: that asks for one killed class and would refute this; this is the universal positive statement, and exactly one of the two can end up established.
  nonsingular-adjunction-never-enlarges-schur-multiplier: that proves the second-homology map is always onto; this asks that it is always also one-to-one.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

**OPEN.** For every countable group `Q` and every `w in Q * <t>` with
`deg_t(w) != 0`, the map `H_2(Q; Z) -> H_2((Q * <t>)/<<w>>; Z)` is injective.
By `nonsingular-adjunction-never-enlarges-schur-multiplier` it would then be
an isomorphism.

By `kl-failure-yields-a-schur-kill` this implies
`kervaire-laudenbach-nonsingular-conjecture`. Whether the converse holds is
`kl-implies-universal-schur-injectivity`.

## Attempts

1. **Reduce to the coefficient subgroup.** Partial:
   `schur-kernel-localizes-to-coefficient-subgroup` and
   `amenable-coefficients-have-zero-schur-kernel` settle the claim whenever the
   coefficient subgroup is amenable, or more generally has Connes-embeddable
   twisted group algebras. They say nothing when the coefficient subgroup is
   neither.
2. **Aspherical relative presentations.** They settle it by
   `aspherical-adjunction-has-zero-schur-kernel`. Not every adjunction is
   aspherical, so this is not a proof.
3. **From the conjecture.** Open as `kl-implies-universal-schur-injectivity`.
