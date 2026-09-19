---
rg: 2
id: sp4-metaplectic-class-is-not-inflated-from-level-two
kind: claim
title: The mod-two reduction of the universal-cover class of Sp4(Z) is not pulled back from Sp4(F2)
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/spin_seed.py
distinct_from:
  sp4-spin-cover-projective-representation-in-dimension-four: that exhibits one realizable torsion class in dimension four and shows it is not the metaplectic class; this compares the metaplectic class against every class inflated from the level-two quotient.
  sp4-fd-projective-multiplier-is-finite: that bounds the group of finite-dimensionally realizable multipliers; this shows one specific finite quotient, level two, realizes none of the metaplectic class.
---

Let `mu_2 in H^2(Sp_4(Z); Z/2)` be the reduction of the class of the
universal-cover extension `1 -> Z -> Sp~_4(Z) -> Sp_4(Z) -> 1`, the class of
the metaplectic double cover `E_2`.  Let `q : Sp_4(Z) -> Sp_4(F_2) = S_6`.
Then `mu_2` is not in the image of `q^* : H^2(S_6; Z/2) -> H^2(Sp_4(Z); Z/2)`.

`H^2(S_6; Z/2)` has three nonzero classes: the class of the spin double
cover (restricting nontrivially to `A_6`), its sum with the cup square of the
sign character, and the cup square itself.  Projective representations of
`Sp_4(Z)` realizing the three pullbacks are explicit: the basic spin
representation pulled back through the odd theta characteristics
(`sp4-spin-cover-projective-representation-in-dimension-four`), its twist by
the scalar `i^{sign}`, and the scalar representation `i^{sign}` alone (every
root generator is a transvection, hence an odd permutation of the six odd
characteristics).  For each, the linear system over `F_2` asking for
generator signs that make the relator scalars equal `(-1)^{k_r}`, with `k_r`
the universal-cover lift exponents, is inconsistent.  Since the only
coboundary freedom on a fixed generating set is such a sign rescaling, none of
the three pulled-back classes equals `mu_2`.

**ESTABLISHED (computational).**  Consequently no finite-dimensional
representation of the metaplectic cover `E_2` with `z -> -1` factors through
the level-two congruence quotient; the finite quotients of `E_2` in which `z`
survives, which exist by Deligne, live at deeper levels.
