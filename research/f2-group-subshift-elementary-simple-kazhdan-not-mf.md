---
rg: 2
id: f2-group-subshift-elementary-simple-kazhdan-not-mf
kind: claim
title: Every finitely generated group containing F_2 gives an infinite finitely generated simple Kazhdan group EL_N(LC(Z,F_q)⋊Γ)/Z with no nontrivial MF quotient
distinct_from:
  paradoxical-cantor-actions-give-simple-kazhdan-not-mf: that is the general theorem for a given action satisfying (H-gen) and (H-par); this supplies such an action for every finitely generated group containing F_2.
  boundary-action-elementary-simple-kazhdan-not-mf: that is the free group on its boundary; this is every finitely generated group containing F_2, on a free symbolic model.
  residually-finite-group-toeplitz-elementary-groups-lef-kazhdan: that gives LEF simple Kazhdan groups from Toeplitz actions of residually finite groups; this gives simple Kazhdan groups with no MF quotient from paradoxical actions, and the two can share an acting group.
artifacts:
  - research/artifacts/un-horofunction-families-paradoxical-subshifts-2026-09-13.md
---

**ESTABLISHED (unreviewed; proof in `f2-group-subshift-elementary-simple-kazhdan-not-mf-proof`).**

**Statement.** Let `Γ` be a finitely generated group containing a nonabelian free subgroup, and let `Z` be the free
minimal paradoxical Cantor subshift of `f2-groups-have-paradoxical-free-minimal-subshifts`. Let `q` be a prime power,
`N ≥ 3` and `R = LC(Z, F_q) ⋊ Γ`.
1. `S_N = EL_N(R)/Z(EL_N(R))` is an infinite, finitely generated, simple group with property (T), and
   `Z(EL_N(R)) ⊆ F_q^× I_N`.
2. For every `n ≥ 2`, every homomorphism from `EL_n(R)` to an MF group is trivial. Hence `S_N` has no nontrivial MF
   quotient.

**Instances** (the `F_2` input is recalled, not imported, so these are not separately established):
- every non-elementary hyperbolic group, one-ended ones included, with no trivial-finite-radical hypothesis;
- `SL_n(ℤ)` for `n ≥ 2`, and other not virtually solvable finitely generated linear groups.

**Both sides at one acting group.** When `Γ` is also residually finite (`F_2`, `SL_3(ℤ)`, surface groups),
`residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` gives a Cantor `Γ`-space whose elementary group is LEF.
So at a fixed acting group the approximation type is decided by the action (towers versus paradox), not by the group.

**Model test.** An amenable acting group can't satisfy the paradox, and the Pestov ring (a minimal `ℤ`-subshift)
carries an invariant measure and gives an LEF group, consistent with the dichotomy.

**Review (un-verify-3, 2026-09-13): PASS.** The route supplies exactly the hypotheses of the reviewed `paradoxical-cantor-actions-give-simple-kazhdan-not-mf`: finitely generated `Γ`, minimal, free hence topologically free, (H-gen), (H-par). "Instances" are recalled and correctly marked not separately established. `research/artifacts/un-review3-2026-09-13-part6.md` §3.
