---
rg: 2
id: deligne-twisted-group-algebra-is-not-stably-finite
kind: claim
title: A twisted group algebra of Sp4(Z) with Deligne's multiplier fails stable finiteness in some characteristic other than three
refuted_by:
  - deligne-triple-cover-group-algebras-are-stably-finite
distinct_from:
  deligne-triple-cover-nonsurjunctive: that asks for any strict automaton on E_3 over any alphabet; this asks for the linear witness, a one-sided invertible matrix over a twisted group algebra of Sp4(Z), which also makes E_3 non-linear-sofic.
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

**OPEN.** For some prime `p != 3`, finite field `F` of characteristic `p` containing a primitive cube root of
unity `w`, `j in {1, 2}` and `n >= 1`, there are `A, B` in `M_n(F^(w^(ja))[Sp_4(Z)])` with `BA = 1 != AB`. Here
`a` is the section cocycle of Deligne's triple cover `E_3`.

**Payoff.**
- **Gottschalk:** a strict linear automaton on `E_3`
  (`deligne-cover-nonsurjunctive-from-twisted-algebra-failure`), refuting Gottschalk and
  `finite-normal-subgroups-do-not-affect-surjunctivity`.
- **Linear soficity:** `E_3` is not `F_p`-linear sofic and not sofic
  (`non-linear-sofic-via-deligne-twisted-algebra-failure`). No group is known to be non-linear-sofic.

## Attempts

- **Constraints on any witness:**
  - **Rank models.** It refutes rank-approximate projective representations of the multiplier in
    characteristic `p` (`deligne-cover-linear-soficity-is-rank-projective-approximation`). So a witness is at
    least a rank-metric sector gap.
  - **Support.** Its support group `Lambda <= Sp_4(Z)` must keep `z` in the finite residual of its preimage in
    `E_3`. Otherwise the multiplier dies on a finite-index subgroup of `Lambda` and the algebra embeds in a
    matrix ring over a stably finite untwisted group algebra. Virtually free and amenable `Lambda` are
    excluded.
- **Design sources: none.**
  - The strict-pair designs on main (Leavitt corners, invariant output, table groups) come from hosts with a
    compression `R = R^2`.
  - `Sp_4(Z)` is linear, and its untwisted group algebras are stably finite.
  - The only non-linear-algebraic input is the non-inflated multiplier, and no mechanism turns a
    multiplier into a one-sided inverse.
