---
rg: 2
id: nonsingular-adjunction-never-enlarges-schur-multiplier
kind: claim
title: Adjoining a nonsingular root maps the old Schur multiplier onto the new one
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `Q` be a group, `w in Q * <t>` with `deg_t(w) != 0`, and
`q : Q -> X = (Q * <t>)/<<w>>`. Then

    q_* : H_2(Q; Z) -> H_2(X; Z)   is surjective,

so `H_2(X) = H_2(Q)/K_2(Q, w)`, where `K_2(Q, w) = ker q_*` is the **Schur
kernel** of the adjunction.

With `Q = F(S)/R_Q`, `F' = F(S) * <t>`, `R_Y = <<R_Q>>_{F'}` and a lift
`w~ in F'` of `w`, the Hopf class of `r in R_Y cap [F',F']` lies in the
Schur kernel exactly when

    r in [F', R_Y] . [F', <<w~>>].

So a nonzero Schur kernel has a finite certificate: one identity in the free
group `F'`, plus a proof that `r notin [F', R_Y]`.

DERIVATION
nonsingular-schur-surjection-proof
