---
rg: 2
id: literal-mf-radical-is-unsquared-defect
kind: claim
title: The literal MF residual is the normal closure of the unsquared defect
root: true
distinct_from:
  literal-mf-radical-exact: That retained refuted claim asserted the smaller equality `Res_MF(E)=<w>`; this is the correct exact computation after the sign-free theorem.
  unsquared-defect-mf-invisible: That established claim proves only the inclusion `<<u>> <= Res_MF(E)`; this claim proves equality and identifies the universal MF quotient.
artifacts:
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - GroupApproximation/Sofic/LiteralSignFreeRadicalReduction.lean
  - non_mf_groups_exist.tex
---

For the literal finitely presented group `E`, put

```text
u = [tct^-1,v_1],
D = <<u>>^E.
```

Then

```text
Res_MF(E) = D = N_conj,
E/Res_MF(E) ~= Sigma *_B (B x C_2),
```

and that quotient is MF.

Moreover, if `q:E->E/<w>` and `D_coll` is the involutive collapse defect of
the witness used in the sign-free theorem, then

```text
Res_MF(E/<w>) = D_coll = D/<w>,
Res_MF(E) = q^-1(D_coll).
```

Thus the projection-collapse criterion computes the residual exactly for the
principal literal example.
