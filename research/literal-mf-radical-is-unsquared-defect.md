---
rg: 2
id: literal-mf-radical-is-unsquared-defect
kind: claim
title: The finitely presented sofic literal group has radical equal to the unsquared defect
root: true
goal: true
distinct_from:
  literal-mf-radical-exact: That retained refuted claim asserted the smaller equality `Res_MF(E)=<w>`; this is the correct exact computation after the sign-free theorem.
  unsquared-defect-mf-invisible: That established claim proves only the inclusion `<<u>> <= Res_MF(E)`; this claim proves equality and identifies the universal MF quotient.
artifacts:
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - GroupApproximation/Sofic/LiteralSignFreeRadicalReduction.lean
  - GroupApproximation/Sofic/LiteralTheoremAPackage.lean
  - non_mf_groups_exist.tex
---

The literal group `E` is finitely presented and sofic.  Put

```text
u = [tct^-1,v_1],
D = <<u>>^E.
```

Then the main target is the boxed equality

```text
BOXED: Rad_MF(E) = D = <<[tct^-1,v_1]>>^E = N_conj,
E/Rad_MF(E) ~= Sigma *_B (B x C_2),
```

and that quotient is MF.

Moreover, if `q:E->E/<w>` and `D_coll` is the involutive collapse defect of
the witness used in the sign-free theorem, then

```text
Rad_MF(E/<w>) = D_coll = D/<w>,
Rad_MF(E) = q^-1(D_coll).
```

Thus the projection-collapse criterion computes the residual exactly for the
principal literal example.

There are now two independent routes to the hard lower inclusion.  The new
route exactifies the finite eight-lamp packet in `E/<w>`, follows its 256
character types through the affine holonomy, and closes the one-sided
compression on an authenticated common carrier.  Its terminal rational rank
certificate is `W>=0` and `4W<=2W`, hence `W=0`; it does not use the original
commuting-involution endpoint.
