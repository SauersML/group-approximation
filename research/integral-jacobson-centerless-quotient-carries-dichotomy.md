---
rg: 2
id: integral-jacobson-centerless-quotient-carries-dichotomy
kind: claim
title: Modulo its scalar center the integral Jacobson elementary group satisfies the whole-group MF dichotomy, and is MF exactly when the group is
distinct_from:
  integral-jacobson-mf-radical-is-all-or-nothing: that is the restricted dichotomy, about the restriction of an MF homomorphism to the finitary special linear subgroup, consumed here; this identifies the only other kernel, the scalar center, and states the dichotomy in whole-group form for the quotient by it and for odd rank.
  mf-group-with-order-two-center-has-mf-central-quotient: that is the general lemma about a group with an order-two center, consumed here; this is its application to the integral Jacobson group together with the converse direction through the residually finite quotient.
  integral-jacobson-elementary-group-is-not-mf: that is the open question; this is an exact reformulation of it on a centerless group, not a decision.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `J = Z<s,t | ts = 1>`, `G_n = EL_n(J)`,
`N_n = SL_fin(Z)`, `T_n = G_n/N_n`, and `n >= 4`.

* `C_(G_n)(N_n) = Z(G_n) = G_n cap {+-I}`, which is `{+-I}` for even `n`
  (`-I = w_12^2 w_34^2 ... w_(n-1,n)^2`) and `{I}` for odd `n` (the
  symbol image of `-I` would have determinant `-1`).  In both cases
  `Z(G_n) cap N_n = 1`.
* For every MF-valued homomorphism `phi` of `G_n`,

  ```text
  N_n <= ker(phi)      or      ker(phi) <= Z(G_n).                       (CZ1)
  ```

  So for odd `n >= 5` the dichotomy holds in whole-group form for `G_n`
  itself: `phi` is injective or kills `N_n`.
* For even `n >= 4` put `P_n = G_n/{+-I}`.  Then `C_(P_n)(N_n{+-I}/{+-I}) = 1`,
  every MF-valued homomorphism of `P_n` is injective or kills the image
  of `N_n`, and

  ```text
  G_n is MF     <=>     P_n is MF.                                       (CZ2)
  ```

**Why it is worth naming.**  It removes the only loophole in the
integral dichotomy: an MF-valued homomorphism of `G_4` injective on
`SL_fin(Z)` may have kernel `{+-I}`, and if `G_4` is MF one does (the
quotient map to `P_4`).  On `P_4` there is no such loophole.  The open
question `integral-jacobson-elementary-group-is-not-mf` is therefore
exactly: does the centerless group `P_4` admit one MF-valued
homomorphism nontrivial on a single transvection.  Nothing is decided.

Derivation: `integral-jacobson-centerless-quotient-carries-dichotomy-proof`.
