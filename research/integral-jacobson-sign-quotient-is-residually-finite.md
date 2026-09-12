---
rg: 2
id: integral-jacobson-sign-quotient-is-residually-finite
kind: claim
title: The integral Jacobson elementary group modulo its finitary special linear subgroup is residually finite, so that subgroup is the finite residual
distinct_from:
  integral-jacobson-symbol-kernel-is-finitary-general-linear: that is the algebraic identification of the symbol kernel and of the sign extension, consumed here; this is the analytic-free but nontrivial statement that the sign extension is residually finite, which needs a finite detector built from stable Steinberg groups.
  laurent-elementary-groups-are-residually-finite: that is residual finiteness of the elementary groups over the Laurent ring, the base of the extension; this is residual finiteness of a central order-two extension of it, which does not follow from the base and is proved through K_2 of Z/4.
  central-extension-twisted-sector-criterion: that relates MF of a central order-two extension to a twisted sector of the quotient; this proves residual finiteness of one specific such extension by an explicit finite detector, and MF follows from residual finiteness.
  binary-jacobson-mf-radical-dichotomy: that places the binary Jacobson radical in a two-element set using simplicity of the finitary kernel over the binary field; this computes the finite residual of the integral group, whose finitary kernel is not simple.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  With `J = Z<s,t | ts = 1>`, `S = Z[z,z^-1]`,
`T_n = EL_n(J)/SL_fin(Z)`, and `eta = diag(1 - 2e, 1)` the sign of
`integral-jacobson-symbol-kernel-is-finitary-general-linear`, for every
`n >= 2`:

* `T_n` is residually finite, and the class of `eta` is detected by a
  finite quotient;
* `Res_fin(EL_n(J)) = SL_fin(Z)`, the intersection of the kernels of all
  homomorphisms to finite groups;
* `Rad_MF(EL_n(J)) <= SL_fin(Z)`.

**Why this is not automatic.**  `T_n` is a central extension of the
residually finite `EL_n(S)` by `C_2`; central extensions of residually
finite groups by finite groups need not be residually finite, so the
sign has to be seen by an explicit finite quotient.  The detector is
`K`-theoretic: `T_oo = lim T_n` is `St(S)/<{-1,-1}>`, the class of
`eta` is the Steinberg symbol `{z, -1}`, and the two evaluations
`z -> 1`, `z -> -1` into `St_r(Z/4)`, a finite group in which
`{-1,-1}` is nontrivial, separate `{z,-1}` from `{-1,-1}` and hence
detect `eta`.  Modulo an odd prime the symbol `{-1,-1}` dies and modulo
`2` the sign is invisible, so `Z/4` is the minimal detector.

**Consequences.**  The MF radical of `EL_n(J)` is bounded above by the
locally-residually-finite-by-nothing group `SL_fin(Z)`, which has no
nontrivial finite quotient; whether the radical is all of `SL_fin(Z)` or
trivial is the integral dichotomy
`integral-jacobson-mf-radical-is-all-or-nothing`, and the same detector
is what makes the universal torsion rings' radicals exact
(`universal-torsion-defect-rings-have-exact-mf-radical`).

Derivation: `integral-jacobson-sign-quotient-is-residually-finite-proof`.
