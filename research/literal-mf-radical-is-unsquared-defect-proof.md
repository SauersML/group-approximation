---
rg: 2
id: literal-mf-radical-is-unsquared-defect-proof
kind: route
title: Identify the unsquared-defect quotient, embed it in a Shulman double, and pull back
target: literal-mf-radical-is-unsquared-defect
requires:
  - unsquared-defect-mf-invisible
  - symmetric-double-weak-mf
  - mf-positive-controls
  - literal-mark-quotient-not-mf
  - universal-mf-quotient
artifacts:
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - research/artifacts/shulman-2603-13564-verified.md
  - GroupApproximation/Sofic/LiteralSignFreeRadicalReduction.lean
---

## Why sufficient

Put `d=tct^-1`, `B=iota(mathcal B)`, `u=[d,v_1]`, and `D=<<u>>^E`.
The affine mod-2 transitivity calculation shows that every commutator `[d,b]`,
`b in B`, is either trivial or conjugate to `u`: `d` commutes with the linear
part and with even translations, while the linear part is transitive on the
seven nonzero parity classes.  Thus `D=N_conj`.

After quotienting by `D`, `d` centralizes `B`; writing `c=t^-1 d t` makes the
old `[c,B]=1` relation redundant because `tBt^-1<=B`.  Since `w=u^2`, the
central-mark relations disappear.  The remaining presentation is

```text
E/D ~= Sigma *_B (B x C_2),
Sigma = <B,t | tbt^-1=alpha(b)>.
```

`Sigma` is finitely generated linear over `Q` in the manuscript's explicit
matrix model, hence residually finite.  Thus `G_0=Sigma x C_2` is residually
finite and MF.  By `symmetric-double-weak-mf`, `G_0 *_B G_0` is MF.  The
natural map `Sigma *_B(B x C_2) -> G_0 *_B G_0` is injective by amalgam normal
form.  Subgroup heredity from `mf-positive-controls` makes `E/D` MF.

By `unsquared-defect-mf-invisible`, every corona homomorphism kills `u`, hence
kills `D`, so `D<=Res_MF(E)`.  Conversely, composing `E->E/D` with a faithful
corona model of the MF quotient has kernel exactly `D`, so `Res_MF(E)<=D`.
Therefore `Res_MF(E)=D=N_conj`.

Finally `<w><=D` because `w=u^2`.  Residual pullback through `E->E/<w>` gives
`Res_MF(E/<w>)=D/<w>`.  The specific involutive witness in the sign-free proof
has base commutators normally generating `D/<w>`, so `D/<w><=D_coll`; the
general collapse theorem gives `D_coll<=Res_MF(E/<w>)`.  Hence

```text
D_coll = Res_MF(E/<w>) = D/<w>,
Res_MF(E) = q^-1(D_coll).
```
