---
rg: 2
id: literal-unsquared-defect-quotient-is-mf-proof
kind: route
title: Embed the unsquared-defect quotient in the residually finite symmetric double
target: literal-unsquared-defect-quotient-is-mf
requires:
  - literal-telescope-split-normal-form
  - symmetric-double-weak-mf
  - mf-positive-controls
artifacts:
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - research/artifacts/shulman-2603-13564-verified.md
---

Put `d=tct^-1`.  The affine parity calculation shows that every `[d,b]`,
`b in B`, is either trivial or conjugate to `[d,v_1]`; hence quotienting by
`D=<<[d,v_1]>>` makes `d` centralize `B`.  Replacing `c` by `t^-1dt` and
removing the now-redundant central-sign relations gives

```text
E/D ~= Sigma *_B (B x C_2).
```

The literal matrix model in `literal-telescope-split-normal-form` realizes
`Sigma` as a finitely generated subgroup of `GL_4(Q)`, so it is residually
finite.  Thus `G_0=Sigma x C_2` is residually finite and MF.  The natural map

```text
Sigma *_B (B x C_2) -> G_0 *_B G_0
```

is injective by amalgam normal form.  The target is MF by
`symmetric-double-weak-mf`, and subgroup heredity from `mf-positive-controls`
makes `E/D` MF.

