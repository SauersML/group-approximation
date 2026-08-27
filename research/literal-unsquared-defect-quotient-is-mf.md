---
rg: 2
id: literal-unsquared-defect-quotient-is-mf
kind: claim
title: The quotient of the literal group by the unsquared defect is MF
distinct_from:
  literal-mf-radical-is-unsquared-defect: That also proves the hard radical lower inclusion; this isolates the independent quotient model used only for the reverse inclusion.
  symmetric-double-weak-mf: That is the general positive theorem for a symmetric double; this identifies and embeds the concrete literal quotient into one such double.
artifacts:
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - research/artifacts/shulman-2603-13564-verified.md
---

For `u=[tct^-1,v_1]` and `D=<<u>>^E`, one has

```text
E/D ~= Sigma *_B (B x C_2),
```

where `Sigma=<B,t | tbt^-1=alpha(b)>` is the literal affine telescope.  This
quotient is operator MF.  Consequently a faithful norm-matrix-corona model
of `E/D`, pulled back to `E`, has kernel exactly `D`.

