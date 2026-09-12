---
rg: 2
id: stw93-jiang-su-slice-ideal-is-quasitrace-null
kind: claim
title: The Jiang--Su trace-zero slice generates a quasitrace-null XCIII ideal
distinct_from:
  stw93-tensor-factor-central-quasitrace-rigidity: that claim controls restriction to the embedded central slice; this one passes from the trace-zero part of the slice to the ambient ideal it generates and identifies the resulting quotient quasitraces.
  stw01-qt-invisible-ideal-extension-principle: that is an abstract extension principle assuming an entire ideal is quasitrace-invisible; this claim proves that hypothesis for a concrete candidate ideal inside the XCIII trace kernel.
artifacts:
  - research/artifacts/stw93-xciii-free-group-jiang-su-si-audit-2026-08-30.md
---

Let

```text
A=C*_r(F₂)⊗𝒵,   D=A_ω∩A',   I=J_τ∩D,
ι:F(𝒵)→D,      E=J_τ∩F(𝒵),
K_𝒵=Ideal_D(ι(E)).
```

Then `K_𝒵⊆I`, and every normalized `2`-quasitrace on `D` vanishes
on `(K_𝒵)_+`.  Consequently pullback along `π:D→D/K_𝒵` is a
bijection

```text
QT₁(D/K_𝒵) ≅ QT₁(D).
```

Thus the XCIII unique-quasitrace problem is unchanged after quotienting by
`K_𝒵`, and its trace-kernel obstruction is exactly the residual ideal
`I/K_𝒵`: every normalized quasitrace on `D` annihilates `I` if and only
if every normalized quasitrace on `D/K_𝒵` annihilates `I/K_𝒵`.
