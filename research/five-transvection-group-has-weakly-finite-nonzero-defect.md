---
rg: 2
id: five-transvection-group-has-weakly-finite-nonzero-defect
kind: claim
title: Some homomorphism from the five-transvection group into the units of a weakly finite F_3-algebra sends minus one to minus one and has nonzero two-root defect
distinct_from:
  four-transvections-and-x23-force-defect-vanishing: that asserts every such homomorphism kills the defect; this is its negation, stated as a claim so that a proof refutes the vanishing claim through the graph.
  depth-monotone-units-carry-weakly-finite-nonzero-defect: that builds models with nonzero defect on sofic unit subgroups containing the standard frame; Γ_5 is not known to be sofic, so this is open.
---

**OPEN.** With `Γ_5`, `z`, `x_12(1)` and `x_23(1)` as in `four-transvections-and-x23-force-defect-vanishing`: there are
a weakly finite `F_3`-algebra `W` and a homomorphism `ρ : Γ_5 -> W^x` with `ρ(z) = -1` and
`(ρ(x_23(1)) - 1)(ρ(x_12(1)) - 1) != 0`.

**Routes.**
- `weakly-finite-nonzero-defect-via-sofic-jacobson-image`: soficity of the half-line image `Γ_V <= GL_2(J_(F_3))`.
- Soficity of `Γ_5` itself, or a finite quotient separating the eight elements `z^e x_23(1)^a x_12(1)^b`, also suffices
  (Theorem 4.1 of `research/artifacts/four-transvection-escape-set-2026-09-12.md`). No route node is written for these.

A proof refutes `four-transvections-and-x23-force-defect-vanishing`. It does not decide Gottschalk's conjecture: it
only removes one candidate input for `ternary-anti-central-summand-has-no-weakly-finite-image`.
