---
rg: 2
id: shadow-kleene-saturation-metatheorem
kind: claim
title: A HALT-surviving and NONHALT-shadow-erased word compiler yields a finitely presented full-MF-radical group
root: true
distinct_from:
  threshold-free-reverse-kleene-mf-higman: that theorem requires NONHALT membership in the MF radical itself; this theorem requires only membership in the strictly larger operator-to-HS shadow residual and recovers operator-norm invisibility after saturation.
  threshold-free-reverse-kleene-higman-diagonal: that theorem targets all HS microstates and concludes nonhyperlinearity; this one only controls HS shadows of operator-norm microstates and concludes full MF radical.
  single-shadow-word-saturation-compiler: that theorem consumes an already nontrivial shadow word; this theorem uses Kleene proof search to manufacture one from HALT/NONHALT compiler semantics.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

Suppose a total computable compiler sends a machine index `e` to a finite
alphabet, a uniformly recursively enumerable relator stream presenting
`Gamma_e`, and a word `w_e`, such that

```text
HALT(e)    => w_e != 1 in Gamma_e,
NONHALT(e) => w_e in S(Gamma_e).
```

Then there exists a nontrivial 2-generated finitely presented
acylindrically hyperbolic property-(T) group `Q` with
`normMFResidual Q=top`.  The fixed-point machine searches only for a finite
proof of `w_e=1`; it uses no matrix dimension, defect threshold, convergence
rate, or soundness modulus.

The proposition-level self-aware contradiction is machine-checked as
`shadowKleene_fixedPoint_logic`; presentation computability and Kleene's
recursion theorem remain the explicit external layer.
