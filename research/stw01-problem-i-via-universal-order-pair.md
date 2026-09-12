---
rg: 2
id: stw01-problem-i-via-universal-order-pair
kind: route
title: Settle Problem I by additivity on the universal order pair, via affine rescaling
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-universal-order-pair-quasitrace-additivity
  - stw01-order-pair-defects-rescale-generic-defects
---

Assume every bounded 2-quasitrace on the universal order-pair algebra `U` adds
`(h_0, k_0)`. Let `sigma` be a bounded 2-quasitrace on a unital C*-algebra `A`.

1. **Additivity on `A_+` gives a trace.** For `a, b in A_sa`,
   `a_+ + b_+ + (a + b)_- = (a + b)_+ + a_- + b_-`. Applying `sigma`, additivity on `A_+`, and
   `sigma(c) = sigma(c_+) - sigma(c_-)` on each `C*(c)` gives `sigma(a + b) = sigma(a) + sigma(b)`.
   Real homogeneity holds on each `C*(a)`, and `sigma(a + ib) = sigma(a) + i sigma(b)` is an
   axiom. So `sigma` is linear, and with `sigma(z^* z) = sigma(z z^*)` it is a trace. Hence if
   `sigma` is not a trace, some `x, y in A_+` have `D(x, y) != 0`.
2. **Normalize.** With `t = 1 / max(||x||, ||y||)`, homogeneity on commutative subalgebras
   gives `D(t x, t y) = t D(x, y) != 0`, and `tx`, `ty` are contractions.
3. **Rescale and pull back.** `stw01-order-pair-defects-rescale-generic-defects` with
   `eps = 1/5`, `s = 0` gives a unital *-homomorphism `psi : U -> A` with
   `psi(h_0) = (1/2) 1 + (1/5) t x` and `psi(k_0) = (1/5) t y`. Then `sigma o psi` is a
   bounded 2-quasitrace on `U`: composition with a *-homomorphism preserves the axioms, as
   recorded on `stw01-modular-single-pair-via-universal-order-pair`. Its defect on
   `(h_0, k_0)` is `(1/5) t D(x, y) != 0`, contradicting the assumption.

So every bounded 2-quasitrace is a trace.

**Relation to the modular chain.** The existing chain
`stw01-modular-single-pair-via-universal-order-pair` then
`stw01-problem-i-via-modular-single-pair` reaches the same root through Steps 0-3 in a
type `II_1` AW*-factor, the three-block dilation and an intermediate-value tuning of `eps`.
This route needs none of them. The converse (Problem I implies the required claim) is
trivial and is not recorded as a route, to avoid a dependency cycle. Details: Section 2 of
`research/artifacts/stw01-order-pair-rescaling-2026-09-12.md`.
