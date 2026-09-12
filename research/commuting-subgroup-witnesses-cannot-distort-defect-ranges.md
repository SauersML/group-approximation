---
rg: 2
id: commuting-subgroup-witnesses-cannot-distort-defect-ranges
kind: claim
title: Witnesses drawn from any rank-modelled subgroup of units supported off the cylinder set never distort a defect range, even when they have infinite order
distinct_from:
  some-commutant-element-distorts-defect-range-rank: that is the open distortion target for every nontrivial model of R^x; this is a firewall on a model of L x Lambda showing commuting witnesses from a rank-modelled Lambda are inert.
  locally-finite-hnn-data-allow-independent-cylinder-defects: that realizes identities inside one locally finite subgroup plus single conjugations with independent defects; this realizes a commuting non-locally-finite subgroup, such as the infinite-order escaping units, as a tensor factor with exactly proportional ranks.
  finite-subgroup-data-cannot-force-defect-submultiplicativity: that is the regular assignment on finite-subgroup algebras; this covers matrices over the group algebra of an infinite subgroup of units supported off U.
artifacts:
  - research/artifacts/commutant-distortion-product-firewall-2026-09-12.md
---

**ESTABLISHED** (route `commuting-subgroup-witness-product-model-proof`; artifact Section 2; independent
re-derivation requested from `w4-vf-gate`).

**Statement.** In `R^x = L_(F_2)(1,2)^x`, let `U` be clopen proper, `Theta` a frame triple with union a proper
subset of `U`, `L <= G_U` a countable infinite locally finite subgroup containing the two transvections of
`Theta`, and `Lambda <= G_(U^c)` a countable subgroup with some characteristic-two rank model `rho`. Then
`<L, Lambda> = L x Lambda`, and `sigma_L (x) rho` is a nontrivial fixed-point-free rank model of `L x Lambda` with
`delta = rk(D_Theta) = 3/8` and

```text
rk(D_Theta Z) = delta rk(Z)      for every n and every Z in M_n(sigma(F_2[Lambda])) .
```

Every invariant summand built from such `Z` has normalized defect exactly `delta`.

**Consequence.** The escaping units `b = iota_A(w_23) iota_(A1)(w_12)` and `x^A_12(s_0) x^A_21(1)`, placed off `U`,
generate infinite cyclic groups, which have rank models. So as commuting witnesses they cannot supply
`some-commutant-element-distorts-defect-range-rank`. A distortion proof has to use straddling units of `R^x` as
factors (not only as conjugators), properties of `Lambda` that no rank model has, or global inputs (corner
locality, globality, compactness). Artifact Section 3.

## Attempts

- Established, not open. Tensor product of the regular direct-limit model of `L` with `rho`, along a product
  ultrafilter; ranks multiply.
