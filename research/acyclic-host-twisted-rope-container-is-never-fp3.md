---
rg: 2
id: acyclic-host-twisted-rope-container-is-never-fp3
kind: claim
title: "No acyclic-host twisted rope container of a universal finitely presented group is of type FP_3"
distinct_from:
  acyclic-host-twisted-rope-container-is-of-type-fp3: that is the negation of this claim, the open candidate this claim refutes
---

Take the construction of `acyclic-host-twisted-rope-container-is-of-type-fp3`:

- `G = F/R` finitely presented, containing a universal finitely presented
  group;
- `L = F_1 *_R F_2` the double and `π: L → G`;
- `ι_0: L → P_0` with `P_0` finitely presented;
- `K_ac(G) = HNN(P_0 × L × G; L; f_1, f_2)` with `f_1(y) = (ι_0(y), 1, 1)`
  and `f_2(y) = (1, y, π(y))`.

**Claim.** For every choice of `G`, `P_0` and `ι_0`, `K_ac(G)` is not of type
`FP_3(Q)`, so not `FP_3`, `F_3` or `F_∞`. Acyclicity of `G` and `P_0` is not
used; only their finite presentability is.

It is an instance of `split-edge-hnn-with-non-fp2-edge-is-not-fp3`, through
route `acyclic-host-container-not-fp3-via-split-edge`. So the integral
homology circle `K_ac(G)` passes every trivial-coefficient test and still
fails `FP_3`, on product coefficients.
