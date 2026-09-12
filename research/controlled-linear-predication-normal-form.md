---
rg: 2
id: controlled-linear-predication-normal-form
kind: claim
title: Orthogonal predication lowers controlled linear relations to parity operator equations
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-readable-control-freezing-to-lcs: freezing asks for one globally invariant readable atom; predication works locally on the whole direct-sum representation and deliberately leaves selector soundness unresolved.
  finite-linear-commutation-system-to-lcs: that compiler starts from unconditional affine equations and commutations; this claim is the exact lowering step that turns each controlled branch relation into such an equation plus selector involutions.
---

Let `P_1,...,P_m` be pairwise orthogonal projections summing to `1`, and let
`U_1,...,U_n` be self-adjoint involutions commuting with every `P_a`. Define

```text
G_(a,i) = P_a U_i + (1-P_a),
Z_a     = 1 - 2P_a.
```

Then all `G_(a,i)` and `Z_a` are self-adjoint involutions,

```text
prod_a G_(a,i) = U_i,
```

and whenever the participating `U_i` commute, the controlled branch equation

```text
P_a prod_(i in I_a) U_i = (-1)^b P_a
```

is equivalent to the unconditional parity operator equation

```text
prod_(i in I_a) G_(a,i) = Z_a^b.
```

Thus finite controlled-linear operator relations admit an exact predicated
normal form. All remaining nonlinearity is confined to the assertion that the
`Z_a` arise from one mutually exclusive and exhaustive projection partition.
