---
rg: 2
id: sylvester-leavitt-defect-gap-and-geometric-descent
kind: claim
title: Every Sylvester rank function on the binary Leavitt unit group algebra has a normalized defect gap and geometric two-sided descent
distinct_from:
  leavitt-defect-descent-chain-holds-in-regular-rank-rings: that is the gap, descent and near-minimal multiplicativity for homomorphisms into faithful regular rank rings, with exact lower descent constant c_*; this is the gap and the two-sided descent, with lower constant c_0/m_0, for every Sylvester rank function, with no regular envelope.
  sylvester-rank-functions-have-a-uniform-two-root-defect-gap: that bounds the defect below by a constant depending on the displacement eta of a generator; this normalizes by the augmentation quotient, so the constant is uniform over all non-augmentation rank functions, and adds the descent.
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

**ESTABLISHED** (lane `w5-regular-rankfn`; verified PASS by `w4-vf-gate`, Section 26 of
`research/artifacts/gk-vf-gate-verification-2026-09-12.md`, fbcf9d2005) by
`sylvester-leavitt-defect-gap-descent-proof`.

Let `R = L_(F_2)(1,2)`, `D = ([x_23(1)] - 1)([x_12(1)] - 1)` in `F_2[R^x]` through `R^x = EL_3(R)`, and
`D_A = iota_A(D)` for a proper prefix `A`. Let `rho` be any Sylvester matrix rank function on `F_2[R^x]` other
than the augmentation rank, and `rho_omega` its augmentation quotient
(`perfect-group-augmentation-quotient-ranks-are-fixed-point-free`). There are constants `c_0 > 0` and `m_0 >= 1`,
independent of `rho`, such that:
1. **Gap.** `c_0 <= rho_omega(D_A) <= 1/2` for every proper prefix `A`;
2. **Descent.** For pairwise disjoint proper cylinders `A_1, ..., A_k` with proper union,
   `f(k) = rho_omega(D_(A_1) ... D_(A_k))` depends only on `k`, and `(c_0/m_0) f(k) <= f(k+1) <= f(k)/2`.

`c_0 = c^Syl(1/4)` comes from compactness, and `m_0` from normal generation of `R^x` by the nine-leaf subgroup.

**Consequence.** Of the class-(A') defect chain of `research/artifacts/rank-gate-axiom-audit-2026-09-12.md`
Section 3, only two inputs still need a regular envelope: exact globality, which gives the constant `c_*` in place
of `c_0/m_0` (`sylvester-leavitt-kazhdan-fixed-ideals-are-global`), and kernel corners for near-minimal
multiplicativity (`sylvester-near-minimal-leavitt-defects-are-multiplicative`).

## Attempts

Established, not open. Proof in artifact Section 4.
