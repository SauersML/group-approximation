---
rg: 2
id: leavitt-right-child-frames-generate-infinite-order-units
kind: claim
title: The ternary tree of Leavitt frames at a cylinder conjugates into degree-zero units, while the frame at the right child, or a coefficient root with an opposite root, already gives units of infinite order
distinct_from:
  locally-finite-hnn-data-allow-independent-cylinder-defects: that is the rank model with independent defects for identities of one locally finite subgroup plus single conjugations; this decides which configurations of Leavitt frames fit inside one locally finite subgroup and which do not.
  finite-subgroup-data-cannot-force-defect-submultiplicativity: that says what is left is a unit of infinite order used as a factor; this computes the smallest such configurations, the right-child exchange product (a first generator of Thompson's F) and x_12(s_0) x_21(1), and shows the whole ternary frame tree at a cylinder lies in one locally finite conjugate of the degree-zero units.
artifacts:
  - research/artifacts/locally-finite-conjugation-defect-firewall-2026-09-12.md
---

**ESTABLISHED** (proof route `leavitt-ternary-frame-tree-uniformization-proof`; artifact Sections 3–4).

Let `R = L_(F_2)(1,2)` with code `(0, 10, 11)`, and let `A` be a proper cylinder. Write
`iota_P(GL_3(F_2))` for the finite frame at `P`: roots of both signs, Weyl elements and the `F_2`-torus.

1. **The ternary frame tree.** For every `k >= 1` there is a prefix replacement `w` in `V` conjugating
   all of the following into the degree-zero units `union_n GL_(2^n)(F_2)`, a locally finite group:
   * `iota_(Ac)(GL_3(F_2))` for every word `c` of length `< k` over `{0, 10, 11}`;
   * for `k >= 2`, the nine-leaf `GL_9(F_2)` at `A`.

   So the frames at `A`, `A0`, `A10`, `A11`, every halving unit, and opposite roots at those child
   cylinders all lie in one locally finite subgroup.
2. **The right child.** `b = iota_A(w_23) iota_(A1)(w_12)` satisfies `b S[A10] = S[A10] s_0`, so it has
   infinite order. It sends `A10, A110, A111` onto `A100, A11, A101`, a first generator of Thompson's
   `F` on `A1`.
3. **A coefficient root.** `x^A_12(s_0) x^A_21(1)` has infinite order: its `n`-th power has a nonzero
   component of degree `n`.
4. **Positive roots only.** The positive unit roots of the frames at `A` and `A1` generate a finite
   group.

**Consequence.** `locally-finite-hnn-data-allow-independent-cylinder-defects` covers every identity
among the frame tree of item 1. The smallest configurations it cannot cover by one locally finite
subgroup are the frames at `A` and `A1` with an opposite root or Weyl element, and root groups with
coefficients of nonzero degree with an opposite root. An argument for
`leavitt-disjoint-cylinder-defects-strictly-submultiplicative` has to use identities from such a
configuration, beyond single conjugation, or a global input about all rank models of `R^x`.
