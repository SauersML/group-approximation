---
rg: 2
id: leavitt-ternary-frame-tree-uniformization-proof
kind: route
title: Refine frame units to ternary leaves and send the leaves to cylinders of one length; compute the right-child exchange product and a graded top component
target: leavitt-right-child-frames-generate-infinite-order-units
requires: []
artifacts:
  - research/artifacts/locally-finite-conjugation-defect-firewall-2026-09-12.md
---

Complete proof: artifact Sections 3–4.

- **Frame tree.** Every frame unit `S[Acx]T[Acy]` is a sum of leaf units over the complete ternary
  code. A prefix replacement sending the `3^k` leaves to cylinders of one length turns each leaf unit
  into a degree-zero matrix unit. Units of `R` lying in `M_(2^n)(F_2)` are invertible there.
- **Right child.** `iota_(A1)(w_12) S[A10] = S[A110]` and `iota_A(w_23) S[A110] = S[A100]`. So
  `b^n S[A10] = S[A10] s_0^n`, and `b^n = 1` would force `s_0^n = 1`, contradicting `t_1 s_0 = 0`.
- **Coefficient root.** `m = 1 + e_1 + d_1` with `d_1 = (1 + S[A00]T[A10]) S[A10]T[A0]` of degree 1.
  By induction `d_1^n S[A0] = S[A10] s_0^(n-1) + S[A0] s_0^n`, which is nonzero. So `m^n` has a nonzero
  component of degree `n`.
- **Positive only.** A lexicographic potential on the regions strictly decreases along each positive
  unit, so products of more than 9 vanish and the generated group is finite.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 15.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS, with one naming correction: b sends A10, A110, A111 to A100, A11, A101, which does not preserve order, so b is in V but not in F (it is x_0 on A1 followed by the exchange of A101 and A11). Infinite order and every conclusion are unaffected.*
