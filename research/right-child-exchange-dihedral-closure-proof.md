---
rg: 2
id: right-child-exchange-dihedral-closure-proof
kind: route
title: Conjugate the root at A1 by b, read the pair in the frame (A10, A11), take the lowest-degree part of the powers, and split off the upper-right block
target: right-child-exchange-group-has-infinite-dihedral-root-closure
requires:
  - leavitt-right-child-frames-generate-infinite-order-units
artifacts:
  - research/artifacts/right-child-exchange-group-structure-2026-09-12.md
---

Artifact Sections 1–5. **OPEN** until `w4-vf-gate` re-derives it.

1. **`b` on points** (item 2 of `leavitt-right-child-frames-generate-infinite-order-units`). `b` fixes `A0z`, sends
   `A10z -> A100z`, `A110z -> A11z`, `A111z -> A101z`, and is the identity off `[A]`.
   * Its matrix on `[A1]` is `[[s_0, s_1t_1],[0, t_0]]`, with inverse `[[t_0, 0],[s_1t_1, s_0]]`.
   * `b = (A101 <-> A11) ∘ b'`, where `b' = x_0` on `[A1]`.
2. **Conjugates.** `b S[v]T[w] b^-1` is the operator `b(wy) -> b(vy)`.
   * On the six positive roots this gives the artifact Section 2 table. Only `S[A110]T[A111] -> S[A11]T[A101]`
     increases.
   * Under `b'` every row decreases.
3. **Splitting.** With respect to `e_(A0) + e_(A1) + (1 - e_A)`, every generator is `(m, h)` with the product
   `(m,h)(m',h') = (m' + m h', h h')`.
   * The generators `iota_A(x_12(1))` and `iota_A(x_13(1))` have `h = 1`, and the others have `m = 0`.
   * Projection to `h` is a split surjection, and its kernel is abelian of exponent 2.
   * Stripping `A1` by `r -> T[A1] r S[A1]` gives `<x, y, u, beta>`.
4. **Infinite order.**
   * `N_1 = S[A10]T[A11]` and `N_2 = S[A11]T[A101]` square to zero.
   * In the frame `(A10, A11)`, `u_1 u_2 = [[1+t_1, 1],[t_1, 1]]`.
   * The grading `deg s_i = 1`, `deg t_i = -1` is preserved entrywise, and the degree `-n` part of the `n`-th power is
     `[[t_1^n,0],[t_1^n,0]] != 0`.
5. **Orders and locally finite subgroups.**
   * A subgroup normalized by `b` that contains `iota_A(x_23(1))` and `iota_(A1)(x_23(1))` contains `u_1` and `u_2`, so
     it contains `D_inf`.
   * Under `b'`, the conjugate `1 + S[A101]T[A11]` commutes with `u_1`, because `T[A11]S[A101] = 0 = T[A11]S[A10]`, and
     all conjugates lie in `U_<`.
6. **Theorem S.** Elements supported in `[A]` and in `[B]` commute and meet trivially, so the group is
   `Gamma_b × D_8`. Soficity passes both ways between `Gamma_b × D_8` and `Gamma_b`. `b` has infinite order.
   * The contrapositive of `sofic-subgroups-carry-independent-cylinder-defects` gives the certificate form.
