---
rg: 2
id: right-child-exchange-group-has-infinite-dihedral-root-closure
kind: claim
title: The right-child exchange group splits as an elementary abelian 2-group by a two-chart root group, and b turns its x_23 roots at A and A1 into an infinite dihedral pair, so no locally finite subgroup normalized by b contains both
distinct_from:
  lex-decreasing-units-with-order-preserving-letters-are-amenable: that puts the frames at A and A1 with an order-preserving letter such as x_0 inside the amenable U_< ⋊ P, and its Lemma 6.1 excludes setwise orders preserved by b; this shows that for b, which is x_0 on A1 followed by the exchange of A101 and A11, one b-conjugate root generates D_inf with iota_A(x_23(1)), which excludes every order and every locally finite subgroup normalized by b.
  leavitt-right-child-frames-generate-infinite-order-units: that shows b has infinite order and the positive roots at A and A1 generate a finite group; this computes the b-conjugates of those roots, finds exactly one increasing one, iota_A(E_32(t_1)), shows it generates D_inf with iota_A(x_23(1)), and splits the group they generate with b.
  sofic-subgroups-carry-independent-cylinder-defects: that gives theta = 1 on sofic subgroups; this says the right-child exchange group meets that hypothesis exactly when it is sofic, reduces its amenability to the root group <x, y, u, beta>, and leaves that open.
  locally-finite-hnn-data-allow-independent-cylinder-defects: that models identities of one locally finite subgroup plus single conjugations; this shows a locally finite subgroup containing iota_A(x_23(1)) cannot contain the b-conjugate of iota_(A1)(x_23(1)), and that the HNN extension over the finite positive-root group does not model the relation [b x b^-1, x] = 1.
artifacts:
  - research/artifacts/right-child-exchange-group-structure-2026-09-12.md
---

**OPEN** (proved on paper, artifact Sections 1–5; held OPEN until `w4-vf-gate` re-derives it).

**Setting.** `R = L_(F_2)(1,2)` with code `(0, 10, 11)`, and `S[v]T[w]` is the prefix replacement `wy -> vy`. Let `A`
be a proper cylinder and `b = iota_A(w_23) iota_(A1)(w_12)`, which equals
`S[A0]T[A0] + S[A100]T[A10] + S[A11]T[A110] + S[A101]T[A111] + 1 - e_A`. Write
`Gamma_b = <iota_A(D_8), iota_(A1)(D_8), b>`.

**Statement.**
1. **Conjugates.** Of the six `b`-conjugates of the positive roots at `A` and `A1`, only one increases
   lexicographically:
   `b iota_(A1)(x_23(1)) b^-1 = 1 + S[A11]T[A101] = iota_A(E_32(t_1))`.
   With `b' = x_0` on `[A1]` (`b` without the exchange `A101 <-> A11`), all six decrease.
2. **Splitting.** Let `Gamma'_A = <iota_A(x_23(1)), iota_(A1)(D_8), b>`. Then `Gamma_b = M ⋊ Gamma'_A`, where `M` is
   an elementary abelian 2-group: the span of the right `Gamma'_A`-translates of `S[A0]T[A10]` and `S[A0]T[A11]`, in
   the upper-right block of `e_(A0) + e_(A1)`.
   * `Gamma_b` is amenable if and only if `Gamma'_A` is.
   * Stripping `A1` identifies `Gamma'_A` with `<x, y, u, beta>`, where `x = 1 + S[0]T[10]`, `y = 1 + S[10]T[11]`,
     `u = 1 + S[0]T[1]` and `beta = S[00]T[0] + S[01]T[11] + S[1]T[10]`.
   * These lie in `GL_2` over `F_2<s_0, t_0, t_1>`, which is not RFD.
3. **Infinite dihedral pair.** `u_1 = iota_A(x_23(1))` and `u_2 = 1 + S[A11]T[A101]` are involutions, and `u_1 u_2`
   has infinite order: in the frame `(A10, A11)`, the degree `-n` part of its `n`-th power is
   `[[t_1^n, 0],[t_1^n, 0]]`. So `<u_1, u_2> ≅ D_inf`.
4. **Every order.** No subgroup of `R^x` normalized by `b` and containing `iota_A(x_23(1))` and `iota_(A1)(x_23(1))`
   is locally finite.
   * So no order preserved by `b` makes those two roots monotone inside a locally finite group, whether setwise,
     pointwise, piecewise or twisted. This contains multiletter Lemma 6.1.
   * Under `b'` instead, `<iota_A(D_8), iota_(A1)(D_8), b'> <= U_< ⋊ <b'>`. So the escape is the exchange.
5. **Theorem S.** For `B` disjoint from `[A]`, `<Gamma_b, iota_B(D_8)> ≅ Gamma_b × D_8`.
   * `sofic-subgroups-carry-independent-cylinder-defects` applies to it if and only if `Gamma_b` is sofic.
   * Amenability of `<x, y, u, beta>` suffices.
   * A theta < 1 derivation from its relations alone would prove `Gamma_b` nonsofic.

**Open.** Amenability, free subgroups, LEF and soficity of `<x, y, u, beta>`.
