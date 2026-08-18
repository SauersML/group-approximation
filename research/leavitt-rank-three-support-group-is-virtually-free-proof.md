---
rg: 2
id: leavitt-rank-three-support-group-is-virtually-free-proof
kind: route
title: Rewrite the units as a Klein four-group and a rotation, then read Nagao's amalgam
target: leavitt-rank-three-support-group-is-virtually-free
requires: [leavitt-rank-three-unit-lift]
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

## Direct proof

The prerequisite supplies the self-similarity `Psi : M_2(R) -> R` and the
matrices `U_i`, `V_i`; `Psi` is a ring isomorphism, so it identifies
`<U_1,U_2,U_3>` with `K` and `<V_1,V_2,V_3>` with `K_s`.  Full computations in
`research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md`, sections
1--2.

**Step 1 — a Klein four-group and a rotation.**  `r = U_3` has `r^3 = I` in
characteristic two.  Multiplying out, `q_0 = U_2U_3 = [[1,t_0],[0,1]]` and
`q_1 = U_3^(-1)U_1U_3 = [[1,t_1],[0,1]]`.  Upper unitriangular `2x2` matrices
over any ring commute and are involutions in characteristic two, and `t_0`,
`t_1`, `t_0+t_1` are nonzero, so `<q_0,q_1> = C_2 x C_2`.  From
`U_2 = q_0r^(-1)` and `U_1 = rq_1r^(-1)`, `<U_1,U_2,U_3> = <q_0,q_1,r>`, so
there is a surjection `(C_2 x C_2) * C_3 ->> <U_1,U_2,U_3>`.

**Step 2 — the t-subalgebra is free.**  Grade by `deg s_i = 1`, `deg t_i = -1`;
the relations are homogeneous.  For equal-length words `t_alpha s_beta =
delta_(alpha beta)`, so a vanishing combination of length-`n` `t`-words is
killed coefficient by coefficient on right multiplication by `s_beta`.  Hence
`F_2<t_0,t_1>` is free, and symmetrically so is `F_2<s_0,s_1>`.

**Step 3 — specialize and apply Nagao.**  Freeness makes
`sigma : t_0,t_1 |-> X,X^2` a well-defined algebra map into `F_2[X]`, and the
group `<q_0,q_1,r>` has all its elements and inverses with entries in
`F_2<t_0,t_1>`, so `sigma` induces a group homomorphism into `GL_2(F_2[X])`.
Nagao's theorem — H. Nagao, *On GL(2,K[x])*, J. Inst. Polytech. Osaka City
Univ. Ser. A **10** (1959) 117--121, and Serre, *Trees*, II.1.6 — gives
`GL_2(F_2[X]) = GL_2(F_2) *_(B(F_2)) B(F_2[X])`.  The image of `<q_0,q_1>`
lies in `B(F_2[X])` and meets `B(F_2)` trivially (upper-right entries
`X, X^2, X+X^2` are non-constant); `<R_0> = C_3` lies in `GL_2(F_2)` and meets
the order-two group `B(F_2)` trivially.  So every nonempty alternating word is
reduced, the normal form theorem forbids it from being the identity, and the
image is `(C_2 x C_2) * C_3`.  The composite from the free product matches
generators, hence is an isomorphism, hence the surjection of Step 1 is
injective.

**Step 4 — the s-side and the corner element.**  `V_2V_3 = [[1,s_0],[0,1]]`
and `V_1 = [[1,s_1],[0,1]]`, so `<V_1,V_2,V_3>` has the identical shape and
Step 3 runs verbatim with `s_0,s_1 |-> X,X^2`.  For item 3,
`Phi(s_0t_1) = E_12` and `Phi(s_1t_0) = E_21`, so
`Phi(g) = (I+E_12)(I+E_21) = [[0,1],[1,1]] = U_3` and `g = u_3`.

**Step 5 — residual finiteness.**  Both groups are finitely generated linear
groups over `F_2[X]`, a finitely generated commutative ring, so Malcev's
theorem makes them residually finite.  (Free products of finite groups are
residually finite and virtually free, which gives the same conclusion; the
linear embedding is used because Step 3 already produced it.)

## Scope

Nagao's theorem and Malcev's theorem are classical and are cited, not
reproved.  Nothing here is asserted about subgroups of `G` other than these
two, and the free-product structure is claimed only for the specific
generators of `leavitt-rank-three-unit-lift`.
