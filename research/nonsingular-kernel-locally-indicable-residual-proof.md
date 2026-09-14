---
rg: 2
id: nonsingular-kernel-locally-indicable-residual-proof
kind: route
title: Push the equation into each locally indicable quotient and apply Howie
target: nonsingular-coefficient-kernel-in-locally-indicable-residual
requires: [howie-locally-indicable-nonsingular-equations-are-solvable]
---

Let `phi : G -> Q` be a homomorphism with `Q` locally indicable, and let
`g in ker(q)`.

1. **Extend.** Let `Phi : G * <t> -> Q * <t>` extend `phi` by `t -> t`. Let
   `d_G : G * <t> -> Z` and `d_Q : Q * <t> -> Z` kill the coefficients and send
   `t -> 1`. Both `d_Q o Phi` and `d_G` kill `G` and send `t -> 1`, so they are
   equal. Hence `deg_t(Phi(w)) = deg_t(w) != 0`.
2. **Descend.** `Phi` sends each conjugate `u w^(±1) u^(-1)` to the conjugate
   `Phi(u) Phi(w)^(±1) Phi(u)^(-1)`. So `Phi(<<w>>) <= <<Phi(w)>>`, and `Phi`
   induces `Phibar : G_w -> Q_(Phi(w))` with `Phibar o q = q_Q o phi`, where
   `q_Q : Q -> Q_(Phi(w))` is the coefficient map.
3. **Conclude.** `q(g) = 1`, so `q_Q(phi(g)) = Phibar(q(g)) = 1`. By
   `howie-locally-indicable-nonsingular-equations-are-solvable`, `q_Q` is
   injective, since that theorem needs only `deg_t != 0` and no reduction or
   shape hypothesis. So `phi(g) = 1`.

As `phi` was arbitrary, `g in Rad_LI(G)`. If `G` is residually locally
indicable, `Rad_LI(G) = 1`, which gives item 1. Item 2 is the contrapositive,
together with the inclusion `ker(q) <= Rad_MF(G) intersect Rad_hyp(G)` of
`nonsingular-adjunction-preserves-approximation-radicals`.
