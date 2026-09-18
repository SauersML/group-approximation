---
rg: 2
id: ce-relation-full-group-subgroups-hyperlinear-proof
kind: route
title: The full group embeds in the unitary group of the relation factor, which embeds in the hyperfinite ultrapower
target: ce-relation-full-group-subgroups-are-hyperlinear
requires:
  - full-group-subgroup-trace-generation-dichotomy
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

**Step 1 (homomorphism).** For `phi in [R]` let `u_phi in L(R)` be the canonical unitary with Feldman--Moore kernel
the characteristic function of the graph of `phi`. Composition of graphs gives `u_phi u_psi = u_(phi psi)` and
`u_(phi^-1) = u_phi^*`, so `phi -> u_phi` is a group homomorphism `[R] -> U(L(R))`.

**Step 2 (injective).** The route of `full-group-subgroup-trace-generation-dichotomy` computes
`tau_R(v_g)=mu(Fix(g))` for full-group unitaries. Hence

```text
||u_phi - u_psi||_2^2 = 2 - 2 Re tau_R(u_psi^* u_phi) = 2 - 2 mu(Fix(psi^-1 phi)) = 2 mu({x : phi x != psi x}).
```

If `u_phi = u_psi` then `phi = psi` almost everywhere, i.e. `phi = psi` in `[R]`.

**Step 3 (transfer).** Let `theta : L(R) -> R^U` be a trace-preserving unital embedding. It is injective and maps
unitaries to unitaries, so `theta o u` embeds `[R]`, hence every countable subgroup `Lambda <= [R]`, as a subgroup
of `U(R^U)`. By condition 1 of `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower` ("`G` embeds in the
unitary group of a tracial ultraproduct of matrix algebras ... as a subgroup"), `Lambda` is hyperlinear.
