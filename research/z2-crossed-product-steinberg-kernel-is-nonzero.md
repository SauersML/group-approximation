---
rg: 2
id: z2-crossed-product-steinberg-kernel-is-nonzero
kind: claim
title: Over a Z^2 crossed product of a commutative ring, the commutator of h_12(u_1) and h_13(u_2) is a nontrivial element of every unstable Steinberg kernel
distinct_from:
  binary-cantor-ring-stable-steinberg-group-centrally-closed: that is d = 1, where K_2(LC(X,F_2) ⋊ Z) vanishes; this is d = 2, where two commuting translations give a nonzero class in K_2(n,R) for every n >= 3 and in K_2(R).
  subshift-elementary-groups-are-steinberg-groups-in-finite-rank: that asks whether St_n = EL_n for the d = 1 subshift ring; this proves that St_n -> EL_n is never injective for Z^2 crossed products, in any rank.
  rigid-sft-elementary-group-mod-centre-is-fp: that is gate (b), finite normal generation of K_2(n,R) for a rigid free minimal Z^2-SFT; this only shows that the kernel is nonzero, so gate (b) cannot be closed by vanishing.
artifacts:
  - research/artifacts/z2-crossed-product-steinberg-kernel-nonzero-2026-09-16.md
---

Let `A` be a nonzero commutative unital ring with an action of `Z^2`, and let `R = A ⋊ Z^2` with
translation units `u_1, u_2`. Put `D_1 = diag(u_1, u_1^(-1), 1, ..., 1)` and
`D_2 = diag(u_2, 1, u_2^(-1), 1, ..., 1)`.

For `n >= 3` let `c_n = [h_12(u_1), h_13(u_2)] ∈ St_n(R)`. Then:
- `c_n ∈ K_2(n,R) = ker(St_n(R) -> E_n(R))`;
- `c_n` has infinite order, or order a multiple of the additive order of `1_A`;
- in particular `K_2(n,R) ≠ 0` and `St_n(R) -> E_n(R)` is not injective;
- the image of `c_n` in `K_2(R)` has the same property.

**The invariant.** For `n >= 5` there is `sigma: St_n(R) -> A` with the following properties:
- its restriction to `K_2(n,R)` is a homomorphism invariant under conjugation by `St_n(R)`;
- `sigma([x,y]) = -1` whenever `x` lifts `D_1` and `y` lifts `D_2`.

`sigma` comes from the explicit Hochschild 2-cocycle `tau` on `R` given by
`tau(a_0u_(g_0) ⊗ a_1u_(g_1) ⊗ a_2u_(g_2)) = [g_0+g_1+g_2 = 0] · N(g_1,g_2)~(a_0 · alpha_(g_0)(a_1) · alpha_(g_0+g_1)(a_2))`,
with `N(g,h) = P_1(h_1) t_2^(h_2) P_2(g_2) ∈ Z[Z^2]` built from quantum integers.

**Over Cantor systems.** For `R = LC(Ω, F_q) ⋊ Z^2`, with `Ω` any Cantor `Z^2`-system, the kernel
`K_2(n,R)` is nonzero for every `n >= 3`.

**Scope.** The method is a hands-on form of the classical Dennis trace `K_2 -> HH_2` applied to the
symbol of two commuting units. The claim makes no novelty claim beyond this explicit statement over
twisted `Z^2` crossed products. It detects `c_n` only modulo the additive order of `1_A`, so over
`F_q` it does not prove infinite order.
