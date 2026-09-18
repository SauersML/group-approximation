---
rg: 2
id: leavitt-pair-unit-hosts-contain-their-own-squares
kind: claim
title: In any ring with a Leavitt pair the corner map embeds R x R in R, so unit groups, GL_n and E_n contain their own squares; on Steinberg groups the same map loses exactly one copy of K_2
distinct_from:
  boone-higman-closed-under-finite-direct-products: that is the open closure of the Boone--Higman class under products; this is the elementary self-square property of Leavitt-type hosts, which settles the square case (SQ) inside any such host but not the general closure.
  twisted-btb-clopen-action-is-type-a: that shows SV_G contains SV_G x SV_G as a clopen stabilizer; this is the ring-theoretic analogue for unit groups of rings with a Leavitt pair.
  cuntz-stabilized-full-groups-contain-their-own-squares: that is the groupoid version (full groups of Cuntz-stabilized ample groupoids); this is the ring version (units and elementary groups of rings with a Leavitt pair).
---

**ESTABLISHED** (lane proof, bh-major-product, 2026-09-18; elementary; not independently
reviewed). No priority is claimed: this is the standard Cuntz "two isometries" trick, written
out for the Boone--Higman hosts on main.

## Statement

Let `R` be a unital ring with a Leavitt pair: elements `s_1, s_2, t_1, t_2` with
`t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`. Define
`φ(a, b) = s_1 a t_1 + s_2 b t_2`.

1. **Corner map.** `φ : R × R → R` is an injective unital ring homomorphism.
2. **Self-squares.** It induces injective group homomorphisms
   `R^× × R^× → R^×`, `GL_n(R) × GL_n(R) → GL_n(R)` and `E_n(R) × E_n(R) → E_n(R)`
   (apply `φ` entrywise, with `M_n(R × R) = M_n(R) × M_n(R)`). So for every subgroup `G` of
   one of these groups, `G × G` is a subgroup of the same group, realized by the two commuting
   copies `φ(G, 1)` and `φ(1, G)`.
3. **Projective quotients.** Let `F ⊆ Z(R)` be a field of central scalars and
   `P = R^× / F^×`. If `G ≤ P` lifts isomorphically to a subgroup `G̃ ≤ R^×`, then `G × G ≤ P`.
   The lift always exists when `F = F_2`, since then `P = R^×`. In general `φ(G̃ × G̃)` meets
   `F^×` exactly in the diagonal scalars of `G̃ ∩ F^×`.
4. **Steinberg groups lose one K_2.** `φ` induces `St_n(R) × St_n(R) = St_n(R × R) → St_n(R)`.
   Its kernel lies in `K_2(n,R) × K_2(n,R)`. In the stable range it is the kernel of
   `(x, y) ↦ σ_1(x) + σ_2(y)`, where `σ_i` is induced by the corner map `r ↦ s_i r t_i`. Each
   `σ_i` is an isomorphism, since `s_i t_i` is a full idempotent (`t_i (s_i t_i) s_i = 1`), so
   by Morita invariance the kernel is a copy of `K_2(R)`.
   - For the Leavitt resolvent ring `R_L`, `K_2(n,R_L) ≅ Q^×` for every `n ≥ 3`
     (`leavitt-resolvent-k2-stability-holds`, refereed). So the corner square of
     `St_n(R_L)` is not faithful; the images of `E_n(R_L)` and of the unit group are.

## Proof

1. Additivity is clear, and `φ(1,1) = s_1 t_1 + s_2 t_2 = 1`. For products,
   `φ(a,b) φ(c,d) = s_1 a (t_1 s_1) c t_1 + s_1 a (t_1 s_2) d t_2 + s_2 b (t_2 s_1) c t_1
   + s_2 b (t_2 s_2) d t_2 = φ(ac, bd)`,
   using `t_i s_j = δ_ij`. It is injective because `a = t_1 φ(a,b) s_1` and
   `b = t_2 φ(a,b) s_2`.
2. A unital ring homomorphism maps units to units and elementary matrices `e_ij(r)` to
   elementary matrices. Here `e_ij((r, 0)) ↦ e_ij(s_1 r t_1)` and
   `e_ij((0, r)) ↦ e_ij(s_2 r t_2)`. Injectivity comes from item 1, entrywise. The copies
   `φ(G,1)` and `φ(1,G)` commute because `(g,1)` and `(1,h)` commute in `R × R`.
3. `φ(λ, μ)` is central exactly when `λ = μ`, because it equals `μ + (λ − μ) s_1 t_1` and
   `s_1 t_1` is a non-central idempotent. So `φ(G̃ × G̃) ∩ F^× = {φ(λ,λ) : λ ∈ G̃ ∩ F^×}`,
   and `G̃ ∩ F^× = 1` gives an injection `G × G → P`.
4. `St_n(R × R) = St_n(R) × St_n(R)`, because the relations split along the two
   idempotents. The comparison map to `E_n` is compatible with `φ`, so the kernel of the
   induced map on Steinberg groups sits over the kernel on `E_n`, which is trivial by item 2.
   It therefore lies in `K_2(n, R×R)`. On `K_2`, `φ = φ_1 + φ_2` with `φ_i` the two
   orthogonal corner homomorphisms, and a full corner inclusion induces the Morita
   isomorphism.

## Consequences on main

- **(SQ) inside Leavitt hosts.** Every subgroup `G` of the binary Leavitt unit group
  `L_(F_2)(1,2)^×` (`leavitt-unit-group-finitely-presented`, finitely presented and simple)
  has `G × G` inside the same finitely presented simple group. The same holds for the unit
  group of `L ⊗ L` (`leavitt-square-unit-group-is-fp-simple-and-acyclic`, whose finite
  presentation and simplicity rest on the Khanh and Ara–Cortiñas imports), since `s_i ⊗ 1`
  is a Leavitt pair there.
- **The ring side of the master route.** Its hosts are unit groups `(B ⊗ L)^×` over `F_2`.
  They carry the Leavitt pair `1 ⊗ s_i`, so the class of groups it produces is closed under
  finite direct products with no extra work
  (`boone-higman-via-leavitt-units-of-rigid-sft-overgroups`).
- **Joint embedding across F_2-Leavitt hosts.** Suppose `G_i ≤ (B_i ⊗ L)^×` for `i = 1, 2`.
  The unital maps `B_1 ⊗ L → B_1 ⊗ B_2 ⊗ L` (`x ↦ x` in the first and last factors) and
  `B_2 ⊗ L → B_1 ⊗ B_2 ⊗ L` land in one ring with a Leavitt pair. Their images need not
  commute, but `x ↦ φ(x, 1)` and `y ↦ φ(1, y)` do. So `G_1 × G_2 ≤ (B_1 ⊗ B_2 ⊗ L)^×`.
  This host is finitely presented and simple once `(B_1 ⊗ B_2) ⊗ L` satisfies the K-gate
  of `leavitt-tensor-k-theory-is-carried-by-nil-groups` (K_1 = K_2 = 0). `B_1 ⊗ B_2` is
  finitely presented, and it is central simple when `B_1` and `B_2` are.

## Lesson for general BH

Rings with a Leavitt pair square themselves for free: the Cuntz corner map turns any host into
a host of its own square. So every Leavitt-unit route to Boone--Higman proves closure under
products at no extra cost. The only way a Steinberg-type host fails to self-square is through
`K_2`. That is the same `K_2` which stands between `St_N(R_L)` and a finitely presented simple
quotient.
