---
rg: 2
id: projective-leavitt-tensor-units-lie-in-the-permutational-class
kind: claim
title: For every prime p and every d, the unit group of L_p^(⊗d) and its simple quotient by the scalars lie in B_A; the scalars are killed inside L_p^(⊗2d) by u ↦ u ⊗ (u*)^(-1)
distinct_from:
  leavitt-square-unit-groups-mod-scalars-satisfy-pbh: that already puts (L_p ⊗ L_p)^x / F_p^x in B_A (09-13), through a type (A) action on the lines of the tensor-square Chen module, with no passage to degree 4; this treats every degree d by the doubling map, and is new only for d >= 3.
  leavitt-unit-groups-mod-scalars-satisfy-pbh: that is the degree-one case L_p^x / F_p^x (09-13), through the Chen module; this recovers it by doubling into degree 2.
  leavitt-tensor-unit-groups-lie-in-the-permutational-class: that is the unit group of L_p ⊗ L_p only, and it leaves the simple quotient by F_p^x open at odd p; this treats every tensor degree d and puts the quotient R_d^x / F_p^x in B_A as a subgroup of the unit group in degree 2d.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that makes (B ⊗ L_p)^x finitely presented and simple modulo scalars; this places the simple quotients of the Leavitt tensor powers in B_A.
  char-p-linear-groups-satisfy-permutational-boone-higman: that is PBH for positive-characteristic linear groups through self-similar polynomial hosts, reviewed; item 4 here is a second route to the same statement through Leavitt tensor units, and adds nothing new about those groups.
  leavitt-pair-unit-hosts-contain-their-own-squares: that gives (SQ) inside a host by the corner map, and at odd p it yields only (R^x x R^x)/Δ(F_p^x); this gives B_A membership of the quotient, hence (SQ) and (JE) for it.
requires:
  - leavitt-tensor-unit-groups-lie-in-the-permutational-class
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees
  - orbit-finite-affine-actions-are-type-a
  - boone-higman-type-a-class-closed-under-finite-extensions
  - char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
---

**ESTABLISHED** (lane proof, bh-major-product, 2026-09-18; not independently reviewed; no
priority claimed). It carries the same conditions as its inputs:
- Khanh's unrefereed preprint arXiv:2609.08428, through
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`;
- the lane derivation `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`, which
  uses the Farrell–Jones conjecture for `Z^(d−1)`;
- Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858, Corollary 4.11.

## Statement

Let `p` be a prime, `L_p = L_(F_p)(1,2)`, `R_d = L_p^(⊗d)` for `d >= 1`, `Q_d = R_d^x / F_p^x`,
and `M_d = C(C^d, F_p)`.

1. `M_d ⋊ R_d^x` is finitely presented, and its affine action on `M_d` is of type (A). So
   `R_d^x` and all its subgroups lie in `B_A`.
2. `ρ(u) = u ⊗ (u^*)^(-1)` is a homomorphism `R_d^x → R_(2d)^x` with kernel exactly `F_p^x`.
   Here `*` is the involution with `s_i^* = t_i` in each factor. So `Q_d ≤ R_(2d)^x`, and
   `Q_d ∈ B_A`.
3. `Q_d` is finitely presented and simple, by part 4 of
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = L_p^(⊗(d−1))`.
   - So every odd-prime Leavitt host lies in `B_A`, including bh-free-26's
     `(L_p ⊗ L_p)^x / F_p^x`.
   - `Q_d x Q_d` and `Q_d x G`, for any `G ∈ B_A`, lie in `B_A` and embed in finitely presented
     simple groups. That is (SQ), and (JE) with every `B_A` group.
4. A second route to `char-p-linear-groups-satisfy-permutational-boone-higman`. For finitely
   generated `H ≤ GL_n(K)` with `char K = p`, `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups`
   gives `H ≤ E_M(R_(d+1)) ≤ GL_M(R_(d+1)) ≅ R_(d+1)^x`, through the ring isomorphism
   `M_M(R) ≅ R` given by an `M`-leaf prefix code in the last factor. So `H ∈ B_A` by item 1.

## Proof

**Item 2.**
- **The involution.** On `L_p`, `*` is the `F_p`-linear anti-automorphism with `s_i ↦ t_i` and
  `t_i ↦ s_i`. It respects the relations: `(t_i s_j)^* = t_j s_i = δ_ij`, and
  `(s_0 t_0 + s_1 t_1)^* = s_0 t_0 + s_1 t_1`. On `R_d` take the tensor product of these
  anti-automorphisms, which is again an anti-automorphism because the factors commute.
- **Homomorphism.** `u ↦ (u^*)^(-1)` is a homomorphism `R_d^x → R_d^x`, because
  `((uv)^*)^(-1) = (u^*)^(-1)(v^*)^(-1)`. In `R_d ⊗ R_d = R_(2d)` the two tensor factors commute,
  so `ρ(u)ρ(v) = uv ⊗ (u^*)^(-1)(v^*)^(-1) = ρ(uv)`.
- **Kernel.** Suppose `u ⊗ (u^*)^(-1) = 1 ⊗ 1`. Over a field, equal nonzero pure tensors have
  proportional factors, so `u = λ·1` with `λ ∈ F_p^x`. Conversely `ρ(λ) = λ ⊗ λ^(-1) = 1`.
- On permutation units, `ρ(u_g) = u_g ⊗ u_g`, the diagonal copy of `dV` in `2dV`.

**Item 1.** This is the proof of `leavitt-tensor-unit-groups-lie-in-the-permutational-class`,
with `2V` replaced by Brin's `dV` and the square by the `d`-cube. Each step is checked for
general `d` below.

- **Finite presentation and `E_5` of `R_d^x`.** `B = L_p^(⊗(d−1))` is a simple, finitely
  presented unital `F_p`-algebra; for `d = 1` it is `F_p`. It is simple because
  `Z(L_p) = F_p` (`leavitt-center-is-coefficient-field`) and tensor products of central simple
  algebras are central simple. It is finitely presented by `4(d−1)` generators, `p`, the
  Leavitt relators of each factor and the commutators between factors.
  `K_*(R_d) = 0` (`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`). So parts
  2–3 of the host theorem give that `R_d^x` is finitely presented and
  `R_d^x ≅ GL_5(R_d) = E_5(R_d)`. The isomorphism is conjugation by the Leavitt isometries
  `σ_i = 1 ⊗ … ⊗ s_(u_i)` of a 5-leaf prefix code in the last factor.
- **Faithful module and `dV`.**
  - `R_d` acts on `M_d` by the tensor power of the Cantor representation. The action is
    faithful because `R_d` is simple.
  - A brick bijection `g ∈ dV` gives the monomial unit `u_g`, and `g ↦ u_g` embeds `dV` in
    `R_d^x`.
- **G1: `M_d ⋊ dV` is `F_∞`.**
  - Let `ρ_0 ∈ dV` be the free order-`p` element that cycles the bricks `[u_k] x C^(d−1)` of a
    `p`-leaf prefix code in the first coordinate.
  - The centralizer computation of the `d = 2` node uses only brick maps and the first
    coordinate. It gives `C_(dV)(ρ_0) ≅ C(B_0, Z/p) ⋊ dV(B_0) ≅ M_d ⋊ dV`.
  - MMN Corollary 4.11 covers Brin's `sV_n` for every `s`, by their Example 2.7(ii) and
    Remark 2.15. With `s = d` and `n = 2`, `C_(dV)(ρ_0)` is `F_∞`.
- **G2: generation.**
  - `E_5(R_d)` is generated by the `e_ij(r)` with `r` in `Γ_d`, which is `1` together with the
    `4d` elements `s_a`, `t_a` of the separate factors. This uses
    `e_ij(rr') = [e_ik(r), e_kj(r')]` for a third index `k`.
  - Under the isomorphism, each generator is `x = 1 + y` with `y = σ_i r τ_j` a monomial.
  - So `y` is a brick bisection `φ : E → D`. Here `E ∩ D = ∅`, since the last coordinates lie
    under the distinct leaves `u_i` and `u_j`. Hence `y^2 = 0` and `x^(-1) = x^(p−1)`.
  - `Y = C^d ∖ (D ∪ E)` contains `C^(d−1) x [u_k]` for `k ∉ {i, j}`, so it is nonempty.
- **G2′: six relators per generator.**
  - `C_x ⊇ dV(D) x dV(Y)` acts by `h` on `D`, by `φ^(-1) h φ` on `E` and by `k` on `Y`, and it
    commutes with `x`.
  - `dV(D)` and `dV(Y)` are transitive on proper nonempty clopen subsets. Every clopen set is
    a finite union of bricks, and a brick splits into two bricks, so any two nonempty clopen
    sets are joined by brick bijections.
  - So `C_x` has six orbits on the additive generators `1_A` of `M_d` with `A` inside `D`,
    `E` or `Y`, and the six relators of the `d = 2` node force the conjugation action of `x`.
- **Assembly and type (A).**
  - `((M_d ⋊ dV) *_(dV) R_d^x) / ⟨⟨ 6·20·(4d+1) relators ⟩⟩ ≅ M_d ⋊ R_d^x`, verbatim.
  - `dV` has at most `2^p − 1` orbits on `M_d`, given by the pattern of nonempty level sets.
  - `orbit-finite-affine-actions-are-type-a` item 3 applies.

**Items 3–4.**
- `B = L_p^(⊗(d−1))` is central simple, so part 4 of the host theorem makes `Q_d` simple.
  `Q_d` is finitely presented as the quotient of a finitely presented group by a finite
  normal subgroup.
- `B_A` is closed under subgroups and finite direct products
  (`boone-higman-type-a-class-closed-under-finite-extensions`), and every `B_A` group embeds in
  a finitely presented simple group. ∎

## Lesson for general BH

The permutational class is not closed under quotients, but on ring-side hosts this costs
exactly one doubling of the tensor degree. The central scalars are the only kernel, and the
pure-tensor map `u ↦ u ⊗ (u^*)^(-1)` kills them with no other loss. This is the Leavitt form
of `PGL_n ↪ GL_(n^2)`, made possible because Leavitt tensor powers are closed under `⊗` and
under `op` (by the involution).

So for every Leavitt-tensor host on main, PBH is exactly finite presentation of the unit
group. Together with the group-side full-group criterion, every host machine on main now
yields the permutational form for free. Any separation of BH from PBH (BFFHZ Question 3.4)
has to come from a finitely presented simple group that is built by neither machine.

## Referee (bh-ref-misc, 2026-09-18): PASS, conditional as stated; one condition is sharper than it reads

Internal referee lane, not an external review.

**Checked.**
- **Item 2.**
  - `*` respects the Leavitt relations (`(t_i s_j)^* = t_j s_i`, `(Σ s_i t_i)^* = Σ s_i t_i`), and a
    tensor product of anti-automorphisms of commuting factors is an anti-automorphism.
  - `u ↦ (u^*)^(-1)` is a homomorphism of unit groups.
  - `u ⊗ w = 1 ⊗ 1` over a field forces `u ∈ F_p^x`.
  - `u_g^* = u_(g^(-1))`, so `ρ(u_g) = u_g ⊗ u_g`.
- **Item 1 for general `d`, step by step against the `d = 2` node.**
  - `B = L_p^(⊗(d−1))` is finitely presented and central simple. A central simple algebra tensored
    with a simple algebra is simple in any dimension, and `Z(A ⊗ B) = Z(A) ⊗ Z(B)`. These are the
    three properties that `khanh-ara-cortinas-hypotheses-hold-for-leavitt-tensor-hosts` ("Beyond
    `B = L_p`") says the host theorem uses.
  - MMN: Example 2.7(ii) is `s` colours of arity `n`, i.e. Brin's `sV_n`, valid and bounded;
    Remark 2.15 says Brin-like algebras are complete; Corollary 4.11 then applies. These are the
    quotes in `research/artifacts/leavitt-module-fp-2026-09-13.md`, so `s = d` is covered.
  - The centralizer computation uses only the first coordinate.
  - G2: `y² = 0` and `x^(-1) = x^(p−1)`.
  - G2′: two nonempty clopen sets are joined by brick bijections after splitting bricks. This is
    more elementary than the `d = 2` node's groupoid argument, and correct.
  - The assembly is the same as for `d = 2`.
  - Type (A): the orbit count `2^p − 1` from level-set patterns, and item 3 of
    `orbit-finite-affine-actions-are-type-a`.
- **Items 3–4.**
  - `Q_d` is finitely presented because its kernel is finite and central.
  - Simplicity is part 4 of the host theorem under `K_1 = K_2 = 0`.
  - Item 4 (the second route for char `p`) was not re-checked; its input
    `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` was not read.

**Gap: the condition is sharper than it reads.** The headline case, the odd-`p` host
`(L_p ⊗ L_p)^x / F_p^x`, uses item 1 in degree `2d = 4`. So it needs `K_1 = K_2 = 0` for `L_p^(⊗4)`.
- That comes only from `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`, an unreviewed
  lane derivation.
- Its step on regular coherence of the Laurent extensions `C[Z^m]` is flagged there as not stated in
  the literature (Bartels–Lück record it as open in general).
- The Ara–Cortiñas regular-supercoherence audit covers `L_p ⊗ L_p` and not `L_p^(⊗4)`.

So every odd-prime conclusion here depends on three things: that derivation, Khanh's unrefereed
preprint, and MMN. **Recommended next review: the regular-coherence step (Step 3.2) of
`leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`.**

## Relation to the 09-13 Chen-module nodes (bh-major-product, 2026-09-18, after the referee)

This node was written without noticing two nodes already on main since 09-13:
- `leavitt-unit-groups-mod-scalars-satisfy-pbh` (`d = 1`);
- `leavitt-square-unit-groups-mod-scalars-satisfy-pbh` (`d = 2`).

They put `L_p^x / F_p^x` and `(L_p ⊗ L_p)^x / F_p^x` in `B_A` through type (A) actions on the
lines of Chen modules. Those actions are on the groups themselves, and they never pass through
`L_p^(⊗2d)`.

So the referee's sharper condition applies only to the cases `d >= 3`. For the headline odd-`p`
hosts of degree `d <= 2`, `B_A` membership needs only the inputs of the 09-13 nodes, and not
`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`.

What is new here:
- item 2 and its consequence for `d >= 3`;
- item 1 for `d >= 3`, and for the unit groups `R_d^x` themselves (not modulo scalars) at odd
  `p`.

Attempt 14 of `boone-higman-closed-under-finite-direct-products` listed the odd-prime hosts as
uncovered. That was already wrong on 09-13.
