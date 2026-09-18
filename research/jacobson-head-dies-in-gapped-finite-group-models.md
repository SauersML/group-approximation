---
rg: 2
id: jacobson-head-dies-in-gapped-finite-group-models
kind: claim
title: Every almost-homomorphism through representations of a gapped finite-group family, even with arbitrary scalar rephasing, kills the Jacobson head x_13(Q) in any group that receives St_4(J)
artifacts:
  - experiments/gapped-head-bound-2026-09-17/check_commutator_rigidity.py
distinct_from:
  fp-simple-groups-have-no-gapped-finite-unitary-models: that needs the approximated group to be finitely presented, infinite and simple, and uses no scalar rephasing; this works in any group receiving a homomorphism from the finitely presented St_4(J), with an explicit linear bound on the head, and allows an arbitrary scalar one-cochain on top of the representation, so it applies to the non-simple EL_n(J), n >= 4, where the simple-group argument has nothing to act on.
  transvection-floor-kills-ambient-rank-transfers: that is the rank-floor theorem for representations of SL_n(F_q) in cross characteristic, applied to rank-model transfers; this uses it (together with a commutator trick) only to show that GL_d(F_2), d >= 5, is Hilbert-Schmidt rigid, and then kills the head.
  jacobson-mirror-head-swap-kills-ambient-approximations: that kills approximations inherited from an overgroup in which the mirror head is conjugate to the head; this kills every model whose matrices are, up to scalars, representation images of a gapped finite group, with no overgroup or swap involved.
  cohn-elementary-group-is-not-lef: that shows EL_n(J) has no exact local embedding into finite groups; this upgrades the same Steinberg chain from exact finite images to approximate unitary models through gapped groups, where the maps into the groups need not be multiplicative anywhere.
  binary-gl-finite-sections-have-no-projective-k2-phase: that rules out genuine Schur-multiplier phases on GL_m(F_2) and leaves relator-dependent scalar one-cochain perturbations open; this closes those, for every m >= 5 and every map into GL_m(F_2).
  projective-jacobson-multipliers-have-a-linear-head-bound: that bounds the head for unitary tuples whose relators are block-central; this derives centrality of the defects from the character-ratio gap of the target group and handles non-central defects separately.
---

**ESTABLISHED** (route `jacobson-head-dies-in-gapped-finite-group-models-proof`, swarm-0917-w9-w9-ptm-pull, 2026-09-18, unreviewed).

Let `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`. `‖A‖_2² = tr(A*A)` is the normalized Hilbert-Schmidt norm, so
`‖U - 1‖_2² = 2 - 2 Re tr U` for a unitary `U`.

**Models.** Let `Γ` be a group and `𝒢` a class of finite groups. A *`𝒢`-model* of `Γ` is a map
`π(g) = c(g) ρ(φ(g))`, where:
- `φ : Γ → G` is an arbitrary map (not assumed multiplicative anywhere) into some `G ∈ 𝒢`;
- `ρ : G → U(N)` is a unitary representation;
- `c : Γ → U(1)` is an arbitrary scalar one-cochain (`c ≡ 1` is the plain case).

For finite `F ⊆ Γ`, `def_F(π) = max_{g,h ∈ F} ‖π(g)π(h) - π(gh)‖_2`.

**Rigidity.** `𝒢` is *`C`-rigid* if for every `G ∈ 𝒢`, every unitary representation `ρ` of `G`, every noncentral
`D ∈ G`, every `λ ∈ U(1)` and every `y ∈ G`:

```text
‖ρ(y) - 1‖_2 <= C ‖ρ(D) - λ‖_2.                                        (R)
```

- (R1) A θ-gapped family (definition on `fp-simple-groups-have-no-gapped-finite-unitary-models`) is
  `C`-rigid with `C = sqrt(2/(1-θ))`. By `lst-quasisimple-classical-character-ratio-bound`, all finite
  quasi-simple classical groups together are `C`-rigid with `C = sqrt(2/(1 - 2^(-1/481))) < 37.3`.
- (R2) `{GL_d(F_2) : d >= 5}` is `8√2`-rigid, by a two-step commutator reduction to a transvection plus the
  transvection floor of `transvection-floor-kills-ambient-rank-transfers`. This does not use Larsen-Shalev-Tiep.

**Theorem 1 (dichotomy, any group).** Let `𝒢` be `C`-rigid, `F ⊆ Γ` finite and `π = c·ρ∘φ` a `𝒢`-model. Then one of
the following holds.
- (a) Every defect `φ(g)φ(h)φ(gh)^(-1)`, `g, h ∈ F`, is central in `G`.
- (b) `‖ρ(y) - 1‖_2 <= C def_F(π)` for every `y ∈ G`. When `c ≡ 1`, this gives `‖π(g) - 1‖_2 <= C def_F(π)` for every `g ∈ Γ`.

**Corollary 1 (LEF).** Let `𝒢` be `C`-rigid with trivial centers, for example `GL_d(F_2)`, `d >= 5`, or the finite
simple classical groups. Suppose a group `Γ` has plain (`c ≡ 1`) `𝒢`-models `π_k` with `def_F(π_k) → 0` for every finite `F` and
`liminf ‖π_k(g) - 1‖_2 > 0` for every `g ≠ 1`. Then `Γ` is LEF.

This is the unitary analogue of `gap-sofic-approximations-are-local-embeddings`, and it holds for any group.

**Theorem 2 (head bound).** Let `Λ = <X | R>` be finitely presented, and let `ι : Λ → Γ` be a homomorphism. Let
`μ ∈ Λ` be killed by every homomorphism from `Λ` to a finite group, let `ν ∈ Λ` be arbitrary, and put `λ = [μ,ν]`.

There is a finite set `F_1 ⊆ Γ`, depending only on `ι` and on fixed words for the relators, `μ` and `ν`, with the
following property. Every `𝒢`-model `π` of `Γ`, for `C`-rigid `𝒢`, satisfies

```text
‖π(ιλ) - 1‖_2 <= (7 + 8C) def_{F_1}(π),
```

and `‖π(ιλ) - 1‖_2 <= max(7, C) def_{F_1}(π)` when `c ≡ 1`.

**Corollary 2 (the Jacobson head).** Take `Λ = St_4(J)`, which is finitely presented, with `μ = x_12(Q)`,
`ν = x_23(1)` and `λ = x_13(Q)`. By the Steinberg chain of `cohn-elementary-group-not-lef-proof`, every finite
image of `St_4(J)` kills `x_12(Q)`. So for every group `Γ` with a homomorphism `ι : St_4(J) → Γ`, and `z = ι(x_13(Q))`:
- every sequence of `𝒢`-models with `def_F → 0` on finite sets has `‖π_k(z) - 1‖_2 → 0`;
- every trace on `Γ` that is a pointwise limit of `tr∘π_k` for such models has `τ(z) = 1`.

This applies to:
- `Γ = EL_n(J)`, `n >= 4`, including `EL_20(J) ≅ E_20(T_2)`;
- `Δ = St_20(L_2(F_2))`, with `z = x_13(s_1 t_1)`, via the unital ring map `S ↦ s_2`, `T ↦ t_2`, which sends `Q` to `s_1 t_1`;
- any overgroup of these.

The kernel `{τ = 1}` is normal, so every such trace factors through `Γ/<<z>>`. For `EL_n(J)`, where
the normal closure of `z` contains the simple finitary kernel `GL_fin` of the symbol sequence, this is the symbol quotient.

**What it kills.** No hyperlinear approximation of `EL_20(J)`, and no approximation of it or of `Δ` that sees the head
(`τ(z) ≠ 1`), is a `𝒢`-model for a rigid `𝒢`, even after arbitrary relator-dependent scalar rephasing. This includes:
- representations of `GL_d(F_2)` of every kind, fed by any map into them: window or Toeplitz truncations, periodic
  and bilateral finite models landing in `GL_d(F_2)`, and permutation modules on vectors, subspaces and flags (the
  configuration and Haar-type permutation models);
- Weil representations and all rank-model transfers through the ambient group;
- representations of any family of finite quasi-simple classical groups.

The mark on the `EL_20(J)` decision point of `agent-leavitt-not-bcs-negative-root-corner` can therefore only be
certified through:
- targets with no uniform gap (alternating or symmetric groups of unbounded degree, or unbounded products); or
- unitary models that are not scalar multiples of a finite-group representation image.

**Calibrations.**
- Four indices are used exactly through the finite presentation of `St_4(J)`. At three indices, the LEF parabolics
  `J^2 ⋊ EL_2(J)` reported on the bus (`jacobson-rank-three-parabolics-are-lef`, swarm-0917-w9-w9-ptl-pull) keep the
  head alive at `√2` through exact embeddings into `GL(F_2)`. The theorem is silent there, because there is no
  `St_4(J)` source.
- `SL_3(Z)` has plain gapped models (its congruence quotients). It is not the target of any homomorphism from `St_4(J)`
  carrying a nontrivial head, which is consistent.
- `experiments/gapped-head-bound-2026-09-17/check_commutator_rigidity.py` checks, exactly over `F_2`:
  - the commutator formula of the rigidity step for random `D` in `GL_d(F_2)`, `d = 5, 6, 7`;
  - the inequalities of (R2) on the vector, plane and flag permutation modules of `GL_5(F_2)`.

**Not claimed.** Products of unboundedly many gapped factors (compare
`fp-simple-groups-have-no-models-through-classical-products`), `GL_d(F_q)` for `q > 2`, and models that are not
scalar multiples of representation images.

DERIVATION
jacobson-head-dies-in-gapped-finite-group-models-proof
