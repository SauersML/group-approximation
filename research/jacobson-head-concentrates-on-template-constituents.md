---
rg: 2
id: jacobson-head-concentrates-on-template-constituents
kind: claim
title: In every finite-group unitary or sofic model of a group receiving St_4(J), the Jacobson head lives only on template constituents of a bounded-depth derived subgroup, so products of general linear groups of any number, rank and field kill it
distinct_from:
  jacobson-head-dies-in-gapped-finite-group-models: that needs a groupwise rigid target family, which excludes direct products of two nonabelian groups and GL_d(F_q) for q > 2, and lists unbounded products as a survivor; this works constituent by constituent inside an arbitrary finite target, bounds the head by the defect plus the weight of template constituents of G^(L), and so kills products with any number of factors, over any fields, with abelian and bounded-derived-length extensions
  fp-simple-models-concentrate-on-template-constituents: that is the analogous concentration for a finitely presented infinite simple group, using simplicity to see a commutator of generators; this is for the non-simple, non-finitely-presented EL_n(J), n >= 4, and St_20(L_2(F_2)), sees the head x_13(Q) through the finite residual of St_4(J), gives an explicit linear bound, and allows arbitrary scalar rephasing
  fp-simple-groups-have-no-models-through-classical-products: that is the product-target kill for finitely presented infinite simple groups; this is the product-target kill for the Jacobson head, which lies in a non-simple group
---

**ESTABLISHED** (route `jacobson-head-concentrates-on-template-constituents-proof`, swarm-0917-w9-w9-nh-follow,
2026-09-18, unreviewed).

**Notation.** `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`. `Λ = St_4(J) = <X | R>` is finitely presented. `μ = x_12(Q)`,
`ν = x_23(1)`, `λ = [μ,ν] = x_13(Q)`. `‖·‖_2` is the normalized Hilbert-Schmidt norm and `χ̃_σ = χ_σ/χ_σ(1)`.

**Models.** As on `jacobson-head-dies-in-gapped-finite-group-models`: a group `Γ`, a homomorphism `ι : Λ → Γ`, and
`π(g) = c(g) ρ(φ(g))` with:
- `φ : Γ → G` an arbitrary map into an arbitrary finite group `G`;
- `ρ : G → U(N)` a unitary representation;
- `c : Γ → U(1)` an arbitrary scalar one-cochain.

`z = ι(λ)`. `def_F(π) = max_{g,h ∈ F} ‖π(g)π(h) - π(gh)‖_2`.

**Template constituents.** Fix `L >= 0` and `θ < 1`, and put `H = G^(L)`, the `L`-th derived subgroup. Fixed words
`v_x ∈ F(X)^(L)` with `v_x = x` in `Λ` (they exist because `Λ` is perfect) define a homomorphism `Ψ : F(X) → H`,
`Ψ(x) = v_x(φ(ιy) : y ∈ X)`. Decompose `ρ|_H = ⊕ σ` into irreducible representations of `H`, with weights
`p_σ = dim σ / N`. The constituent `σ` is a *template constituent* if:
- `|χ̃_σ(Ψ(r))| > θ` for every relator `r ∈ R`; and
- `σ(Ψ(r))` is not a scalar for at least one `r ∈ R`.

Write `p_T(θ, L)` for the total weight of the template constituents.

**Theorem.** For every `L >= 0` and `θ < 1` there are a finite set `F_1 ⊆ Γ` and a constant `K`, depending only on `ι`,
`L`, `θ` and fixed words, such that every model satisfies

```text
‖π(z) - 1‖_2 <= K def_{F_1}(π) + 2 sqrt(p_T(θ, L)).
```

**Corollary 1 (head mass is template mass).** Let `π_k` be finite-group models of `Γ` with `def_F(π_k) → 0` for every
finite `F`, and let `τ` be a pointwise limit of `tr∘π_k`. Then for every `L` and `θ < 1`:

```text
liminf_k p_T(θ, L)(π_k) >= (1 - Re τ(z))/2.
```

So a hyperlinear certificate through finite groups that sees the head (`τ(z) ≠ 1`) carries definite weight, at every
depth `L` and every `θ < 1`, on constituents of `G_k^(L)` in which every relator of `St_4(J)` is nearly scalar but some
relator is not a scalar.

**Corollary 2 (constituent-gapped kills).** If every irreducible representation of `G_k^(L)` is θ-gapped (the class
`𝒢_θ` of `constituent-gapped-finite-groups-closed-under-products`), then `p_T = 0` and `‖π_k(z) - 1‖_2 <= K def`. This
covers, with arbitrary scalar rephasing and with permutation representations (sofic models):
- `L = 0`: quotients of `∏_{i<=m} Γ_i × A` with `Γ_i` finite quasi-simple classical, `A` abelian and `m` unbounded;
- `L = 4`: `∏_{i<=m} GL_{N_i}(F_{q_i})` in any ranks, over any finite fields, with any number of factors. This includes
  `q > 2`, which the gapped theorem does not claim;
- any fixed `L`: extensions of such products by groups of derived length `<= L`, for example `∏ GL_{N_i}(q_i) ⋊ P` with
  `P` of derived length `<= L - 4` permuting isomorphic factors.

These apply to `Γ = EL_n(J)`, `n >= 4` (in particular `EL_20(J)`, the Toeplitz decision point of
`agent-leavitt-not-bcs-negative-root-corner`), to `Δ = St_20(L_2(F_2))` with `z = x_13(s_1 t_1)`, and to every overgroup.

**What it removes.** The "unbounded products" survivor recorded on `jacobson-head-dies-in-gapped-finite-group-models`,
and its `GL_d(F_q)`, `q > 2`, exclusion. Block-diagonal truncation models of every kind, tensor products of truncation
models at several levels, and Weil or permutation modules of products of classical groups all kill the head.

**What survives.** Finite-group certificates of `EL_20(J)` must put their head mass on template constituents of
`G^(L)` for every `L`. By `constituent-gapped-finite-groups-closed-under-products` (e) and
`template-constituents-primitive-or-small-minimal-degree`, the natural source is subgroups of classical groups that are
not gapped, such as alternating groups acting on their deleted permutation modules. The theorem says nothing about
unitary models that are not scalar multiples of representation images of finite groups.

DERIVATION
jacobson-head-concentrates-on-template-constituents-proof
