---
rg: 2
id: kms-central-lamp-mixing-cannot-separate-top-core
kind: claim
title: In the product Frobenius–Möbius class, if some counter cycle of the KMS top map f̄ on B_0 does not contract, central lamp mixing (F = f̄·τ on lamps, τ into T_0 of any rank) cannot separate the top core, on any domain, power-type included - the refereed invariant principal ideal of kms-top-every-counter-cycle-must-contract, built with a larger field and exponent L + N', lies in 𝔫J, where τ vanishes, so F = f̄ there
distinct_from:
  kms-lamp-mixing-dies-on-br-relation: that kills central lamp mixing for counter-pair domains via G4; this kills its effect on the core for every domain, power-type included, by choosing the core inside the kernel of the mixing character.
  kms-counter-cocycles-reduce-to-central-lamp-mixing: that reduces counter cocycles to central lamp mixing; this shows central lamp mixing does not separate the top core, so together they close both routes at the lamp level.
  kms-top-every-counter-cycle-must-contract: this reuses its Steps 1–4 with the parameters r and N' enlarged.
  two-counter-kms-groups-are-self-similar: that is the crux KD2_p; this is an attempt record under it.
---

**ESTABLISHED (lane bh-kd2p-2, 2026-09-19; **referee PASS with proof repair**, bh-ref-g, beaeb35b6a): the
theorem stands; the step "the mixing character vanishes on `J ∩ 𝔪_z`" was false in general and is replaced
below, and the mixing map is widened to any rank.** KD2_p stays **OPEN**.
It settles route (B) of `research/artifacts/gq-bh-kd2p-state.md` at the level at which that route was posed: whether the lamp components of the lift separate the top core. The step from the top core to the kernel of the action on the tree (the normal-closure check below) is **not** done here; it is the same check for every lift, mixed or not.

## Setting

- Notation of `kms-configuration-lift-needs-non-contracting-counters` (KMS arXiv:1204.6506v5 §4.1). `F : H → G(M)` is the virtual endomorphism, `f̄` its top map on `B_0 = R_K ⋊ U_0`, and `J = H ∩ R_K` the lamp part of the domain.
- **Product Frobenius–Möbius hypothesis** of `kms-top-every-counter-cycle-must-contract` (refereed PASS, bh-ref-g, 28f69471d1), and some cycle `C` of the counter permutation with `Σ_{i∈C} j_i ≥ 0`. This is exactly the situation a hard lift is in: by G6 the machine counters and the `ã_i` renormalize together (Part 2 of the configuration node), and a hard machine needs non-contracting counters (Part 3 sketch). So `f̄` has a top core, and the `T`-components are supposed to separate it.
- **Route (B).** `F(A_0) = τ·f̄(A_0)` with `τ ∈ T_0`, and the counters go to `ψ(u)` (a central counter twist changes nothing on the torsion part, by `kms-counter-cocycles-reduce-to-central-lamp-mixing` (iii)).
- **The mixing map (repaired per beaeb35b6a).** Since `B_0` fixes `T_0` (refereed Step 1 of
  `kms-lamp-mixing-dies-on-br-relation`), `F(b) = f̄(b)·τ(b)` on lamps, where `τ : J → T_0` is `F_p`-linear with
  `τ(ρ·b) = aug(ρ)·τ(b)` for `ρ ∈ S = F_p[U_H]`. It may have any rank.
- **Where `τ` vanishes.** If `aug` does not factor through `S`, then `τ = 0`. If it does, put `𝔫 = ker(aug|_S)`;
  then `τ` factors through `J/𝔫J` and **vanishes on `𝔫J`**. It need not vanish on `J ∩ 𝔪_z`.
- **The fibre.** `R_K` is finite over `S`, so `R/𝔫R` is a finite (Artinian, possibly non-reduced) `F_p`-algebra.
  Its maximal ideals are the fibre points `z_1, …, z_m`, where every `u ∈ U_H` equals 1, and
  `𝔫R ⊇ ∏_k 𝔪_{z_k}^L` for some `L`.
- **Fibre coordinates.** Each `s_i(z_k)` is a root of unity, and `s_i(z_k) ≠ 1`, since `1 − s_i` is a unit of
  `R_K`.

## Theorem

There is a nonzero ideal `I ⊆ 𝔫J` of `R_K` with `f̄(I) ⊆ I`. On `I`, `F = f̄` for every central mixing map `τ`. So the lamp components of a route-(B) lift vanish on the top core `I`, and do not separate it.

## Proof

- Run Steps 1–4 of `kms-top-every-counter-cycle-must-contract` for the cycle `C`, with two parameters enlarged:
  - **the field.** Take `r` so large that `P^1(F_{p^r})` contains `s_i(z_k)` for every `i ∈ C` and **every**
    fibre point `z_k`, as well as every coordinate of every point of the support `Z` used there.
    `Z_0 = P^1(F_{p^r}) ∖ {0, 1, ∞}` is still stable under Galois and under Möbius maps over `F_p`, which is all
    Step 4 uses. Since `s_i(z_k) ∉ {0, 1, ∞}`, it lies in `Z_0`.
  - **the exponent.** Replace `N'` by `L + N'` (repair 1 of beaeb35b6a). A larger exponent still works, since
    Step 3 needs only `M'' ⊇ ∏_{w∈Z} 𝔪_w^{N'}`.
- Steps 1–4 give `h̃ = ∏_{i∈C} (h^{(i)})^{p^{w_i}}` with `h^{(i)} = ∏_{c∈Z_0}(s_i − c)^{L+N'}`, such that
  `I = h̃R_K` lies in the domain and satisfies `f̄(I) ⊆ I`.
- **`I ⊆ 𝔫J`** (repaired). Fix `i ∈ C`. For each `w ∈ Z ∪ {z_k}`, the minimal polynomial of `s_i(w)` over `F_p`
  (repair 2 of 28f69471d1) appears in `h^{(i)}` with exponent `L + N'`. So `h̃` vanishes to order at least
  `L + N'` at every such point. The ideals of distinct points are comaximal, so
  `h̃ ∈ ∏_k 𝔪_{z_k}^L · ∏_{w∈Z} 𝔪_w^{N'} ⊆ 𝔫R·𝔞 ⊆ 𝔫J`, with `𝔞 = ∏_{w∈Z} 𝔪_w^{N'} ⊆ M'' ⊆ J`.
- **`F = f̄` on `I`.** For `b ∈ I ⊆ 𝔫J`, `τ(b) = 0`, so `F(b) = f̄(b) ∈ I`. This holds for every central mixing
  map `τ`, of any rank. ∎

## What this closes, and what it doesn't

- **Closed.** Together with `kms-counter-cocycles-reduce-to-central-lamp-mixing`, both lamp-level routes (A) and (B) are closed in the product Frobenius–Möbius class, under that node's hypothesis (V) for route (A). Separation by lamp components is impossible whenever the top map has a non-contracting cycle. Power-type domains do not help: `τ ≠ 0` is possible there, but the core can be placed inside `𝔫J ⊆ ker τ`.
- **Not done: the normal-closure check.** The kernel of the action on the tree is the largest normal subgroup `N ⊴ G(M)` with `N ≤ H` and `F(N) ≤ N`. The normal closure of `I` in `G(M)` is `I·[T, I]`, and `[T, I] ⊆ T_0`. Showing `[T, I] ≤ H` and `F([T, I]) ≤ I·[T, I]` needs control of `F` on `H ∩ T`, which is part of the lift not constrained here. This check is identical for a top-preserving lift. So if it fails, the separation is done by `F` on `T` itself, not by any lamp mixing.
- **Still open (remaining cases of KD2_p).**
  - `F` on `H ∩ T`: the normal-closure check above, i.e. whether the configuration part of a lift can separate the top core.
  - Route (A) when (V) fails: all image counters share a common unit point.
  - Lifts that mix into grades other than `T_0`, or into `B_1, …, B_K`.
  - Top maps outside the product Frobenius–Möbius class (tropical rigidity suggests none, per a sketch).
  - `p = 2`.

## Lesson

**The lamps can't do the separating.** Any central lamp mixing vanishes on `𝔫J`, and the refereed core construction has enough freedom to sit inside `𝔫J`. If a hard self-similar KMS lift exists, its configuration part `F|_{H∩T}` must do the separating.
