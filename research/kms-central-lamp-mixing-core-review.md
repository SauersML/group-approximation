---
rg: 2
id: kms-central-lamp-mixing-core-review
kind: claim
title: Referee review of kms-central-lamp-mixing-cannot-separate-top-core (bc38115be1) — the theorem is correct, but the proof step "the mixing character vanishes on J ∩ m_z" is false in general, because the character vanishes only on n·J, n the augmentation ideal of S; it is repaired by building the invariant principal ideal inside n·J, i.e. vanishing to high order at every point of the fibre over the augmentation point; the normal-closure gap is correctly flagged
distinct_from:
  kms-central-lamp-mixing-cannot-separate-top-core: that is the lane node reviewed here.
  kms-lamp-mixing-br-relation-review: that review found central lamp mixing not excluded on power-type domains; this node shows it cannot separate the top core there anyway, which is consistent.
  kms-counter-cocycles-review: that review flagged the normal-closure gap this node now states.
---

**ESTABLISHED (referee bh-ref-g, 2026-09-19; review of `kms-central-lamp-mixing-cannot-separate-top-core`,
commit bc38115be1).** Inputs refereed earlier: Steps 1–4 of `kms-top-every-counter-cycle-must-contract` (PASS,
28f69471d1), and the augmentation criterion of `kms-lamp-mixing-dies-on-br-relation` (PASS with scope repair,
28f69471d1).

## Verdict: PASS with a proof repair

The theorem holds: there is a nonzero `f̄`-invariant ideal `I` of `R_K`, inside the domain, on which a
central lamp mixing acts as `f̄`. One step of the proof is wrong, and it is repairable within the node's own
construction.

## Consistency with the earlier review

This node does not contradict my earlier observation that on power-type domains the augmentation factors and a
nonzero central `τ` is not excluded. It concedes that `τ` may be nonzero, and shows that such a `τ` cannot
separate the top core, because the core can be placed inside `ker τ`.

## The general mixing map

- Central lamp mixing on the whole lamp domain `J = H ∩ R_K` is `F(b) = f̄(b)·τ(b)`. Here `τ : J → T_0` is an
  `F_p`-linear map with `τ(ρ·b) = aug(ρ)·τ(b)` for `ρ ∈ F_p[U_H]`, because `T_0` is central and fixed by `B_0`.
- The node writes `τ^{ε(b)}` with a single `τ` and a scalar `ε`. That is the rank-one case. The general `τ` may
  have rank greater than 1, and the argument should allow it.
- `R_K` is a domain, so every nonzero `b` has the same annihilator, the kernel of `F_p[U_H] → S`. If `aug` does not
  factor through `S`, then `τ = 0`. If it does, write `𝔫 = ker(aug|_S)`; then `τ(s·b) = aug(s)·τ(b)`, so `τ`
  factors through `J/𝔫J`.

## The wrong step

**The step.** "`ε` vanishes on `J ∩ 𝔪_z`."

**Why it fails.** In general `τ` vanishes only on `𝔫J`.
- `R_K` is finite over `S = F_p[U_H]`, so `R/𝔫R` is a finite `F_p`-algebra.
- Its maximal ideals are the whole fibre `{z_1, …, z_m}` of points where every `u ∈ U_H` equals 1. For power-type
  domains `R/𝔫R` can also be non-reduced, since `u − 1 = (s − 1)^{p^e}`-type elements are not radical.
- A linear functional on `J/𝔫J` can be nonzero on an element vanishing at `z` but not at another fibre point, or on
  a nilpotent direction at `z`.

**The repair.**
- `R/𝔫R` is Artinian, so `𝔫R ⊇ ∏_k 𝔪_{z_k}^L` for some `L`.
- `J ⊇ M'' ⊇ 𝔞 := ∏_{w∈Z} 𝔪_w^{N'}`, so `𝔫J ⊇ 𝔫·𝔞 = 𝔫R·𝔞 ⊇ ∏_k 𝔪_{z_k}^L · ∏_{w∈Z} 𝔪_w^{N'}`.
- In Steps 1–4, take `r` so large that `Z_0` contains the relevant coordinates of **every** fibre point `z_k` and
  of every point of `Z`. Replace `N'` by `L + N'`.
- Then `h̃` vanishes to order at least `L + N'` at each point of `Z ∪ {z_k}`, through one factor for a fixed
  `i ∈ C`. So `h̃ ∈ ∏ 𝔪^{…} ⊆ 𝔫J ⊆ ker τ`, using that the ideals of distinct points are comaximal.
- Invariance `f̄(h̃R) ⊆ h̃R` is unaffected: Step 4 uses only that `Z_0` is stable under Galois and Möbius maps over
  `F_p`.

So `I = h̃R` satisfies `I ⊆ ker τ`, and `F = f̄` on `I`, for every central mixing map `τ`.

## Scope

- **Normal-closure gap: correctly stated.** The node says explicitly that the step from the top core to the kernel
  of the action on the tree needs control of `F|_{H∩T}`, and does not claim it. This matches my review 941f051f16.
- **"Route (B) closed": correct at the level stated.** Lamp components cannot separate the top core. That applies
  in the product Frobenius–Möbius class, with a non-contracting cycle, for every domain.
- **The remaining list is accurate:**
  - `F|_{H∩T}`;
  - route (A) without (V);
  - other grades;
  - maps outside the class;
  - `p = 2`.

## Repairs

1. Replace "`ε` vanishes on `J ∩ 𝔪_z`" by "`τ` vanishes on `𝔫J`". Build `I` inside `𝔫J` as above: all fibre points
   in `Z_0`, and exponent `L + N'`.
2. Allow a general `τ : J/𝔫J → T_0`, not only rank one.

## Priority

This is internal to KD2_p. I found no external issue.
