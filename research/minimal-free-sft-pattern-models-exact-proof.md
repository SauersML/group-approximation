---
rg: 2
id: minimal-free-sft-pattern-models-exact-proof
kind: route
title: Valid colourings map equivariantly into the SFT, and freeness plus minimality transfer relations in both directions
target: minimal-free-sft-full-group-pattern-models-are-exact
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

## Why sufficient

Notation is as in the claim. Fix a validly coloured `Z^d`-set `(Ω, c)` and put `π(ω) = x_ω`, where `x_ω(μ) = c(μ·ω)`.

1. **`π` lands in `X` and is equivariant.**
   - `x_{λ·ω}(μ) = c((μ+λ)·ω) = x_ω(μ+λ)`, so `x_{λ·ω} = λ·x_ω`.
   - The `K`-pattern of `x_ω` at `ν` is `κ ↦ c(κ·(ν·ω))`, which is the pattern at the point `ν·ω`. That pattern is allowed.
   - So `x_ω` shows no forbidden pattern anywhere. Since `X` is the SFT cut out by these forbidden patterns, `x_ω ∈ X`.
2. **`Ω` is free.** If `λ·ω = ω` then `λ·x_ω = x_ω`, so `λ = 0` by freeness on `X`. Free `Z^d`-orbits are infinite. This is item 2.
3. **Rules are local.** `f_s` is continuous with finitely many values on the compact space `X`. Its level sets are clopen, so each is a finite union of cylinders. So `f_s(x)` depends only on `x|_{B_R}` for some `R`, and `s_Ω(ω)` only reads colours near `ω`.
4. **Cocycles.**
   - Each `g ∈ [[Z^d ~ X]]` is `g(x) = f_g(x)·x` for a continuous `f_g : X → Z^d`.
   - Freeness makes `f_g` unique.
   - Uniqueness gives `f_1 = 0` and `f_{gh}(x) = f_g(h x) + f_h(x)`.
5. **Homomorphism.** For `g ∈ Γ` put `g_Ω(ω) = f_g(πω)·ω`.
   - For `s ∈ S` this is the rule action `s_Ω`.
   - `π(g_Ω ω) = f_g(πω)·πω = g(πω)`.
   - Hence `g_Ω(h_Ω ω) = f_g(h πω)·f_h(πω)·ω = f_{gh}(πω)·ω = (gh)_Ω(ω)`, and `1_Ω = id`.
   - So `g_Ω` has inverse `(g^{-1})_Ω`, and `g ↦ g_Ω` is a homomorphism `Γ → Sym(Ω)` extending `s ↦ s_Ω`.
6. **Injective.** Suppose `g_Ω = id`.
   - For every `ω`, `f_g(πω)·ω = ω`, so `f_g(πω) = 0` by step 2.
   - So `Fix(g) = f_g^{-1}(0)` is closed and contains `π(Ω)`.
   - `π(Ω)` contains the `Z^d`-orbit of some `x_ω`, which is dense in `X` by minimality.
   - Hence `Fix(g) = X`, and `g = 1`.
7. **Marked equality.** By steps 5 and 6, a word in `S^{±1}` is trivial in `Sym(Ω)` exactly when it is trivial in `Γ`. So `(⟨S_Ω⟩, S_Ω) = (Γ, S)`. This is item 1.

**Instance.**
- `minimal-aperiodic-wang-shift-exists` makes `Omega_U` a nearest-neighbour SFT, cut out by edge matching on a finite window, with a free minimal `Z^2`-action.
- `minimal-z2-subshift-derived-full-groups-are-fg-simple` makes `D([[Z^2 ~ Omega_U]])` finitely generated, infinite and simple.
- So the theorem applies to `Γ = D([[Omega_U]])` with any finite generating set.

**Isolation lemma.** Let `Γ` be finitely generated, infinite and simple, marked by `S`.
- **Isolated ⇒ finitely presented.** Put `Γ_n = ⟨S | words of length ≤ n trivial in Γ⟩`.
  - For `n ≥ m`, a word of length `≤ m` is trivial in `Γ_n` iff it is trivial in `Γ`: one direction holds because `Γ` is a quotient of `Γ_n`, the other by definition. So `Γ_n → Γ` in the space of marked groups.
  - If `(Γ, S)` is isolated, some `Γ_n` equals it, so `Γ` is finitely presented.
- **Finitely presented ⇒ isolated.** Let `⟨S | R⟩` present `Γ` and pick `s_0 ∈ S` with `s_0 ≠ 1`.
  - "Every `r ∈ R` is trivial and `s_0 ≠ 1`" is an open condition.
  - A marked group satisfying it is a quotient of `Γ` in which `s_0` survives. Simplicity makes the kernel trivial, so the group is `(Γ, S)`.
- Only the first direction is needed for the consequence below; the second shows the criterion is exact.

**Consequence.** Suppose `D([[Omega_U]])` were not finitely presented.
- By the isolation lemma, some marked groups different from `(Γ, S)` would converge to it.
- By item 1, none of them is the rule group of a validly coloured `Z^2`-set. So every model they come from shows forbidden patterns.
- Matui's approximants are minimal subshifts `Z ⊆ Y_1`. If `Z ≠ Omega_U`, then `Z ⊄ Omega_U`: a nonempty closed invariant subset of the minimal `Omega_U` is all of it.
  - So the clopen set of points of `Z` showing a forbidden pattern at the origin is nonempty.
  - By minimality of `Z`, finitely many translates of that set cover `Z`, so every point of `Z` sees a defect within bounded distance.
