---
rg: 2
id: fabrykowski-gupta-ascending-hnn-satisfies-boone-higman
kind: claim
title: The ascending HNN extension of the Fabrykowski–Gupta group along its last-section endomorphism embeds in a finitely presented simple group
distinct_from:
  grigorchuk-supergroup-fp-amenable-hnn-satisfies-boone-higman: that is a binary example; this is a ternary one, with first sections that factor through the abelianization.
  bounded-last-section-ascending-hnns-satisfy-boone-higman: that is the general criterion; this checks it for the Fabrykowski–Gupta group.
requires:
  - bounded-last-section-ascending-hnns-satisfy-boone-higman
---

**ESTABLISHED** (lane proof below; elementary; not reviewed; no priority claimed).

## The group and the endomorphism

Let `T_3 = {0,1,2}^*`, let `a` be the rooted 3-cycle `a(i w) = (i+1) w` (indices mod 3), and
let `r = (a, 1, r)`, meaning `r|_0 = a`, `r|_1 = 1`, `r|_2 = r`, with trivial root
permutation. The Fabrykowski–Gupta group is `Γ = ⟨a, r⟩`. Its abelianization is `(Z/3)^2`,
free on the images of `a` and `r` (Bartholdi arXiv:math/0007062, proof of Theorem
`thm:Gamma`: "`F/F' ≅ (Z/3)^2 ≅ Γ/Γ'`" with `F = ⟨a, r | a^3, r^3⟩`; TeX read).

Let `χ_0, χ_1: Γ → Γ` be the homomorphisms through the abelianization with

```text
χ_0(a) = 1,  χ_0(r) = a;       χ_1(a) = r,  χ_1(r) = 1,
```

and define `σ(g) = (χ_0(g), χ_1(g), g)`. This is a homomorphism `Γ → Aut(T_3)` because it is
coordinatewise one, and it is injective (last coordinate).

**`σ(Γ) ≤ Γ`.** First, `σ(r) = (a, 1, r) = r`. Second, `σ(a) = (1, r, a) = a^{-1} ∘ r ∘ a`:
indeed `(a^{-1} r a)(i w) = i · r|_{i+1}(w)`, giving sections `(r|_1, r|_2, r|_0) = (1, r, a)`.
So `σ` is an injective endomorphism of `Γ`. In Bartholdi's left-to-right convention it is his
substitution `σ(a) = r^{a^{-1}}, σ(r) = r` from Theorem `thm:Gamma`. The present argument does
not rely on his theorem.

## Statement

`Γ*_σ = ⟨Γ, t | t^{-1} g t = σ(g)⟩` embeds in the Röver–Nekrashevych group `V_3(S)` of a
finite bounded automaton group `S ≥ Γ`. Hence **`Γ*_σ` embeds in a finitely presented simple
group**, and it lies in the permutational class `B_A`. `Γ*_σ` is amenable and not elementary
amenable, because `Γ` has intermediate growth (a literature input, not re-read).

## Proof: check the criterion of `bounded-last-section-ascending-hnns-satisfy-boone-higman`

- **Bounded.** `r` is directed along `2^∞`, with off-ray sections in `{1, a}`.
- **Last-section form.** `σ(g) = (ψ_0(g), ψ_1(g), g)` with `ψ_z = χ_z`, and `σ(Γ) ≤ St(1)`.
- **(F) finite.** `ψ_0(Γ) = ⟨a⟩` and `ψ_1(Γ) = ⟨r⟩`, both of order 3.
- **(E) eventually finitary.** On the abelianization, `σ` sends `ā ↦ r̄` (since `σ(a)` is a
  conjugate of `r`) and `r̄ ↦ r̄`. So for `k ≥ 1`, `σ^k(a)` and `σ^k(r)` both map to `r̄`,
  which gives:
  - `ψ_0σ^k(a) = ψ_0σ^k(r) = a`, which is finitary;
  - `ψ_1σ^k(a) = ψ_1σ^k(r) = 1`.

  So (E) holds with `k_0 = 1`. (For `k = 0`, `ψ_1` takes values in `⟨r⟩`, which is bounded but
  not finitary. That is allowed.)

The criterion applies. ∎

## Scope

- **Finite presentation.** Bartholdi's stated L-presentation of `Γ` uses three substitutions
  `σ, χ_1, χ_2`, the last two being automorphisms. By his Theorem `thm:hnn`, the associated
  finitely presented group has three stable letters. This node covers only the
  single-stable-letter extension `Γ*_σ`, a subgroup of that group.
  - His proof also mentions a σ-only presentation with six iterated relators. If that one is
    ascending, `Γ*_σ` is itself finitely presented. That is not checked here.
  - BH for the three-letter group would additionally need the automorphisms `χ_1, χ_2`
    realized compatibly in the host. That is open.
- **Priority.** None claimed; bounded search only.
