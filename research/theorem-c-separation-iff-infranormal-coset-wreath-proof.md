---
rg: 2
id: theorem-c-separation-iff-infranormal-coset-wreath-proof
kind: route
title: Distill the pointwise stabilizer of the fixed algebra, intersect the hyperlinear stabilizers, and read infranormality off conjugation by the compression semigroup
target: theorem-c-separation-iff-infranormal-coset-wreath
requires:
  - hyperlinear-action-distills-to-stabilizer-coset-bernoulli
  - kun-thom-nonsofic-wreath
---

# Proof

Write `X_Δ = ({±1},fair)^(G/Δ)` with `(g·x)_c = x_(g^(-1)c)`, `x_c` the coordinate at the
coset `c`, and `A_Δ = {x : x_Δ = 1}` (coordinate at the base coset). By Fourier
transform `L^∞(X_Δ) ⋊ G = L(W_Δ)`, so `W_Δ` is hyperlinear iff `X_Δ` is a hyperlinear
action. We use `hyperlinear-action-distills-to-stabilizer-coset-bernoulli` (call it
**D**) and its closure property (C2).

**Lemma 0.** `Stab(A_Δ) = Δ`, and `W_(gΔg^(-1)) ≅ W_Δ`.
`hA_Δ = {x : x_(hΔ) = 1}`, which equals `A_Δ` mod null iff `hΔ = Δ` (distinct
coordinates are independent and nonconstant). The `G`-sets `G/Δ` and `G/gΔg^(-1)` are
isomorphic via `kΔ ↦ kg^(-1)·gΔg^(-1)`, so the actions and the wreaths are isomorphic.

## Part 1: the floor

Assume `G` hyperlinear, so `G ∈ ℱ` (`X_G` is the one-point base shift, trivial action,
crossed product `L^∞({±1}) ⊗ L(G)`, embeddable). Since `G` is countable, `∩ ℱ` is the
intersection of a countable subfamily `(Δ_i)`: for each `g ∉ ∩ℱ` pick one member
omitting `g`. The product action `∏_i X_(Δ_i)` is hyperlinear (C2). The sets
`A_i = {x : x^(i)_(Δ_i) = 1}` have `Stab(A_i) = Δ_i` by Lemma 0, so by **D** the wreath
over `∩_i Δ_i = Δ_hl` is hyperlinear, and `Γ ≤ Δ_hl`. So `Δ_hl ∈ ℱ`.

For `p ∈ P_Γ = {g : gΓg^(-1) ≤ Γ}` we have `Γ ≤ p^(-1)Γp`. If `Δ ∈ ℱ` then
`p^(-1)Δp ⊇ p^(-1)Γp ⊇ Γ` and `W_(p^(-1)Δp) ≅ W_Δ`, so `p^(-1)Δp ∈ ℱ`. Hence

```text
Δ_hl = ∩_(Δ∈ℱ) Δ  ⊆  ∩_(Δ∈ℱ) p^(-1)Δp = p^(-1) Δ_hl p,     i.e.  p Δ_hl p^(-1) ≤ Δ_hl.
```

So `P_Γ ⊆ P_(Δ_hl)`; `P_Γ` generates `G`, hence so does `P_(Δ_hl)`: `Δ_hl` is infranormal.

## Part 2: the equivalence

**(a) ⇒ (b).** Let `X` be hyperlinear with `B = L^∞(X)^Γ` not `G`-invariant, and let
`Δ = Δ_B` be the pointwise stabilizer of `B`. `Γ ≤ Δ` by definition. By **D**
(Consequence 2) `W_Δ` is hyperlinear. Suppose `⟨⟨Γ⟩⟩ ≤ Δ`. Then for every `g`,
`g^(-1)Γg` fixes `B` pointwise, i.e. `Γ` fixes `g·B` pointwise, i.e. `g·B ⊆ B`; so `B` is
`G`-invariant, a contradiction.

**(b) ⇒ (c).** `Δ ∈ ℱ`, so `Δ_hl ≤ Δ`, and `⟨⟨Γ⟩⟩ ⊄ Δ` gives `⟨⟨Γ⟩⟩ ⊄ Δ_hl`.
(If `ℱ` were empty, (b) could not hold.)

**(c) ⇒ (a).** `⟨⟨Γ⟩⟩ ⊄ Δ_hl` forces `ℱ ≠ ∅` (else `Δ_hl = G`), so `G` is hyperlinear
(it is a subgroup of any `W_Δ`) and `Δ_hl ∈ ℱ` by Part 1. Take `X = X_(Δ_hl)`, a hyperlinear
action. The coordinate `x_(Δ_hl)` is `Γ`-invariant because `Γ ≤ Δ_hl` fixes the base
coset. Since `⟨⟨Γ⟩⟩ ⊄ Δ_hl` there is `g` with `g^(-1)Γg ⊄ Δ_hl`, i.e. `Γ ⊄ gΔ_hl g^(-1)`,
so some `γ ∈ Γ` has `γgΔ_hl ≠ gΔ_hl`. Then `g·x_(Δ_hl) = x_(gΔ_hl)` and
`γ·x_(gΔ_hl) = x_(γgΔ_hl)`, an independent nonconstant coordinate, so
`g·x_(Δ_hl) ∉ L^∞(X)^Γ`. The fixed algebra is not `G`-invariant.

**Nonsoficity.** Under (a)–(c) the action `X_(Δ_hl)` has non-invariant `Γ`-fixed algebra,
so by Kun--Thom Theorem C (`kun-thom-nonsofic-wreath`) it is not sofic. `Δ_hl` is not
normal because it contains `Γ` but not `⟨⟨Γ⟩⟩`. The same argument shows `X_Δ` is
hyperlinear and not sofic for any `Δ` as in (b).

## Part 3: the free separation

Let `G` be sofic and `Δ` as in (b). Put `Y = X_Δ × ({±1},fair)^G` with the diagonal
action. `Y` is essentially free because its Bernoulli factor is. The Bernoulli shift of
a sofic group is a sofic action (Elek--Lippner; Păunescu arXiv:1002.0605v5, Theorem 2.1 and
its proof, quoted in `research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md`),
hence hyperlinear; `X_Δ` is hyperlinear; so `Y` is hyperlinear by (C2). `Y` has `X_Δ` as a
factor, soficity passes to factors (restrict the embedding), and `X_Δ` is not sofic; so
`Y` is not sofic. This is `hyperlinear-nonsofic-free-action`. ∎
