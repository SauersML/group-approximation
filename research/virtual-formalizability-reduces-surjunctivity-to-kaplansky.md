---
rg: 2
id: virtual-formalizability-reduces-surjunctivity-to-kaplansky
kind: route
title: Localize to the memory subgroup, regroup along a finite-index subgroup, formalize, and linearize under stable finiteness
target: stable-finiteness-forces-binary-surjunctivity
requires:
  - injective-automata-over-fg-groups-are-virtually-formalizable
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Let `F_2[G]` be stably finite and `tau` injective on `(F_2^n)^G`, with finite memory `M`.

1. **Localize.** Put `Γ = ⟨M⟩`, a finitely generated group. Since `tau(x)(g)` reads only `x` on
   `gΓ`, `tau` acts on `A^G = ∏_(gΓ) A^(gΓ)` coset by coset, as copies of the same rule `tau_Γ` over
   `Γ`. So `tau_Γ` is injective, and `tau` is surjective iff `tau_Γ` is.
2. **Formalize.** By the first prerequisite there are a finite-index `H <= Γ` and a left inverse
   `sigma` such that `(tau_Γ, sigma)` is formal as a pair of `H`-automata on `N = n[Γ:H]` tracks.
3. **Linearize.** `M_N(F_2[H])` is a unital subring of `M_N(F_2[G])`, which is directly finite, so it
   is directly finite. By the second prerequisite, applied over `H`, `tau_Γ o sigma = id`. So
   `tau_Γ` is surjective, and by step 1 so is `tau`.

Unlike the invalidated routes `formalizable-pairs-reduce-surjunctivity-to-kaplansky` and
`formalizable-left-inverses-reduce-surjunctivity-to-kaplansky`, this route is not killed by
`binary-left-inverse-pairs-need-not-be-formalizable`: regrouping produces several tracks, where the
one-track classification does not apply.
