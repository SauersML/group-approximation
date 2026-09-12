---
rg: 2
id: rokhlin-maximality-co-amenable-ascent-proof
kind: route
title: Følner windows on the coset space, sub-additivity on one factor, and weak containment to discard the complement
target: rokhlin-maximality-ascends-co-amenable-subgroups
requires:
  - seward-rokhlin-entropy-subadditivity
  - seward-weak-containment-relative-entropy-equality
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - bernoulli-rokhlin-maximality-passes-to-subgroups
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

Section 1 of the artifact. Put `X = A^G` uniform, and let `Q_g` be the coordinate partition at g. Let P be a countable generating partition with finite entropy, and fix ε > 0.

1. **Window.** By martingale convergence there is a finite S with `H(Q_g | ∨_(s ∈ S) gsP) < ε` for every g.
2. **Følner cosets.** Take `Ω' ⊆ H\G` with `|Ω's \ Ω'| <= (ε/|S|)|Ω'|`, and let `Ω'' = {ω : ωS ⊆ Ω'}`. Then `|Ω''| >= (1 - ε)|Ω'|`. Fix representatives `r(ω)`.
3. **Product structure.** Over H, X is the product of the Bernoulli shift `B = (A^(Ω''))^H` on the coordinates in the cosets of `Ω''` with the independent Bernoulli complement C.
4. **Partitions.** Put `P' = ∨_(ω ∈ Ω') r(ω)P` and `Σ = σ-alg_H(P')`.
   - Since `r(ω)s = k r(ωs)` with `k ∈ H`, every `r(ω)sP` with `ω ∈ Ω''` is Σ-measurable.
   - So `Q'' = ∨_(ω ∈ Ω'') Q_(r(ω))` has `H(Q'' | Σ) < |Ω''| ε`.
5. **Upper bound.** Let Z be the ergodic H-factor with sigma-algebra `F_(Ω'') ∨ Σ`. `seward-rokhlin-entropy-subadditivity`, with the chain `Σ ⊆ B(Z)`, gives `h^Rok_H(Z) <= H(P') + H(Q'' | Σ) < |Ω'| H(P) + |Ω''| ε`.
6. **Lower bound.**
   - Every generator β of Z satisfies `σ-alg_H(β) ∨ C = B(X)`, so `h_H(X | C) <= h^Rok_H(Z)`.
   - B is free. C is Bernoulli, hence weakly contained in every free action (`abert-weiss-free-actions-weakly-contain-bernoulli`).
   - `seward-weak-containment-relative-entropy-equality` with `X := B`, trivial F and `Y := C` gives `h_H(X | C) = h^Rok_H(B)`.
   - By maximality of H, `h^Rok_H(B) = |Ω''| log q`. If `Ω'' = Ω`, C is trivial and neither import is needed.
7. **Conclusion.** `H(P) > (1 - ε)(log q - ε)`. Letting ε -> 0 gives `h^Rok_G(A^G) >= log q`. Applying this to the alphabets `A^k` gives item 1.

Item 2 adds the down-passing of `bernoulli-rokhlin-maximality-passes-to-subgroups`. Item 3 applies item 5 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts` (Seward's Corollary 4.1) to `h^Rok_G(k^G) = log k`.
