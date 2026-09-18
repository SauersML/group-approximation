---
rg: 2
id: cover-pair-sections-force-fixed-point-surjectivity-proof
kind: route
title: Equivariant sections preserve fixed-point sets; morphisms of pairs pull deficiencies back; on the free monoid, right translation by a is a non-surjective injection that an automaton can read through
target: cover-pair-sections-force-fixed-point-surjectivity
requires:
  - post-surjective-sft-covers-admit-scheduled-sections
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
artifacts:
  - research/artifacts/fixed-point-surjectivity-and-free-monoid-calibration-2026-09-18.md
  - experiments/free-monoid-cover-pair-2026-09-17/check.py
---

Complete proofs are in the artifact.

1. **F1 (§1).** Let `z ∈ Fix(H)`. Equivariance gives `h.s(z) = s(h.z) = s(z)`, so `s(z) ∈ X ∩ Fix(H)` and
   `F(s(z)) = z`. Taking `H = G` gives `|C_X| ≥ |A|`.
   - For a seed exact on `Sym_E`: the constant `a^G` lies in `Sym_E` and `ξ(a^G)` is `G`-fixed.
   - Equivariance then spreads exactness at `1` to every site.
2. **F2 (§2).** Suppose `z ∈ D_H(X, F)` and `π(z') = z` with `z' ∈ Fix(H)`. If `z' = F'(x')` with `x'` `H`-fixed,
   then `ρ(x')` is `H`-fixed and `F(ρ(x')) = z`, a contradiction. Each listed construction is checked to carry
   such a morphism, `(ρ, π)`, back to `(X, F)`.
3. **F3.** `strict-pairs-give-dual-failures-on-bounded-defect-domains`, part 3, gives the automaton section `τ` of
   `σ|_{X_R}`, and F1 applies. Proposition C is that of the scheduled-sections artifact, the one used by
   `post-surjective-sft-covers-admit-scheduled-sections`.
4. **M1 (§3).** The Rees-periodic sets `Per_n` are finite, `τ`-invariant and dense. An injective `τ` is therefore
   onto a dense subset, and its image is closed.
5. **M2 (§3).** The lift is explicit: `x'(ua) = z(u)`, `x'(ub) = 0`, `x'(ε) = x(ε)`. `F` never reads `x(ε)`,
   and the only constant of `X` is `0^M`. This is machine-checked on small balls by
   `experiments/free-monoid-cover-pair-2026-09-17/check.py`.
