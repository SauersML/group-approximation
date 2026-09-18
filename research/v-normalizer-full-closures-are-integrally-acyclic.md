---
rg: 2
id: v-normalizer-full-closures-are-integrally-acyclic
kind: claim
title: For every group of outer automorphisms of Thompson's V, the full closure of its preimage in Aut(V) is integrally acyclic and perfect, so no homology obstructs finite presentation
distinct_from:
  v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz: that identifies the germ groupoid of V ⋊ ⟨t⟩ as O_2 ⋊_t Z and decides when the lag cocycle extends; this computes its groupoid homology (zero) and deduces acyclicity of the full closure.
  fp-rsgs-have-fp-full-closures: that is the open question whether full closures of finitely presented RSGs are finitely presented; this shows that for the test family V ⋊ ⟨t⟩ every homological invariant of the full closure vanishes, so no homological obstruction to a negative answer exists.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**ESTABLISHED** through `v-normalizer-full-closures-are-integrally-acyclic-proof`. Lane proof
(bh-higman-classic). It is a short deduction from two theorems read at source on 2026-09-18 from their TeX
e-prints (local copies under `$GQ/src/bh-higman-classic/`):
- Matui, arXiv:0909.1624 (`htfgeg.tex`): Theorem `LHS` (1), Theorem `reduction` (2), Proposition
  `homosim`, Theorem `CKHomology`;
- X. Li, arXiv:2209.08087 (`Homology_TFG.tex`): Corollary `introcor:Vanish`, and the definitions of
  comparison and of purely infinite minimal groupoids (TeX l. 802–804).
Not independently reviewed. No priority claimed.

## Statement

Let `N(V) ≅ Aut(V)` be the normalizer of Thompson's `V` in `Homeo({0,1}^N)`. Let `Q ≤ Out(V) = N(V)/V` be
any subgroup, `Γ_Q ≤ N(V)` its preimage, and `G_Q` the groupoid of germs of `Γ_Q`. Then:
1. `H_*(G_Q; Z) = 0` in all degrees.
2. `[[Γ_Q]]`, the topological full group of `G_Q`, is integrally acyclic: `H_n([[Γ_Q]]; Z) = 0` for all
   `n > 0`. It is also perfect, since it equals its commutator subgroup.

In particular this holds for `Γ_t = V ⋊ ⟨t⟩` for every `t ∈ N(V)`. For `Q = 1` it recovers the
Szymik–Wahl theorem that `V` is integrally acyclic, which Li's corollary reproves.

## Consequence for Question 1.4

For the test family of `fp-rsgs-have-fp-full-closures`, `H_1 = H_2 = 0`. So no homological invariant
can show `[[Γ_t]]` is not finitely presented, nor fail to be of type `FP_n`, for any `t`. A negative
answer to Question 1.4 in this family would need a non-homological invariant. A positive answer needs
a finiteness argument (Attempt 3 there).
