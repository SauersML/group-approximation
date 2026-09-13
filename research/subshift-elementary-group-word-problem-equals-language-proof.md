---
rg: 2
id: subshift-elementary-group-word-problem-equals-language-proof
kind: route
title: Compute over the full-shift crossed product, restrict to X, and decide vanishing by window queries
target: subshift-elementary-group-word-problem-equals-language
requires: [marked-subshift-elementary-group-determines-language, subshift-elementary-group-is-simple-modulo-centre, minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

Artifact §1.
1. **Language to word problem.** `W_w(σ_X) = 1` iff `w ∉ L(X)` (`marked-subshift-elementary-group-determines-language`).
2. **Word problem to language.** Represent elements of `R_full = LC(A^Z,F_q)⋊Z` as finite sums of `f_j u^j`, with
   window tables for the `f_j`. Sums and products (`(fu^i)(gu^j) = f (g∘T^(−i)) u^(i+j)`) are computable, so the
   matrix `M_g` of a word `g` is computable.
3. **Restriction.** `π : R_full → R_X` is a ring homomorphism sending generators to generators, so `g` maps to
   `π(M_g)`. `π(Σ f_j u^j) = 0` iff every `f_j` vanishes on the windows in `L_(2m+1)(X)`: finitely many
   computable queries.
4. **Triviality.** `g = 1` in `S_X` iff `π(M_g) = c I_3` for some `c ∈ F_q^×`, since the centre is scalar
   (`subshift-elementary-group-is-simple-modulo-centre`) and scalars in `G_X` are central. This is finitely many
   vanishing tests with queries fixed in advance, hence a truth-table reduction.
