---
rg: 2
id: effective-subshift-invariant-measure-existence-is-pi01-proof
kind: route
title: Pattern-frequency linear programs on balls, then a diagonal compactness limit and Kolmogorov extension
target: effective-subshift-invariant-measure-existence-is-pi01
requires: []
artifacts:
  - research/artifacts/un-open-6-tarski-complexity-2026-09-13.md
---

Complete proof in the artifact, §1. Summary.

1. **The programs.** For `n ≥ 1` let `Adm(e,n)` be the set of `q ∈ A^(B_n)` such that for every pattern `p` among the
   first `n` enumerated elements of `W_e` and every `g ∈ Γ` with `g·supp(p) ⊆ B_n`, the restriction of `q` to
   `g·supp(p)` is not `g·p`. `LP(e,n)` asks for `ρ : Adm(e,n) → [0,1]` with `Σ ρ = 1` and, for every `s ∈ S` and every
   `w ∈ A^(B_(n-1))`,
   `Σ_{q|B_(n-1) = w} ρ(q) = Σ_{q|sB_(n-1) = s·w} ρ(q)`
   (note `sB_(n-1) ⊆ B_n`). The data are finite and computable from `(e,n)`, and feasibility of a rational linear
   system is decidable. So `∀n LP(e,n)` is `Π⁰₁`, uniformly in `e`.
2. **Measure ⇒ programs.** If `μ` is invariant with `μ(X_e) = 1`, put `ρ(q) = μ([q at B_n])`. Cylinders of patterns
   outside `Adm(e,n)` miss `X_e`, so `ρ` lives on `Adm(e,n)`; the equations are `μ(s·C) = μ(C)` for the cylinder `C`
   of `w` at `B_(n-1)`.
3. **Programs ⇒ measure.** Take feasible `ρ_n`, and let `q_(n,m)` be the marginal of `ρ_n` on `B_m` for `m ≤ n`. By a
   diagonal subsequence all `q_(n,m)` converge, to `q_m`; marginals are consistent, so Kolmogorov extension gives a
   Borel probability `μ` with `μ([w at B_m]) = q_m(w)`. Summing the level-`n` equations over the extensions of a
   pattern on `B_(m-1)` gives the level-`m` equations, which pass to the limit: `μ(s·C) = μ(C)` for ball cylinders,
   hence for all cylinders and all `g ∈ Γ`. For a forbidden pattern `p` and `g ∈ Γ`, once `p` is enumerated and
   `g·supp(p) ⊆ B_m`, every `q_(n,m)` with `n ≥ m` large gives mass `0` to occurrences of `g·p`; so does `μ`, and a
   countable union gives `μ(X_e) = 1`.
