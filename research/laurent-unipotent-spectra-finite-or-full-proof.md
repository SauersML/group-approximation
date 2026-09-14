---
rg: 2
id: laurent-unipotent-spectra-finite-or-full-proof
kind: route
title: Rich coordinates write arbitrary windows into the others, so a non-bounded invariant closed set is dense
target: laurent-unipotent-spectra-are-finite-or-full
requires: [bms-congruence-kernel-trivial-not-totally-imaginary]
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

Artifact part 1, Sections 1–3.

**Setup.** `Â ≅ F_q^Z` via a nontrivial `ψ : F_q → μ_p`, and `A` acts by shifts and convolution. For a character `χ`,
`Ann(χ)` is an ideal with normalized generator `h`, `h(0) ≠ 0`. The window `W_N = span{t^n : |n| ≤ N}` has length
`L = 2N+1`. The dual action of `e_ij(a)` on coordinates is `χ_j ↦ χ_j + a·χ_i`.

1. **(F1) Rich coordinates cover windows.** If `Ann(y) = 0` or `deg Ann(y) ≥ L`, then restriction to `W_N` maps `A·y`
   onto `Ŵ_N`. The image of `closure(A·y)` is `(W_N ∩ Ann(y))^⊥`, and a nonzero multiple of `h` has exponent span
   `≥ deg h > 2N`.
2. **(F2) Poor characters are few.** Characters with nonzero annihilator of degree `< L` number `< q^{2L}`: there are
   `< q^L` choices of `h`, each with `q^{deg h}` characters.
3. **(F3) Fibres are large.** If `deg Ann(y) = D ≥ L`, window fibres in `A·y` have `q^{D-L}` elements. If
   `Ann(y) = 0`, they are infinite.
4. **(F4) Annihilators are unbounded.** Without a uniform nonzero `J`, some coordinate of some `χ ∈ K` has zero
   annihilator or annihilator degree `> 3L`. Finitely many `h` of bounded degree would multiply to a uniform `J`.
5. **Density.** Fix `N` and patterns `π_1, …, π_m`. Take `y = χ_1` as in (F4).
   - By (F3) and (F2) choose `b` with `z = χ_2 + b·y` rich and window `π_2`; apply `e_12(b)`.
   - For `k ≥ 3`, use (F1) to set window `π_k` via `e_1k(b_k)`.
   - Set window `π_1` via `e_21(b)` with `y + b·z`, by (F1) for the rich `z`.
   - `K` is closed and meets every basic open set, so `K = Â^m`.
6. **Representations.** `K` is the Gelfand spectrum of `σ(C*(A^{d-1}))`, hence closed, and it is invariant under the
   upper-left `E_{d-1}(A)`.
   - In the finite case `σ(u(v)) = 1` on `J^{d-1}`.
   - Commutators `[e_{i,d}(j), e_{d,k}(1)] = e_{i,k}(j)` and signed permutations put `E_d(A,J)` in `ker σ`.
   - Bass–Milnor–Serre Corollary 4.3 b) (`bms-congruence-kernel-trivial-not-totally-imaginary`) gives
     `SL_d(A,J) = E_d(A,J)`, so `σ` factors through `SL_d(A/J)`.
