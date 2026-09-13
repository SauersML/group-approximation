---
rg: 2
id: binary-leavitt-unit-tracial-rank-functions-are-mixtures
kind: claim
title: Tracial rank functions on C[R^x], and limits of HS approximations of R^x, are mixtures of the augmentation rank and the von Neumann rank
distinct_from:
  binary-leavitt-full-character-simplex: that classifies characters of R^x; this reads off the Sylvester matrix rank functions those characters induce, and what HS approximations give for von Neumann dimensions of kernels.
  simple-group-rank-functions-are-augmentation-or-detecting: that is the dichotomy for arbitrary Sylvester rank functions on the group algebra of a simple group over any field; this classifies exactly the tracial ones over C for R^x, where the detecting side is a single rank function.
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that asks whether the augmentation rank is the only rank function over F_2, where no trace exists; this is characteristic zero, where the von Neumann rank already detects the defect and the tracial rank functions form a segment.
---

**ESTABLISHED (proved on paper, unreviewed; a corollary of the character simplex).** Let
`G = L_(F_2)(1,2)^x`. For a matrix `A` over `C[G]` write `rk_ε(A) = rank_C ε(A)` and
`rk_vN(A) = (Tr ⊗ τ_G)(range projection of λ(A))`.

1. **Tracial rank functions.** Let `π : C[G] -> M` be a unital `*`-homomorphism into a von
   Neumann algebra with a faithful normal tracial state `τ`. Put
   `rk_π(A) = (Tr ⊗ τ)(range projection of π(A))`. Then
   `rk_π = α rk_ε + (1 - α) rk_vN`, where `α = τ(π(g))` for any `g != 1`.
2. **HS approximations.** Let `σ_n : G -> U(d_n)` satisfy
   `||σ_n(gh) - σ_n(g) σ_n(h)||_2 -> 0` along an ultrafilter `ω`, in the normalized
   Hilbert--Schmidt norm. Extend them linearly to matrices over `C[G]`, and let `ν_n(A, s)` be
   the number of singular values of `σ_n(A)` above `s`, divided by `d_n`. Then:
   - the limit character is `lim_ω tr σ_n(g) = α + (1-α) δ_(g,1)` for one `α in [0,1]`;
   - for every matrix `A`, `lim_(s↓0) lim_ω ν_n(A, s) = α rk_ε(A) + (1-α) rk_vN(A)`, the limit
     in `s` taken outside a countable set;
   - `limsup_ω dim ker σ_n(A) / d_n <= α dim ker ε(A) + (1-α) dim_vN ker λ(A)`.

**What it says.**
- Any nondegenerate HS model of `R^x` (`α < 1`) sees von Neumann dimensions of kernels
  exactly at the level of numerical rank, after removing the trivial part.
- Exact kernel dimensions satisfy only the upper bound. A matching lower bound would need a
  uniform determinant bound for `σ_n(A)`, an integrality that almost representations do not
  have.
- Existence of such models is the open hyperlinearity question
  (`binary-leavitt-unit-group-hyperlinear`). This node decides nothing about it.

Route: `binary-leavitt-unit-tracial-rank-functions-proof`.
