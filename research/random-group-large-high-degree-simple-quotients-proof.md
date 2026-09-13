---
rg: 2
id: random-group-large-high-degree-simple-quotients-proof
kind: route
title: Union-bound small simple quotients with the nonbacktracking return bound, kill bounded degree with Kozma–Lubotzky, and fill relators with one conjugate of a_1^3
target: random-group-simple-quotients-are-large-and-high-degree
requires:
  - nonbacktracking-walks-on-regular-multigraphs-return-rarely
  - random-groups-have-no-fixed-degree-linear-representations
  - finite-simple-groups-at-most-two-per-order
  - infinite-simple-quotient-count-iff-marked-limit-quotient
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

Notation as in the target. Put `p_m = (2m−2)/(2m−1)`.

## (Q1)

**One homomorphism.** Let `φ: F_m ->> S` with `|S| >= 3`. By
`nonbacktracking-walks-on-regular-multigraphs-return-rarely` ("Use for words"), a uniform
reduced word `ω` of length `l >= 2` has `P[φ(ω) = 1] <= p_m`. The relators are independent,
so `P[R ⊆ ker φ] <= p_m^k`.

**Union bound.** Each normal subgroup of `Γ` with quotient `S` is `ker φ` for at least one
epimorphism `φ: F_m ->> S` with `R ⊆ ker φ`. There are at most `|S|^m` such `φ`, and by
`finite-simple-groups-at-most-two-per-order` at most two groups `S` of each order `n`. So the
expected number of these normal subgroups is at most

```text
Σ_(n=3..M) 2 n^m p_m^k  <=  2 M^(m+1) p_m^k.
```

Markov's inequality gives the probability bound. At `M = M_l`,
`M^(m+1) <= exp(θ_m k/2)` and `p_m^k = exp(−θ_m k)`, so the bound is `2 exp(−θ_m k/2)`. For
`d > 0`, `k -> ∞`.

## (Q2)

**Simple quotients.** Let `S` be a finite simple quotient of `Γ` with `pdeg(S) <= D`.
Steps 1–3 of (M3) in `infinite-simple-quotient-count-marked-limit-proof` give an injective
`θ: S -> GL_(D^2)(F)`. So `ρ = θ ∘ (Γ ->> S)` has `|ρ(Γ)| = |S|`. Take degree `D^2` in
item 1 of `random-groups-have-no-fixed-degree-linear-representations`: a.a.s. every such `ρ`
has `|ρ(Γ)| <= 2`.

**Linear quotients.** An infinite quotient `Γ ->> G <= GL_(D^2)(K)` is a representation with
infinite image, excluded by the same item.

## (Q3)

Intersect the events of (Q1) at `M = M_l` and of (Q2). Both have probability tending to 1.
Every `S_n` in (M1) is a finite simple quotient of `Γ`, and `|S_n| -> ∞`, so only finitely
many terms have `|S_n| <= 2`. Each term with `|S_n| >= 3` has `|S_n| > M_l` by (Q1) and
`pdeg(S_n) > D` by (Q2).

## (Q4)

**One relator word.** Let `l = 2r + 3`, `r >= 0`, and `w_0 = a_2^r a_1^3 a_2^{-r}`. It is
reduced of length `l` and lies in `<<a_1^3>>`. With repetitions,
`P[R = (w_0, …, w_0)] = |S_l|^(−k) > 0` for every `d >= 0`.

**PSL_2 targets.** Let `x = [[0,−1],[1,−1]]`, `T = [[1,1],[0,1]]`, `S = [[0,−1],[1,0]]`.
- `x^3 = I`: `x^2 = [[−1,1],[−1,0]]` and `x^2 · x = I`.
- `xT = S`, and `S^{-1} T S = [[1,0],[−1,1]] = E_21(−1)`.

For a prime `p >= 5`, map `a_1 -> x`, `a_2 -> T`, `a_i -> I` for `i >= 3`, reduce mod `p` and
project to `PSL_2(F_p)`. This is `ψ_p`.
- **Onto.** The image contains `E_12(1)` and `E_21(−1)`, hence every `E_12(t)` and
  `E_21(t)`, `t ∈ F_p`. These generate `SL_2(F)` over any field `F`. For `g = [[a,b],[c,d]]`
  with `c ≠ 0`, `E_12((1−a)/c) g` has top-left entry 1, and then left multiplication by
  `E_21(−c)` leaves `E_12(b')`. If `c = 0`, first replace `g` by `E_21(1) g`.
- **Simple, distinct kernels.** `PSL_2(F_p)` is simple for `p >= 5` (classical). The kernels
  are pairwise distinct because the orders `p(p^2−1)/2` are.
- **Contains the relators.** `ψ_p(a_1^3) = 1`, so `w_0 ∈ ker ψ_p`.

Hence `E[#{N ⊴ Γ : Γ/N ≅ PSL_2(F_p), p >= 5}] >= Σ_p P[R = (w_0,…,w_0)] = ∞`.

**Alternating targets.** `a_1 -> (1 2 3)`, `a_2 -> (1 2 ⋯ n)` with `n >= 5` odd maps onto
`Alt(n)`. This is Step 2 of `density-random-first-moment-divergence-proof`, whose generation
argument is repeated there. It kills `a_1^3`, and the same sum diverges.

**A.a.s. absence (d > 0).** `pdeg(PSL_2(F_p)) <= 2`, so (Q2) with `D = 2` excludes these
quotients a.a.s.

## (Q5)

At fixed `l` there are `|S_l|^k` relator sequences, each with probability `|S_l|^(−k)`. So

```text
E[X(Γ) | E] = Σ_(R ∈ E) P[R | E] · X(Γ_R),
```

a finite sum of terms in `[0, ∞]` with positive weights. It is finite iff every term is.
