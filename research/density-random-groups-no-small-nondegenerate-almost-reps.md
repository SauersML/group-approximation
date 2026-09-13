---
rg: 2
id: density-random-groups-no-small-nondegenerate-almost-reps
kind: claim
title: Random groups with independent reduced relators have no nondegenerate unitary almost-representations below dimension about the square root of the number of relators
distinct_from:
  meshulam-random-complex-no-polynomial-quotients: that is Meshulam's theorem that random 2-complex groups have no nontrivial quotient of polynomial order, a profinite statement in the Linial--Meshulam model; this is a statement about Hilbert--Schmidt almost-representations in a density-type model of random presentations, with a dimension cap of order the square root of the number of relators.
  bounded-dimension-microstates-force-lef: that says a single dimension cap on microstates for every window forces LEF; this says a random presentation admits no nondegenerate almost-representation below a cap that grows with the relator length, and it draws no conclusion about LEF.
  density-random-group-hyperbolic-kazhdan-with-positive-b2: that supplies hyperbolic Kazhdan groups with b_2 >= 1 in the cyclically reduced density model; this is a dimension-collapse statement for almost-representations in the independent reduced-words model, with no property (T) content.
artifacts:
  - research/artifacts/solve-nh-random-t-2026-09-13.md
---

**ESTABLISHED.** Fix `n >= 2`, `d ∈ (0,1)` and `ε ∈ (0,1]`. Let `A` be the
`2n` letters `s_i^{±1}`, and let `R_ℓ` consist of `N_ℓ = ⌈(2n−1)^{dℓ}⌉`
independent uniform reduced words of length `ℓ`. Put

```text
κ_n = (n−1) / (2n (2n−1)^2),
D_ℓ = ⌊ ( κ_n N_ℓ / (4n log(1 + 8ℓ/ε)) )^(1/2) ⌋.
```

With probability tending to 1 as `ℓ → ∞`, the following holds. Let `D <= D_ℓ`
and `U = (U_1, …, U_n) ∈ U(D)^n` with

```text
||r(U) − I||_2 <= ε/2        for every r ∈ R_ℓ,
```

where `||X||_2 = tr_D(X*X)^(1/2)` is the normalized Hilbert--Schmidt norm. Then
`||a(U) − b(U)||_2 <= 2ε` for all letters `a, b ∈ A`. In particular every `U_i`
is within `2ε` of `U_1`, and `||U_i^2 − I||_2 <= 2ε`.

So below dimension `D_ℓ ≍ (2n−1)^{dℓ/2} / √(log ℓ)`, every ε/2-almost
representation of `Γ_ℓ = ⟨s_1, …, s_n | R_ℓ⟩` is 2ε-close to a map sending every
generator to one near-involution. That is the length-parity quotient, which
exists exactly for even `ℓ`. The proof is an elementary first-moment argument,
`density-random-small-almost-reps-first-moment-proof`. No novelty is claimed.

## What this shows and what it does not

- **Dimension floor for approximations.** If `s_1 s_2^{-1} ≠ 1` in `Γ_ℓ`, an
  approximation with `τ(s_1 s_2^{-1}) ≈ 0` has `||U_1 − U_2||_2 ≈ √2 > 2ε` for
  `ε < 1/√2`. So any Hilbert--Schmidt model of `Γ_ℓ` that is ε/2-exact on the
  relators and close to the regular trace on `s_1 s_2^{-1}` needs dimension
  larger than `D_ℓ`.
- **Small finite quotients.** The regular representation of a quotient `Q`
  in which two letters differ is exact and nondegenerate. So w.h.p. `Γ_ℓ` has
  no such quotient of order at most `D_ℓ`. This is the unitary analogue of
  "random groups have no small quotients".
- **No non-hyperlinearity.** The statement is consistent with hyperlinearity at
  every density. At density below 1/6 random groups are virtually special, hence
  hyperlinear, and the theorem still holds there. A first-moment union bound
  cannot reach dimensions with `D^2 log ℓ ≫ N_ℓ`; see the artifact, Attempt (b).

## Model

Relators are independent uniform *reduced* words, repeats allowed. The Gromov
density model uses cyclically reduced words
(`gromov-density-random-groups-kazhdan-above-third`). The same argument, with the
swapped letter taken from the middle of the word, should give the analogue
there. That version is not proved here and is not claimed.

DERIVATION
density-random-small-almost-reps-first-moment-proof
