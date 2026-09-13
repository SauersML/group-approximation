---
rg: 2
id: subshift-el3-models-explicit-kazhdan-constant
kind: claim
title: G_X and its finite simple models SL_3N(F_2) share the explicit Kazhdan constant 1/(8(12√(2(|A|+2))+6+36√2)) for the note's generators
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that gives marked convergence and uniform expansion with no numerical constant; this gives an explicit constant for the manuscript's generating set and the resulting explicit spectral gap.
  primitive-binary-words-give-four-regular-simple-expanders: that is a degree-four family for a different three-element generating set with an unspecified constant; this uses the elementary generators e_ij(1), e_ij(u^±1), e_ij(e_a) and gives a number.
---

Let `X ⊆ A^Z` be an infinite minimal subshift, `R = LC(X,F_2) ⋊ Z`,
`G = EL_3(R)`, and `d = |A| + 2`. Mark `G` by the involutions

```text
Σ = { e_ij(s) : i ≠ j, s ∈ {1, u, u^(-1)} ∪ {e_a : a ∈ A} },
```

the generating set of `simple_kazhdan_sofic_group.tex` (l.94--95). Let `y_k` be
periodic sequences of least period `N_k` with the same words of length `2k+1` as
`X`. Mark `SL_(3N_k)(F_2)` by the images `Σ_k`, namely `e_ij(I)`, `e_ij(P^(±1))`,
`e_ij(D_(y_k)(e_a))`.

1. Put `c_d = 1/(8(12√(2d) + 6 + 36√2))`. Then `κ(G, Σ) >= c_d`, and
   `κ(SL_(3N_k)(F_2), Σ_k) >= c_d` for every `k`.
2. The normalized adjacency operator of the Cayley graph of
   `(SL_(3N_k)(F_2), Σ_k)` has all eigenvalues off the constants at most
   `1 − c_d^2/(12(d+1))`. These Cayley graphs converge to `(G, Σ)` in the space of
   marked groups, so they are expanders with an explicit spectral gap that converge
   to an infinite simple Kazhdan group.
3. Fibonacci subshift (`|A| = 2`, `d = 4`): `κ > 1/727`, and the spectral gap
   exceeds `1/(60 · 727^2) > 3·10^(-8)`.
