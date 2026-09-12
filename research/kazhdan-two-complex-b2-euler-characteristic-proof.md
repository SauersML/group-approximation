---
rg: 2
id: kazhdan-two-complex-b2-euler-characteristic-proof
kind: route
title: Cartan--Hadamard asphericity, vanishing b_1 from (T), and corner counting
target: kazhdan-two-complex-b2-is-euler-characteristic-minus-one
requires: []
---

## Direct proof

1. **Asphericity.** CAT(0) spaces are contractible, and `Γ` acts freely and
   cellularly on `X` by deck transformations. So `K = Γ\X` is a `K(Γ,1)`, and
   `H_*(Γ;Q) = H_*(K;Q)`, which vanishes above degree two.
2. **Betti numbers.** `χ(K) = b_0 - b_1 + b_2`, with `b_0 = 1`. Property (T) makes
   `H_1(Γ;Z)` finite, so `b_1 = 0` and `b_2 = χ(K) - 1`.
3. **Counting.** Each edge contributes one link vertex at each endpoint, so
   `Σ_v v_L = 2|E|`. Each face corner is one link edge, so `Σ_v e_L = p|F|`. With
   constant link data, `|E| = |V| v_L/2` and `|F| = |V| e_L/p`, and
   `χ = |V| - |E| + |F|` gives the formula.
4. **Hyperbolicity.** `Γ` acts properly and cocompactly on the CAT(−1) space `X`,
   so it is quasi-isometric to `X` (Švarc--Milnor) and hence hyperbolic.
5. **Worked instance.** A regular hyperbolic square with angles `π/3` exists,
   because `4·π/3 < 2π`. Link edges have length `π/3` and link girth is 6, so every link
   cycle has length at least `2π`. By Gromov's link condition and Cartan--Hadamard,
   `X` is CAT(−1). `PG(2,q)` has `q^2+q+1` points and lines, each on `q+1` of the other
   kind, so `v_L = 2(q^2+q+1)`, `e_L = (q+1)(q^2+q+1)`, and
   `1 - v_L/2 + e_L/4 = 1 + (q^2+q+1)(q-3)/4`.

∎
