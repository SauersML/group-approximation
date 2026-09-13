---
rg: 2
id: bowen-chapman-ambient-rank-models-do-not-round-peripheral-proof
kind: route
title: Folner boxes in congruence quotients are far from every ideal, by the uncertainty principle on (Z/N)^3
target: bowen-chapman-ambient-rank-models-do-not-round-peripheral
requires: []
artifacts:
  - research/artifacts/nls-rank-metric-witness-2026-09-12.md
---

# Folner boxes are far from ideals

This is a direct establishment. The complete proof is in Section 2.4 of the
artifact.

- **Invariant subspaces and commutant (Lemma B1).**
  - `rho_N(e_ij(f)) - 1 = E_ij (x) fbar`, and `F_2[N^3] -> A` is onto because
    `x_l^-1 = x_l^(N-1)`.
  - So `rho_N(Gamma)` spans `M_3(A)`.
  - The invariant subspaces are therefore the `I^3`, for ideals `I` of `A`, and
    the commutant is `1_3 (x) A`.
- **Uncertainty (Lemma B2).** Suppose an ideal `I` meets `B_m` in dimension at
  least `m^3 - c`, with `c + 1 <= N^3/64`.
  - `I` contains a nonzero `f` supported on a cube of side
    `s = ceil((c+1)^(1/3)) <= N/4 + 1`.
  - `N` is odd and `char F = 2`, so the characters of `(Z/N)^3` diagonalize `A`
    over `Fbar`. Hence `dim fA` is the number of characters with `chi(f) != 0`.
  - A polynomial of degree less than `s` in each of three variables vanishes at no
    more than `3(s-1)N^2` points of `mu_N^3`.
  - So `dim I > N^3/4`.
- **Items 1 to 3.**
  - Only the 18 generators `e_ij(x_l)` move `W`, and each moves it by one face of
    `m^2` monomials.
  - For item 2, either `B_m cap I` misses more than `N^3/64 - 1` dimensions of
    `B_m`, or `dim I > N^3/4 > 2 dim B_m`.
  - Item 3 is Lemma B2 applied to `I = aA`. Since `B_m <= aA + im(pi_B - a)`,
    `dim(B_m cap aA) >= m^3 - rk(pi_B - a)`. Also `rk a <= m^3 + rk(pi_B - a)`.
- **Item 4.**
  - **Linear-size pieces.** Intersect a piece with the chain `B_j^3`. Its steps have
    dimension at most `9N^2`, and its boundaries are at most `18N^2`.
  - **Centralizers.** Commutator rank is subadditive along words.
  - **Faithful approximations.** Residual finiteness of `G`
    (`ambient_residuallyFinite`) supplies the regular representations. Invariant
    subspaces of the sum meet `A^3 (+) 0` in invariant subspaces of `rho_N`.

`requires: []` is a proof commitment, not a placeholder.
