---
rg: 2
id: sl3z-level-15-subgroup-profinite-torsion-proof
kind: route
title: Determinants of involutions are squares mod 5; torsion in the congruence completion kills an elementary matrix
target: sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts
requires:
  - sl3z-finite-index-subgroups-are-congruence-subgroups
  - congruence-kazhdan-groups-satisfy-strong-atiyah
  - index-two-strong-atiyah-is-a-twisted-norm-equation
---

Notation as in the claim. Write `G = SL_3(Z)`, `A_0 = diag(-1,-1,1)`, and
`e_13(x)` for the elementary matrix.

**`P_5` and `chi`.**
- `P_5 = {diag(X, det X^-1)}`, where `X` runs over the Sylow 2-subgroup
  `C_4 wr C_2 = <diag(2,1), diag(1,2), [[0,1],[1,0]]>` of `GL_2(F_5)`. It has order
  32, and `|SL_3(F_5)| = 2^5 3 5^3 31`.
- `chi(M)` is the Legendre symbol of `det X`, so it is a homomorphism
  `P_5 -> Z/2`. Hence `S`, the graph of `M -> t^chi(M)`, is a subgroup of order 32.
- An involution `X` of `GL_2(F_5)` has `det X = +-1`, a square since `5 = 1 mod 4`.
  The block `X` of an involution `M` of `P_5` is an involution. So `chi` kills
  every involution of `P_5`.

**1. Torsion-free.**
- `H` is the preimage of `S` and contains `Gamma(15)`. Its index is
  `|SL_3(F_3)| |SL_3(F_5)| / 32 = 5616 * 372000 / 32`.
- Let `g` in `H` be torsion. Then `gbar = (g mod 3, g mod 5)` has the same order,
  because `Gamma(3)` is torsion-free. `S` is a 2-group, so the order is `2^j`.
- If `j >= 1`, a power of `g` is an involution `u` in `H`. Mod 3 and mod 5, `u`
  is an involution, since `Gamma(3)` and `Gamma(5)` are torsion-free.
- So `(u mod 3, u mod 5)` lies in `S` with second coordinate an involution. Then
  `chi = 0`, so the first coordinate is 1, contradicting `u mod 3 != 1`. So `j = 0`
  and `g = 1`.
- Property (T) passes to finite-index subgroups of `SL_3(Z)`.

**2. Ranks.** `N = H cap Gamma(3)` is the kernel of `H -> {1, t}`. This map is onto,
because `diag(2,1,3)` has `chi = 1`, so index 2. `N <= Gamma(3)` satisfies Strong
Atiyah over `C` by [[congruence-kazhdan-groups-satisfy-strong-atiyah]]. For `A` over
`C[H]`, `rk_(N(N))(res A) = 2 rk_(N(H))(A)` is an integer.

**3. No torsion-free profinite overgroup.** Suppose `iota : H -> W` is injective with
`W` profinite and torsion-free.
- By [[sl3z-finite-index-subgroups-are-congruence-subgroups]], the profinite
  completion of `H` is its closure
  `Hhat = {(g_l) in prod_l SL_3(Z_l) : (g_3 mod 3, g_5 mod 5) in S}`.
- `iota` extends to a continuous `pi : Hhat -> W`. The kernel `L` of `pi` is
  closed and normal, and it contains every torsion element of `Hhat`.
- For `y` in `Z_l`, `A_0 e_13(y) A_0^-1 = e_13(-y)`. So for torsion `tau` and any
  `g` in `Hhat`, `g tau g^-1 tau^-1` lies in `L`.

The key step builds, for each prime `l`, a torsion element `tau_l` of `Hhat` with
`l`-coordinate `A_0`. Then `g = e_13(x)`, placed in coordinate `l`, lies in `Hhat`
and gives `e_13(2x)` in `L`, again in coordinate `l`.
- **`l` not in `{3,5}`.** `tau_l = A_0` in coordinate `l` lies in `Hhat`, since
  there is no condition there. `x` is arbitrary.
- **`l = 5`.** `A_0 mod 5 = diag(4,4,1)` lies in `P_5` with `chi = 0`. So
  `tau_5 = A_0` in coordinate 5, with 1 in coordinate 3, lies in `Hhat`. Here
  `x` is in `5 Z_5`.
- **`l = 3`.** Let `zeta` in `Z_5` be the root of unity with `zeta = 2 mod 5`, and
  `w = diag(zeta, 1, zeta^-1)`, of order 4, with `w mod 5 = diag(2,1,3)` and
  `chi = 1`. Then `tau_3 = (A_0 at 3, w at 5)` has order 4 and lies in `Hhat`. For
  `g = e_13(x)` at 3 with `x` in `3 Z_3`, the commutator is `e_13(2x)` at
  coordinate 3, and 1 at 5.

`L` is closed, so it contains the full product of these elements, which is a limit
of finite partial products. Take `x = 15` in every coordinate. `15` lies in `3 Z_3`
and in `5 Z_5`, so `L` contains the image of `e_13(30)` in `G`. This element lies in
`Gamma(15) <= H` and is nontrivial, but `iota(e_13(30)) = pi(e_13(30)) = 1`. That
contradicts injectivity. Compact `p`-adic analytic groups are profinite.

**4.** `H` has finite index in `SL_3(Z)`, so every finite-index subgroup `U` of `H`
has property (T) and finite abelianization.
- **Locally indicable:** fails, since `H` itself does not map onto `Z`.
- **Class `C`:** a finitely generated group entering `C` as a directed union
  already occurs at an earlier stage. If it enters as an extension with
  elementary amenable quotient, that quotient has (T), so it is finite, and the
  kernel has finite index and (T). By induction, an infinite (T) group never
  reaches the free groups.
- **Virtually special:** fails. An infinite finitely generated subgroup of a RAAG
  is residually torsion-free nilpotent, so it has infinite abelianization.

**5.** `24` divides `65286000`. For `A` over `C[H]`, `rk_(N(H))(A)` equals
`[G:H]` times the rank of the induced matrix over `C[G]`, which lies in `(1/24)Z`.

**6.** Apply [[index-two-strong-atiyah-is-a-twisted-norm-equation]] to `N <= H`.

**Trust surface.** Residual torsion-free nilpotence of RAAGs, used in item 4 only,
is standard and was not re-read. Item 3 uses only the congruence subgroup property
and elementary matrix identities.
