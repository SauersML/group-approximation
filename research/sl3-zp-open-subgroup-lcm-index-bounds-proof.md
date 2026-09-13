---
rg: 2
id: sl3-zp-open-subgroup-lcm-index-bounds-proof
kind: route
title: A lifted Sylow 2-subgroup acts on cosets with small stabilizers, and 2-subgroups of GL_2(Q_2) have order at most 8
target: sl3-zp-open-subgroup-lcm-index-bounds-for-strong-atiyah
requires:
  - sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48
---

**Item 1.** Let `p` be odd and `W <= SL_3(Z_p)` open. Put
`n = [SL_3(Z_p) : W]`, `a = v_2(|SL_3(F_p)|)` and `b = v_2(lcm W)`.
- **A lifted Sylow subgroup.** As in step (b) of
  `sl3-zp-torsion-free-index-48-proof`, `a >= 4`. A Sylow 2-subgroup of
  `SL_3(F_p)` lifts to a finite `P <= SL_3(Z_p)` of order `2^a`, because the
  reduction kernel is pro-`p` (profinite Schur--Zassenhaus).
- **Small stabilizers.** `P` acts on `SL_3(Z_p)/W` by left multiplication. The
  stabilizer of `gW` is `P cap gWg^(-1)`, a 2-subgroup of a conjugate of `W`, so
  its order divides `2^b`.
- **Counting.** Each orbit `[P : P cap gWg^(-1)]` is divisible by `2^(a-b)` when
  `a >= b`. `n` is the sum of the orbit sizes, so `v_2(n) >= a - b`.

With `W` torsion-free, `b = 0`, and this is step (b) of the index-48 proof.

**Item 2.** Let `P <= SL_3(Q_2)` be a finite 2-group.
- **Summands have 2-power dimension.** A `Q_2`-irreducible representation of
  `P` has dimension `chi(1) m [Q_2(chi) : Q_2]`, where `chi` is an absolutely
  irreducible constituent.
  - `chi(1)` is a power of 2, and the Schur index `m` divides `chi(1)`.
  - `Q_2(chi) <= Q_2(zeta_|P|)` has 2-power degree.
  So `Q_2^3` splits as `1+1+1` or `2+1`.
- **`1+1+1`.** `P` acts on three lines by signs with product 1, so `|P| <= 4`.
- **`2+1`.** `P` acts on the line by the inverse of its determinant on the
  plane, so `P` embeds in `GL_2(Q_2)`.
- **Abelian `C <= GL_2(Q_2)`: `|C| <= 4`.** `Q_2[C]` is a commutative semisimple
  subalgebra of `M_2(Q_2)` acting faithfully on `Q_2^2`. So it is `Q_2`,
  `Q_2 x Q_2` or a quadratic field `L`. `C` lies in its roots of unity, whose
  2-parts have order 2, 4 and at most 4, because `[Q_2(zeta_8) : Q_2] = 4`.
- **Non-abelian `P <= GL_2(Q_2)`: `|P| <= 8`.**
  - **Absolutely irreducible.** Otherwise, by Maschke, the plane splits over
    `Qbar_2` into two lines and `P` is abelian.
  - **Small centre.** `Z(P)` acts by scalars in `Q_2`, so `Z(P) <= {+-1}`, and
    `Z(P)` is the kernel of `P -> PGL_2(C)`.
  - **Image.** The image is a finite 2-subgroup of `PGL_2(C)`, hence cyclic or
    dihedral, with a cyclic subgroup of index at most 2.
  - **Bound.** The preimage `C` of that subgroup is cyclic modulo the central
    `Z(P)`, so it is abelian and `|C| <= 4`. Hence `|P| <= 2|C| <= 8`.
- **The Iwahori.** `I` is pro-2, since `U` has order 8 and the reduction kernel
  is pro-2. So its finite subgroups are 2-groups of order at most 8. A
  conjugate of the dihedral group `D_8 <= SL_3(Z)` lies in `I`, as in item 1 of
  `sl3z-strong-atiyah-iwahori-denominator-8-proof`. So `lcm(I) = 8`, and
  `[SL_3(Z_2) : I] = 168/8 = 21`.

**Consequence.**
- **Density.** `SL_3(Z)` is dense in `SL_3(Z_p)` and `W` is open, so
  `SL_3(Z)/H -> SL_3(Z_p)/W` is a bijection for `H = W cap SL_3(Z)`.
- **Ranks.** Restriction to `H`, then induction from `H` to `W` (both from
  `sl3z-strong-atiyah-iwahori-denominator-8-proof`), give
  `rk(A) = rk_W(res A) / [SL_3(Z) : H]`.
- **Combining inputs.** A gcd of integers each divisible by 16 is divisible by
  16. Torsion-free inputs at `p = 2` are covered by
  [[sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48]].
- **`W = I`.** `gcd(8 * 21, 5616) = 24`.
