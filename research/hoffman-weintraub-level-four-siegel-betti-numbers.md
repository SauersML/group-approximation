---
rg: 2
id: hoffman-weintraub-level-four-siegel-betti-numbers
kind: claim
title: The principal level-four congruence subgroup of Sp_4(Z) has rational Betti numbers 1, 0, 118, 1112, 481
distinct_from:
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that computes Levi-invariant second cohomology of the Siegel and Klingen unipotent radicals; this is the full rational cohomology of the level-four congruence subgroup itself.
---

**ESTABLISHED by citation** (`hoffman-weintraub-level-four-siegel-betti-numbers-citation`).
J. William Hoffman and Steven H. Weintraub, *Cohomology of the Siegel modular
group of degree two and level four*, preprint PDF
`https://www.math.lsu.edu/~hoffman/papers/level4.pdf`, Theorem 1.2.

**Imported statement.** Let `Gamma_2(4) = ker(Sp_4(Z) -> Sp_4(Z/4))`. Then

```text
dim_Q H^i(Gamma_2(4); Q) = 1, 0, 118, 1112, 481   for i = 0,1,2,3,4,
                           0                       for i >= 5.        (HW1)
```

**Consistency check (done here, not imported).** The alternating sum is
`1 - 0 + 118 - 1112 + 481 = -512`, which matches Harder's Gauss--Bonnet value
`zeta(-1) zeta(-3) [Sp_4(Z) : Gamma_2(4)] = (-1/12)(1/120)(737280) = -512`,
with `|Sp_4(Z/4)| = 4^10 (1 - 2^-2)(1 - 2^-4) = 737280`. The paper states the
same check verbatim (see the citation route).

**Use.** The only input needed downstream is `dim H^2(Gamma_2(4); Q) = 118 >= 2`,
used in `genus-two-cover-lattices-fail-bracket-t2`.
