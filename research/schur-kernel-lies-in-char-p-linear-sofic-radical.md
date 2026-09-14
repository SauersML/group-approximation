---
rg: 2
id: schur-kernel-lies-in-char-p-linear-sofic-radical
kind: claim
title: The Schur kernel of a nonsingular adjunction lands in the characteristic-p rank radical of central extensions by finite groups of order prime to p
distinct_from:
  schur-kernel-lies-in-hyperlinear-radical: that is the tracial radical, where Gerstenhaber--Rothaus supplies roots and spectral projections cut the center; this is the radical of rank ultraproducts over algebraically closed fields of characteristic p, for finite centers of order prime to p, where no root theorem is known.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

**OPEN.** Let `p` be a prime and `1 -> Z -> E -> Q -> 1` a central extension of countable groups with `Z` finite of
order prime to `p`, class `alpha`, and evaluation `alpha_H : H_2(Q; Z) -> Z`. For every `w in Q * <t>` with nonzero
`t`-exponent sum,

```text
alpha_H( ker( H_2(Q) -> H_2((Q * <t>)/<<w>>) ) )  <=  Rad_rk,p(E),
```

where `Rad_rk,p(E)` intersects the kernels of all homomorphisms from `E` into unit groups of rank ultraproducts of
matrix algebras over algebraically closed fields of characteristic `p`.

**Payoff.** For Deligne's triple cover and `p != 3`, together with `sp4-schur-kernel-meets-the-deligne-triple-class`
this gives `deligne-central-mark-dies-in-char-p-rank-models`, so `E_3` is not `F_p`-linear sofic.

## Attempts

- **From rank root solvability: proved.** `char-p-schur-radical-from-rank-root-solvability` derives this from
  `rank-ultraproduct-unit-groups-solve-nonsingular-equations` (artifact Theorem 3.4). The isotypic cut to a central
  character is exact because `|Z|` is invertible in `Fbar`. The class comparison is S2 of the tracial Schur-kernel
  artifact with rank roots in place of unitary roots.
- **Unconditionally: nothing.** The only input missing is the root property of the targets. No characteristic-`p`
  degree argument is known.
