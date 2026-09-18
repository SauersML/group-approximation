---
rg: 2
id: deligne-cover-compression-defects-are-trivial
kind: claim
title: Every compression--centralizer defect of every subgroup of every Deligne cover is trivial, so the manuscript's non-MF mechanism is silent on E_3
distinct_from:
  compression-defect-dies-in-finite-dimensions: that kills the defect inside every finite-dimensional representation; this proves the defect itself is trivial in the source group, for groups that are not linear and not residually finite, by lifting the finite-dimensional kill through the Guichardet--Wigner quasimorphism.
  compression-defects-die-in-rigid-targets: that kills the image of the defect in finite or linear targets; this is a source-side vanishing for central extensions of linear groups whose extension class is bounded.
  mf-group-with-finite-central-compression-defect: that exhibits a finite central subgroup inside a compression defect; this shows no Deligne cover and no subgroup of one can carry such a defect, however the subgroup L is chosen.
  sp4-deligne-rigid-infinite-index-subgroup-exists: that asks for a thin subgroup on which the Deligne class stays virtually nonzero; this shows that even such a subgroup, Kazhdan or not, gives a trivial compression defect.
---

**ESTABLISHED.** Let `g >= 1`, `G^` the universal cover of `Sp_(2g)(R)`,
`ker p = <zeta> = Z`, `Z^ = Z(G^)`, and `C <= Z^`. Put `H = G^/C`. For every
subgroup `Delta <= H` and every `L <= Delta`, write

```text
Comp(L) = { s in Delta : s L s^-1 <= L },   G_comp(L) = < Comp(L) >,
D(Delta,L) = << [ x c x^-1, l ] : x in G_comp(L), c in C_Delta(L), l in L >>_Delta,
```

which is the larger (group-generated) defect of
`compression-defect-dies-in-finite-dimensions`. It contains the defect
`D_Delta(L)` of tex eq. (intrinsic-defect). Then

```text
D(Delta, L) <= (Tors(Z^) C)/C,  a central subgroup of order <= 2;      (CD1)
D(Delta, L) = 1   if  C <= ker p   or   C >= Tors(Z^).                 (CD2)
```

**Instances.**
- **(CD3) Every subgroup of every Deligne cover.** For each `n`, the Deligne
  cover `Gamma_n` is the preimage of `Sp_(2g)(Z)` in `G^/<zeta^n>`. Here
  `C = <zeta^n> <= ker p`. So `D(Delta, L) = 1` for every `Delta <= Gamma_n`
  and every `L <= Delta`. For `g = 2`, `n = 3`, this covers
  `E_3 = Gamma_3`, all its finite-index subgroups, and every subgroup,
  Kazhdan or not, thin or not.
- **(CD4) Central quotients of `E_3` keeping `z`.** If `N <= Z(E_3)` and
  `z not in N`, then `D(E_3/N, L) = 1` for every `L`.

**Class killed.** The compression-defect mechanisms are:
- `normal-kazhdan-defect-non-mf`;
- `finite-normal-compression-obstruction`;
- `central-defect-element-mf-image-is-trivial-or-infinite`;
- `locally-finite-defect-subgroup-dies-in-every-corona`;
- `compression-defect-dies-in-mf-under-mark-stability`;
- the manuscript's Theorem compression-criterion and Corollary defect-hs.

Each needs a nontrivial element of some `D(Delta, L)`. `Delta` is the
source group, or the image group in the image-side use of the central-defect
route. The step where every member dies is "exhibit
`1 != w in D(E_3, L)`". By (CD3) and (CD4) no such `w` exists, for any `L`.
By the remark below, the same holds in any image of `E_3` that keeps `z`.

The invariant is the Guichardet--Wigner homogeneous quasimorphism. It
vanishes on every central commutator, by
`sp2g-central-commutators-of-universal-lifts-are-torsion`. The
finite-dimensional kill (Lean `compressionCentralizerDefect_le_ker`)
already makes each defect generator a commutator of a pair that commutes
modulo the center. The quasimorphism then makes that commutator torsion.

**What survives.** This is the mechanism behind the graph's unconditional
non-MF examples (binary Leavitt, commuting lamp, integral Jacobson). A proof
of the goal must therefore leave it:
- **Norm-corona spectral data.** A proof can use operator-norm information
  that no compression defect encodes. This is the Wave 6 calibration.
- **An ambient group.** A proof can go through an overgroup
  `Delta >= E_3` in which `z` lies in a defect. Non-MF of an overgroup does
  not descend, so that route also needs an extension theorem for the
  corona representations of `E_3`.

Derivation: `deligne-cover-compression-defects-are-trivial-proof`.
