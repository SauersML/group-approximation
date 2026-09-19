---
rg: 2
id: fpbs-transverse-skeleton-ray-codes-are-match-rigid
kind: claim
title: On a torsion-free hyperbolic group, a ray code whose letters are basis letters of a malnormal quasiconvex free subgroup F interleaved with long F-transverse insertions in distinct F-double cosets is match-rigid as soon as its forward coding is injective, so every class it carries dies; an off-orbit match in such a skeleton code forces an insertion that fellow-travels a coset of F
distinct_from:
  fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups: that proves match rigidity (MR) kills every class carried by the rays and leaves (MR) as a hypothesis. This proves (MR) for a whole geometric family of codes on any torsion-free hyperbolic group, the skeleton-and-insertion codes that the transplant of the F_2 odometer produces, from coarse geometry of cosets alone.
  fpbs-odometer-killing-class-dies-by-support-rigidity: that proves (MR) inside F_2 from the free-group normal form and the odometer window geometry. Here no normal form of the ambient group exists; the proof aligns F-cosets exactly, through malnormality and the tree of F, and reads off (MR) from forward injectivity of the letter coding.
  fpbs-rotation-support-rigidity-kills-type-iii-classes: its Theorem C needs the rays inside the limit set of a quasiconvex free subgroup. Rays of a transverse skeleton code leave every quasiconvex limit set when the insertions are chosen as in fpbs-quasiconvex-null-lattice-odometer-class-dies.
---

**ESTABLISHED (written proof: `research/fpbs-transverse-skeleton-ray-codes-are-match-rigid-proof.md`).** The proof uses
standard coarse geometry of quasiconvex subgroups of hyperbolic groups (Morse lemma, local-to-global for piecewise
geodesics, bounded coarse intersection of cosets of malnormal quasiconvex subgroups) and the tree of a free group.

**Why this matters for the flagship.** The Bevilacqua--Bowen (BB) route to fixed price one for a cocompact `Sp(n,1)`
lattice needs an amenable, ergodic, PDR imp action whose boundary class passes every filter. By
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`, a ray code with (R), (MR) and (MR±) carries no such class. The
natural way to transplant the `F_2` odometer class to a lattice is a **skeleton code**: the `F_2` letters become the
basis letters of a malnormal quasiconvex free subgroup `F = <a, b>`, and killing elements are inserted at the odometer
windows to leave every quasiconvex limit set. This claim proves that every such code is match-rigid when its
insertions are transverse to `F`. So the whole transverse skeleton family is dead, and the only skeleton codes left
for a lattice certificate are those whose insertions fellow-travel cosets of `F` on unbounded lengths.

## Setting

`Gamma` is torsion-free, nonelementary and hyperbolic, with a fixed finite generating set, word length `|.|` and
hyperbolicity constant `delta`. `F = <a, b> <= Gamma` is free of rank 2 on `a, b`, **malnormal** and **quasiconvex**.
`I ⊂ Gamma` is a set of **insertion letters**, and `I^± = I ∪ I^{-1}`. Assume:

- **(I1) transversality.** For every `r >= 0` there is `D(r)` such that for every `s ∈ I^±` no subsegment of length
  `D(r)` of a geodesic `[1, s]` lies in the `r`-neighbourhood of a left coset `hF`.
- **(I2) distinct double cosets.** The double cosets `F s F`, for `s ∈ I^±`, are pairwise distinct.
- **(I3) length.** `|s| >= L_I` for all `s ∈ I^±`.

A **skeleton code** is an aperiodic Borel automorphism `(X_0, T)` with Borel letters
`G : X_0 -> {a^{±1}, b^{±1}} ∪ I^±` such that along every orbit:
- every maximal run of `F`-letters is a reduced word in `a, b` of length at least `L_F`;
- no two insertion letters are adjacent.

As in `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`, `c_k(x) = (G(x+1) ... G(x+k))^{-1}`, `P_x` is the path
through the vertices `c_k(x)^{-1}`, and `zeta(x) = lim c_k(x)^{-1}`.

## Theorem

**Theorem 2.** For every `F` and every function `D` there is `L_0 = L_0(Gamma, F, D)` such that the following holds
whenever `L_I, L_F >= L_0`.

1. **(R)** holds: every `P_x` is a uniform quasi-geodesic in both directions.
2. **(Exact matching.)** If `g zeta(x) = zeta(x')` with `x, x' ∈ X_0` and `g ∈ Gamma`, then there are `k, k'` with
   `G(x+k+t) = G(x'+k'+t)` for all `t >= 1`.
3. **(MR)** Hence, if the forward coding `y -> (G(y+t))_{t >= 1}` is injective on `X_0`, then `g zeta(x) = zeta(x')`
   forces `x' ∈ x + Z`. If moreover the code is symmetric (`G(-y) = G(y)^{-1}` on an odometer), (MR±) holds, and by
   Theorem 1 of `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups` every class carried by `Gamma zeta(X_0)` has a
   totally dissipative diagonal and is no BB boundary class.

**Corollary (where off-orbit matches must come from).** Let a skeleton code satisfy (I2) and have forward-injective
coding, and suppose it has an off-orbit match `g zeta(x) = zeta(x')`, `x' ∉ x + Z`. Then for every function `D`,
either (I1) fails for `D`, or `min(L_I, L_F) < L_0(Gamma, F, D)`. So a skeleton code with arbitrarily long pieces and
off-orbit matches must have insertions that fellow-travel cosets of `F` on unbounded lengths at some fixed scale `r`.
The proof shows more. At a match, some `F`-stretch of one ray is shadowed by a piece of an insertion of the other ray
(step 2 below is where the match must break).

## Mechanism

1. Junction Gromov products between an `F`-piece and an insertion are bounded by (I1). With long pieces,
   local-to-global makes every ray a uniform quasi-geodesic.
2. Two rays with a common endpoint fellow-travel. Each long `F`-piece `sigma` of one ray is shadowed by a stretch
   `pi` of the other. `pi` contains no whole insertion, by (I1) and (I3). So it lies in one `F`-piece `sigma'`, up to
   two ends of length `< D`.
3. Distinct cosets of the malnormal quasiconvex `F` have bounded coarse intersection. So `sigma` and `sigma'` lie in
   the **same** coset. Pulled back to the tree of `F`, two long fellow-travelling geodesics share a vertex. This is an
   **exact** common vertex of the two rays.
4. From a common vertex, the next cosets agree: `w_1 s F = w'_1 s' F` with `w_1, w'_1 ∈ F`. Then (I2) gives `s = s'`,
   and malnormality (`F ∩ s F s^{-1} = 1`) gives `w_1 = w'_1`. Induction makes all later letters agree.

## Calibration

- **`F_2` itself.** Take `Gamma = F_2 = <x, y>` and `F = <y, yxxyx>`. This `F` is malnormal of rank 2, and no power
  of `x` is conjugate into it (certificate: `experiments/transverse-odometer-lattice-2026-09-17/malnormal_search.py`,
  output `malnormal_search.out`). Insertions from the semigroup of
  `fpbs-quasiconvex-null-lattice-odometer-class-dies` give a symmetric skeleton code on `F_2`. Theorem 2 makes it
  match-rigid, consistent with `F_2` having no BB certificate (cost 2).
- **Where it must fail.** For a closed surface group, the Lebesgue class has a conservative diagonal. So no skeleton
  code with (I1)--(I3), long pieces and forward-injective coding carries Lebesgue measure. Nothing contradicts this.
  Rays of such a code spend all their time in stretches of at least `L_F` inside single cosets of `F`, or on insertions
  that leave every coset after `D` steps. A Lebesgue-typical geodesic has neither rigid pattern.
- **Why (I1) is needed.** Without (I1), an insertion can contain a long `F`-stretch. An `F`-piece of one ray can then
  match inside an insertion of the other, and step 3 breaks. This is exactly the obstacle named in the open statement
  of `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`.

## What this leaves (named open statement)

**Non-transverse insertions.** Is there a symmetric skeleton code on a torsion-free cocompact `Sp(n,1)` lattice, with
quasiconvex-null class, whose insertions violate (I1) and which has a positive-measure set of off-orbit matches? By
Theorem 2, this is the only way a skeleton code can escape `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`. It
is a necessary feature of any skeleton-code BB certificate on a lattice.
