---
rg: 2
id: torsion-free-hyperbolic-mod-p-classes-die-virtually
kind: claim
title: On a torsion-free hyperbolic group every mod-p class of degree at least three dies on a finite-index subgroup
distinct_from:
  every-hyperbolic-group-is-good: that is goodness of every hyperbolic group, all degrees and all finite modules, and it contains Gromov's question; this is only degrees at least three, trivial F_p coefficients, torsion-free groups, and it says nothing about residual finiteness or torsion
  good-groups-have-no-persistent-finite-cohomology: that proves effacement for groups already known to be good; this asks for effacement on torsion-free hyperbolic groups that are not known to be good, such as Kazhdan ones
  persistent-degree-two-class-on-hyperbolic-group: that asks for a persistent degree-two class, which is equivalent to a non-residually-finite finite-kernel extension; this concerns only degrees at least three, where no extension-theoretic or residual-finiteness reformulation is known
artifacts:
  - research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md
---

**OPEN.** For every torsion-free word-hyperbolic group `H`, every prime `p`, every
`q >= 3` and every class `x in H^q(H;F_p)` with trivial action, prove that there is a
finite-index subgroup `W <= H` with `res^H_W(x) = 0`.

A torsion-free hyperbolic group has a finite `K(H,1)` (the Rips complex). So only
`3 <= q <= cd H` matters, and the claim is vacuous when `cd H <= 2`.

**Role.** Route [[every-hyperbolic-group-good-via-rf-and-high-degrees]] shows that this
claim, together with [[hyperbolic-finite-residual-is-torsion-free]], implies
[[every-hyperbolic-group-is-good]]. Conversely, universal goodness implies both inputs:
this claim by [[good-groups-have-no-persistent-finite-cohomology]], and the other by
`good-cocompact-proper-groups-are-virtually-torsion-free` with
`universal-hyperbolic-vtf-iff-rf`. The converse is recorded in prose only (artifact,
Theorem 4). So, relative to Gromov's question, this is exactly what universal goodness
adds.

By Lemma 3.2 of the artifact, the trivial `F_p` case already gives effacement for every
finite coefficient module, uniformly over any class of groups closed under finite-index
subgroups.

## Attempts

- **Special cube complexes (2026-09-16, swarm lane every-hyperbolic-group-is-good).**
  Kropholler--Wilkes goodness (arXiv:1603.07197, Theorem 9) handles every hyperbolic
  virtually compact special `H`. By Agol's theorem (recalled), that includes every
  hyperbolic group acting properly and cocompactly on a CAT(0) cube complex, such as
  free groups, surface groups and closed hyperbolic 3-manifold groups. It stops at groups
  with no such cubulation, notably Kazhdan groups. This is the same wall as in the Attempts
  of `every-hyperbolic-group-is-good`.
- **Ideal reduction.** For each `p`, the effaceable classes form a two-sided ideal of
  `H^*(H;F_p)`. If every hyperbolic group is residually finite, that ideal contains
  `H^1` and `H^2` (artifact, Lemmas 2.1-2.2). It then suffices to efface one
  representative of each indecomposable class in degree `>= 3`. **Where it dies.**
  Indecomposables in degree `>= 3` exist. For example, the top class of a closed
  hyperbolic 3-manifold with `H_1(M;F_p) = 0` is not a product. So the reduction gives no
  general proof.
- **Pullback from better groups.** If `x = f^*(c)` and `c` is effaceable on `Γ`, then `x`
  is effaceable. Good cubulated targets `Γ` are useless for Kazhdan `H`: by the
  fixed-point property (Niblo--Reeves, recalled), such maps have finite image, and then
  `x` is inflated from a finite quotient and effaced on the kernel by definition.
  Hyperbolic targets of small vcd would require a map that is nonzero on a class of
  degree `> vcd Γ`. We know no construction of such a map.
- **Top degree of Poincare duality groups.** If `H` is an orientable `PD^n` group over
  `F_p`, restriction to an index-`d` subgroup is multiplication by `d` on `H^n(H;F_p)`.
  So the top class is effaceable iff `H` has a finite quotient of order divisible by `p`.
  If every hyperbolic group is residually finite, this holds for non-elementary `H`: a
  deep Dehn filling `H/<<g^m>>` with `p | m` is hyperbolic and has an element of order
  `p`. **Where it dies.** Only the top degree is reached. Degrees `3..n-1` are untouched.
- **Natural test case, not attempted computationally.** Torsion-free cocompact lattices
  in `Sp(n,1)` (`n >= 2`) and `F_4^(-20)` are hyperbolic, Kazhdan and linear, hence
  residually finite, with `cd >= 8`. For such a lattice `Γ`, goodness of `Γ` is
  equivalent to this claim for `Γ` and its finite-index subgroups *together with*
  residual finiteness of every finite-module extension of a torsion-free finite-index
  subgroup (artifact, Corollary 2.3 and its converse paragraph, and Lemma 3.2). Residual
  finiteness of `Γ` alone does not supply the degree-two half (referee correction,
  2026-09-16). Searches on 2026-09-16 found no source deciding goodness for these lattices. A
  persistent class on one of them in some degree `3 <= q <= cd` would refute
  `every-hyperbolic-group-is-good` without touching Gromov's question.
