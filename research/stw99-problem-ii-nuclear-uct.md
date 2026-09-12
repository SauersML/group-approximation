---
rg: 2
id: stw99-problem-ii-nuclear-uct
kind: claim
title: All separable nuclear C*-algebras satisfy the universal coefficient theorem (STW Problem II)
root: true
refuted_by:
  - nuclear-algebra-without-uct-exists
distinct_from:
  stw99-problem-iii-r-omega-uct: that asks only for the single divisible target R-omega, where K_1 vanishes and K_0 is the reals; this is the full Rosenberg--Schochet UCT problem, which implies it (route stw99-uct-implies-r-omega-uct).
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**Problem II of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Do all
separable nuclear C\*-algebras satisfy the Rosenberg--Schochet universal
coefficient theorem: for every `B` with `K_*(B)` divisible, the map
`α : KK(A, B) → Hom(K_*(A), K_*(B))` is an isomorphism?

Known positive classes: type I and ASH algebras (Rosenberg--Schochet),
C\*-algebras of second countable amenable groupoids (Tu), nuclear reduced
algebras of twisted étale groupoids and hence all separable nuclear algebras
with a Cartan subalgebra (Barlak--Li Theorem 1.1 and Corollary 1.2, recorded in
`barlak-li-cartan-subalgebras-force-uct`; the printed theorem carries no torsion
hypothesis), locally-UCT nuclear algebras (Dadarlat: approximate containment of
finite sets in UCT subalgebras suffices), and algebras decomposing over nuclear
UCT algebras (`willett-yu-decomposability-forces-uct`).  In the non-nuclear
world the answer is no (Skandalis: `C*_r(G)` for biexact Kazhdan `G`).

**Graph structure (stw-uct lane, 2026-09-11).**  Four live routes now target
this claim, each waiting on open claims:

* `stw99-ii-via-trivial-k-kirchberg-algebras`, through
  `trivial-k-theory-kirchberg-algebras-are-o2` (Kirchberg);
* `stw99-ii-via-complexity-rank-one`, through
  `trivial-k-kirchberg-algebras-have-complexity-rank-one` (Willett--Yu,
  Jaime--Willett);
* `stw99-ii-via-tracially-af-rational-k0`, through
  `tracially-af-rational-k0-algebras-are-universal-uhf` (Dadarlat);
* `stw99-ii-via-coprime-uhf-absorbing-cases`, through the two UHF-localized
  halves `uct-for-two-infinity-absorbing-nuclear-algebras` and
  `uct-for-three-infinity-absorbing-nuclear-algebras`.  The splitting theorem
  `coprime-uhf-stabilizations-detect-uct` is proved here.  The half at 2 is
  equivalent, by Barlak--Li Theorem 1.8, to
  `o2-z2-actions-fix-a-cartan-subalgebra`.

The negation is `nuclear-algebra-without-uct-exists`, which lists what a witness
must avoid.  Problem II implies Problem IX(1) (`stw99-ii-implies-ix1`), so a
non-quasidiagonal nuclear algebra with a faithful trace would refute it.  The
verified sources, theorem numbers and the lane's plan are in
`research/artifacts/stw-uct-reduction-map-2026-09-11.md`.

## Attempts

Recorded reductions, each an established route in the graph or a cited
fact: (i) if the UCT passes to quotients of nuclear algebras it holds for
all (cones are contractible); (ii) Kirchberg: it suffices to handle
crossed products of nuclear algebras by `T`, or by `Z/p` and `Z/q` for
coprime `p, q`; (iii) Kirchberg: it suffices to handle Kirchberg
algebras, and via mapping cones plus Kirchberg--Phillips the problem is
equivalent to every Kirchberg algebra with trivial K-theory being `O_2`;
(iv) Winter's microcosm: the strongly self-absorbing case is Problem
XIII (`stw99-problem-xiv2-ssa-embeds-in-q-oinfty` and its finite part are
the concentrated forms).  This node is also the parent of Problems III, IV, V.

Dead ends on the negative side (uct-problem lane, 2026-09-12; details in
`research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md`):

* **Equivariant K-theoretic classification.**  An outer strongly approximately
  inner `Z_(p^n)`-action on `O_2` that is `KK^G`-equivalent to an action on a
  type I algebra fixes a Cartan subalgebra
  (`bootstrap-class-zp-actions-on-o2-fix-a-cartan`).  Cartan-fixing holds at every
  prime or at most one (`o2-zp-cartan-fixing-all-primes-or-at-most-one`).  So a
  witness needs, at all primes but at most one, an action outside the equivariant
  bootstrap class, which Köhler, Meyer--Nadareishvili and Gabe--Szabó cannot
  name.  Dies there.
* **Property (T) compression rigidity.**  The mechanisms behind this
  repository's non-MF and nonsofic theorems live on non-amenable groups, whose
  group C\*-algebras are not nuclear.  Dies at nuclearity.
* **Ozawa's Kazhdan projections** (arXiv:2609.08892,
  `hyperfinite-factor-not-quasidiagonal`).  Corrected 2026-09-12: the
  non-quasidiagonal trace there is `τ_R`, which is faithful, so faithfulness is
  not what fails; exactness is (R is not exact).  The MF-tensor certificate
  `nuclear-factor-with-infinite-mf-tensor-exists` (route
  `nuclear-non-uct-via-infinite-mf-tensor`) is refuted (2026-09-12) by
  `mf-min-tensor-exact-stably-finite-is-stably-finite`: an MF algebra tensored
  with any exact algebra with stably finite unitization is stably finite, so no
  nuclear second factor with a faithful trace can carry the proper isometry.
  The refutation uses no UCT input.  Dies at exactness.  Details:
  `research/artifacts/uct-fresh-mf-tensor-route-2026-09-12.md` and
  `research/artifacts/uct-nuclear-proper-isometry-2026-09-12.md`.
