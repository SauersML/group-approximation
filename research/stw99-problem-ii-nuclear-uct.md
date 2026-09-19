---
rg: 2
id: stw99-problem-ii-nuclear-uct
kind: claim
title: All separable nuclear C*-algebras satisfy the universal coefficient theorem (STW Problem II)
root: true
distinct_from:
  stw99-problem-iii-r-omega-uct: that asks only for the single divisible target R-omega, where K_1 vanishes and K_0 is the reals; this is the full Rosenberg--Schochet UCT problem, which implies it (route stw99-uct-implies-r-omega-uct).
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
---

**Problem II of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Do all
separable nuclear C\*-algebras satisfy the Rosenberg--Schochet universal
coefficient theorem: for every `B` with `K_*(B)` divisible, the map
`α : KK(A, B) → Hom(K_*(A), K_*(B))` is an isomorphism?

Known positive classes: type I and ASH algebras (Rosenberg--Schochet),
C\*-algebras of second countable amenable groupoids (Tu; twisted with
torsion-free-quotient hypotheses by Barlak--Li), locally-UCT nuclear
algebras (Dadarlat: approximate containment of finite sets in UCT
subalgebras suffices).  In the non-nuclear world the answer is no
(Skandalis: `C*_r(G)` for biexact Kazhdan `G`).

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
the concentrated forms).  No approach is recorded here beyond the
literature; this node exists as the parent of Problems III, IV, V.
