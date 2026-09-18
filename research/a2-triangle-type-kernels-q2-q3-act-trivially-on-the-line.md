---
rg: 2
id: a2-triangle-type-kernels-q2-q3-act-trivially-on-the-line
kind: claim
title: For every triangle presentation of order 2 or 3, including the 65 exotic q=3 classes, the torsion-free index-3 Kazhdan type kernel has no nontrivial action on the line
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for lattices in p-adic groups of characteristic zero; this covers vertex-regular lattices on exotic Ã2 buildings (not linear over any field) and on the F_3((t)) and F_2((t)) buildings, by finite certificates
  exotic-a2-lattices-satisfy-boone-higman: that records the open Boone–Higman question for exotic Ã2 lattices; this is about actions of the q=2,3 vertex-regular ones on the line
  infinite-left-orderable-kazhdan-group: that asks for one infinite left-orderable Kazhdan group; this removes a named family of non-linear torsion-free Kazhdan candidates
artifacts:
  - experiments/a2-left-orderability-2026-09-17/gamma0_sat.py
  - experiments/a2-left-orderability-2026-09-17/complete_pg2.py
  - experiments/a2-left-orderability-2026-09-17/gamma0_q3_pre.out
  - experiments/a2-left-orderability-2026-09-17/complete_q3.out
---

**ESTABLISHED** by `a2-triangle-type-kernels-q2-q3-act-trivially-on-the-line-proof`
(finite computation plus imported CMSZ / CMS facts).

**Setup.** Let `(λ, T)` be a triangle presentation (Cartwright–Mantero–Steger–Zappa) over
the projective plane of order `q ∈ {2, 3}`. Let
`Γ_T = ⟨a_x | a_x a_y a_z = 1, (x,y,z) ∈ T⟩` be the group acting simply transitively on the
vertices of an Ã2 building, and let `Γ_0 = ker(Γ_T → Z/3, a_x ↦ 1)`.

**Statement.** Then:
1. `Γ_0` is an infinite torsion-free group with property (T), of index 3 in `Γ_T`.
2. Every homomorphism `Γ_0 → Homeo_+(R)` is trivial. In particular `Γ_0` is not
   left-orderable.
3. Every homomorphism `Γ_T → Homeo_+(R)` is trivial.

**Scope.**
- The statement covers all `PGL(3,q)`-orbits of triangle presentations:
  - 11 orbits for `q = 2`, i.e. the 8 CMSZ classes;
  - 133 orbits for `q = 3`, i.e. the 89 CMSZ classes.
- By Herron's classification (arXiv:2502.09536), the `q = 3` classes split into 65 exotic
  classes, 16 in `PGL(3,F_3((t)))` and 8 in `PGL(3,Q_3)`.
- By Bader–Caprace–Lécureux, the exotic ones have only finite linear images over any
  commutative ring.
- So statement 2 gives 65 non-linear infinite torsion-free Kazhdan groups acting trivially
  on the line. They are not covered by any Deroin–Hurtado-type theorem on main.
- It also gives the positive-characteristic ones. `higher-rank-p-adic-lattices-are-not-left-orderable`
  covers `Q_p` only.

**Why the type kernel.**
- For `q = 3`, point counting forces `(x,x,x) ∈ T` for some `x`: there are 52 arcs, and
  each triple `(x,x,x)` covers one arc, not three. So `Γ_T` has torsion and is trivially
  not left-orderable.
- Worse, for all 133 orbits the quotient of `Γ_T` by the normal closure of its torsion
  generators is finite. It is trivial for 90 orbits and has order at most 48 for the rest
  (GAP, `torsion_quotient.py`, `torsion_quotient_q3.out`). `Homeo_+(R)` is torsion-free,
  so statement 3 is cheap at `q = 3`.
- The meaningful Kazhdan candidate is the torsion-free `Γ_0`, and that is what the
  certificates constrain.

**Certificate shape.**
- A confluent length-2 rewriting system gives normal forms.
- A left-preorder SAT instance on the type-0 ball `B(3)` with factors `|h| ≤ 2` has 2262
  elements. It encodes `P, H, P^{-1}` as the moved-up, fixed and moved-down sets of a point
  moved by a Schreier generator.
- It is UNSAT for all 133 orbits with two solvers.
- The positive-cone version is already UNSAT on the 156 elements `a_x a_y^{-1}`.

**Not covered.**
- Finite-index subgroups of `Γ_T` other than `Γ_0`.
- Non-vertex-regular Ã2 lattices.
- Orders `q ≥ 4`.
- The certificate size is not uniform in `q`: at `q = 2` the radius-2 positive-cone
  instance is SAT for 5 of the 11 orbits, and radius 3 is needed. So no `q`-independent
  local argument is extracted.
