---
rg: 2
id: literal-group-local-lifting-property
kind: claim
title: The full C*-algebra of the literal group has Kirchberg's local lifting property
refuted_by: [literal-group-fails-local-lifting-property]
distinct_from:
  literal-group-factorization-property: that is amenability of the canonical trace; this is the lifting property of the whole algebra C*(E), which together with hyperlinearity of E implies it (route literal-fp-via-llp) and is strictly stronger in general.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

`C*(E)` has Kirchberg's local lifting property (LLP): every unital completely
positive map from a finite-dimensional operator subsystem of `C*(E)` into a
quotient `B/J` lifts to `B`.  Equivalently for separable algebras, every
`*`-homomorphism from `C*(E)` into a quotient lifts locally to u.c.p. maps.

Known for free groups (Kirchberg), amenable groups, and by
Fournier-Facio--Willett (arXiv:2603.18456) for limit groups, 3-manifold groups,
certain one-relator groups and right-angled Artin groups.  Their permanence
list: LLP passes to subgroups (Cor. 3.17) and to directed unions (Cor. 3.19),
survives semidirect products by amenable groups (Cor. 3.21), amalgamated free
products and HNN extensions over **finite** subgroups (Cor. 3.24, Prop. 3.26),
central extensions by finite groups (Thm. 3.36) and extensions with amenable
kernel (Thm. 3.37).

`E` is a finitely presented HNN-type extension whose stable letter compresses
an **infinite** Kazhdan subgroup `L` (`t L t⁻¹ ≤ L`).  More decisively, the
split normal form exhibits a subgroup `SL_3(Z) < E`.  Ioana--Spaas--Wiersma,
Corollary B (arXiv:2006.01874), prove that `C*(SL_3(Z))` fails LLP, while their
Remark 1.2 proves that LLP of full group C*-algebras passes to subgroups.
Consequently `C*(E)` cannot have LLP.

Why LLP suffices for the route: Brown's amenability criterion is local (finite
set, `ε`), and LLP lifts u.c.p. maps from finite-dimensional operator
subsystems of `C*(E)` into `∏M_k/J_HS` to u.c.p. maps into `∏M_k`, which
Arveson extends to `C*(E)`.

**REFUTED** by `literal-group-fails-local-lifting-property`.  Therefore the
conditional route `literal-fp-via-llp` is dead; this does not decide the
factorization property itself, since LLP is sufficient but not necessary for
that property.
