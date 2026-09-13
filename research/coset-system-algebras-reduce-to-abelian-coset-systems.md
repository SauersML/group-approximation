---
rg: 2
id: coset-system-algebras-reduce-to-abelian-coset-systems
kind: claim
title: Conjecture - after support fixpoint and holonomy pruning, every coset system over finite groups admits an affine abelian relabeling
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-relabeling-conjecture-2026-09-13.md
  - research/artifacts/ex-kac-quantum-compiler-relabeling-collapse-2026-09-13.md
distinct_from:
  relabelable-coset-systems-are-solution-group-corners: that proves collapse onto a solution group for systems that admit an affine relabeling; this conjectures that every coset system with nonzero algebra admits one after pruning, which would make every coset-system gap goal-level.
  exact-label-coset-refinements-are-affine: that treats coset refinements of Boolean context games whose blocks are exactly the shared-variable fibres; this concerns arbitrary coset systems over arbitrary finite groups, with no Boolean source and no label exactness.
  tracial-non-ru-coset-system-with-nonabelian-fibre-exists: that asks for a gap with a nonabelian fibre image; this asks whether the algebra of every such system is already the algebra of a coset system over abelian groups.
---

**OPEN.**  Let `S` be a coset system (as in
`coset-systems-are-torsor-isomorphism-games`) with `A(S) != 0`.  Prove or
refute: there is a coset system `S^ab` over finite abelian groups with
`A(S) ≅ A(S^ab)`.  The expected construction:
- apply the support fixpoint and holonomy pruning below, which leave the
  algebra unchanged;
- then find an affine relabeling.

**If true.**  By `relabelable-coset-systems-are-solution-group-corners`
every coset-system gap is a finitely presented nonhyperlinear group, and
coset syntax never goes beyond `non-hyperlinear-group`.

**If false.**  A counterexample is the first syntax where nonabelian local
structure is visible to the algebra.

## Attempts

- **Proved reductions (artifact, §§1--2).**
  - **(N1) Support fixpoint.**  Goursat relations restrict to Goursat
    relations.  Iterating reaches a normal form: fibres are groups,
    partitions are by normal subgroups, identifications are affine
    bijections of quotient groups.
  - **(N2) Holonomy pruning.**  A cycle of identifications through one common
    section `Θ` acts on the coarse PVM by an affine map `h`, and forces
    vanishing off `Fix(h)`.  Fixed sets of affine maps `x |-> a α(x) b` are
    cosets, so pruning keeps normal form and trivializes the holonomy on the
    support.
  - **(A1)** A single Goursat relation is relabelable.
  - **(A2)** For two normal subgroups, `K/(N_1∩N_2)` is the full fibre
    product over `K/N_1N_2`.  So compatible labelings of the two quotients
    extend.
  - **(A3)** A diamond `N_1, N_2, N_3` of normal subgroups has abelian section
    `T/B`.  So non-distributive interlocking happens only on abelian
    sections, where the true group structure is a labeling preserved by all
    isomorphisms.
- **Where a proof is not yet written (artifact, §3).**
  1. Distributive families of more than two normal subgroups in one fibre,
     with prescribed labelings on their maximal quotients.
  2. A nonabelian section occurring as a common quotient in several fibres,
     through different extensions.
  3. Cycles that do not pass through one common section, where transport is
     a relation and (N2) does not apply directly.
  A counterexample has to live in one of these.
- **Small checks, done by hand.**  Every configuration below is relabelable.
  - Fibres `S_3`, `Q_8`, `D_4`, `S_4`, `A_5`, `S_3 x S_3` with all their
    normal-subgroup partitions.
  - Triangles of fibre bijections.
  - A fibre product `Ξ x_Θ Ξ` with a triangle of automorphism
    identifications.
  These are not a proof.
