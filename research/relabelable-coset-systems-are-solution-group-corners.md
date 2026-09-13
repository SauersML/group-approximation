---
rg: 2
id: relabelable-coset-systems-are-solution-group-corners
kind: claim
title: A coset system whose relation sets become abelian cosets after relabeling each fibre is a corner of a finitely presented group algebra, so its gap gives a nonhyperlinear group
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-relabeling-collapse-2026-09-13.md
distinct_from:
  coset-systems-are-torsor-isomorphism-games: that computes the torsor isomorphism algebra and shows the symmetry is not a group dual once a fibre image is nonabelian; this shows the algebra carrying the gap depends only on the relation sets, and collapses onto a solution group whenever those sets are abelian cosets after relabeling.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the binary linear-system endpoint; this transfers the tracial/non-R^U-to-nonhyperlinear direction to coset systems over arbitrary finite groups admitting an affine relabeling.
  tracial-non-ru-coset-system-with-nonabelian-fibre-exists: that asks for a gap with a nonabelian fibre image; this proves that every relabelable instance of it is goal-level, so a gap beyond the goal needs a system with no affine relabeling.
---

**ESTABLISHED** by `relabelable-coset-systems-are-solution-group-corners-proof`.
It has not been reviewed by an ex-verify lane.

**Setting.**  `S` is a coset system: finite groups `K_q`, and relation sets
`R_(qq') = c_(qq') D_(qq')` for `(q,q') in E`, as in
`coset-systems-are-torsor-isomorphism-games`.  An *affine relabeling* is a
family of abelian groups `A_q` with bijections `β_q : K_q -> A_q` such that
every `(β_q x β_(q'))(R_(qq'))` is a coset of a subgroup of `A_q x A_(q')`.

**Theorem.**  Suppose `S` admits an affine relabeling, and let `n` be the
least common multiple of the exponents of the `A_q`.
1. `A(S) ≅ A(S^β)`: the algebra sees only the relation sets.
2. `A(S^β) ≅ p_ω C^*(Γ)` for a finitely presented group `Γ` with a central
   `J` of order `n`, where `p_ω = (1/n) sum_j ω^(-j) J^j`.
   - Generators: `x_(q,χ)` for `χ in Â_q`, and `J`.
   - Relations: `Â_q` inside each fibre, `J` central with `J^n = 1`, and
     `x_(q,χ) x_(q',χ') = J^k` whenever `(χ,χ')` annihilates `D^β_(qq')`,
     where `ω^k = (χ (x) χ')(c^β_(qq'))`.
3. If `S` is tracial and not `R^U`, then `Γ` is not hyperlinear.

**Meaning.**  The torsor pair of a relabelable system can have non-group-dual
quantum symmetry, but the gap it carries is exactly a solution-group gap.  The
same algebra is the linking algebra of the torsor pair over the abelian
`A_q`, and that pair's symmetry is a group dual.  So nonabelian fibres by
themselves do not put a gap beyond `non-hyperlinear-group`.

**Relabelable examples.**
- All fibres abelian.
- An unconstrained nonabelian fibre adjoined to a linear system.
- Nonabelian fibres whose relations are agreement of abelian quotients with
  affine identifications.
- Every single Goursat relation is relabelable.  An obstruction can only come
  from several quotient partitions of one fibre interlocking around cycles of
  the constraint graph.

**Not decided.**
- No coset system with nonzero algebra is shown to be non-relabelable.
- Relabelability is a sufficient condition for collapse, not an invariant of
  the algebra.
