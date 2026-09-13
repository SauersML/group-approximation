---
rg: 2
id: closed-mcg-v-nonembedding-via-koberda
kind: route
title: Large powers of three twists generate Z² ∗ Z inside any finite-index subgroup, and Z² ∗ Z does not embed in V
target: closed-mcg-finite-index-subgroups-do-not-embed-in-v
requires: []
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

**Imports.** Both were read from the PDFs on 2026-09-12.
1. **Koberda.** T. Koberda, *Right-angled Artin groups and a generalized
   isomorphism problem for finitely generated subgroups of mapping class
   groups*, arXiv:1007.1118v4.
   - **Setting, page 2.** `Σ_{g,p}` has genus `g`, `p ≥ 0` punctures, and
     `χ(Σ) = 2 − 2g − p < 0`. `Mod_{g,p}` is "the group of
     orientation–preserving self–homeomorphisms of Σ which preserve the set of
     punctures, up to isotopy". `A(Γ) = ⟨V | [v_i, v_j] whenever (v_i, v_j) ∈ E⟩`.
   - **Graph, pages 2--3.** The vertices of the graph `Γ` are the elements of
     `F`, joined by an edge "if and only if the supports can be realized
     disjointly. This graph is called the coincidence correspondence of F."
   - **Theorem 1.1, page 3.** "Let {f1,…,fk} ⊂ Mod_{g,p} be an irredundant
     collection of Dehn twists or pseudo-Anosov homeomorphisms supported on
     connected subsurfaces of a given surface. Then there exists an N such that
     for each n ≥ N, the set of mapping classes {f1^n,…,fk^n} is a right-angled
     Artin system for a right-angled Artin subgroup of Mod_{g,p}. The
     isomorphism type of this right-angled Artin group is given by A(Γ), where Γ
     is the coincidence correspondence of {f1,…,fk}."
   - **Irredundancy, page 3.** "irredundancy is equivalent to the requirement
     that no two mapping classes {fi, fj} for i ≠ j generate a cyclic subgroup
     of Mod_{g,p}."
2. **Survey.** Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, Theorem 4.6,
   page 11:
   "The following groups do not embed into Thompson's group V : (1)
   (Bleak–Salazar-Díaz 2013 [20]) The free product Z² ∗ Z". Here [20] is C.
   Bleak and O. Salazar-Díaz, *Free products in R. Thompson's group V*, Trans.
   AMS.

**Standard input (F).** Farb--Margalit, *Primer*, Chapter 3; statement numbers
were not re-checked.
- Dehn twists about essential curves have infinite order.
- Twists about disjoint curves commute.
- `T_a^j = T_b^k` with `j, k ≠ 0` forces `a = b`.
- Two curves have disjoint representatives iff `i(a, b) = 0`.

**Proof.**
1. **Curves.** Since `g ≥ 2`, choose meridians `a` and `b` of two different
   handles, which are disjoint and non-isotopic. Choose a curve `c` meeting each
   of them once.
2. **Irredundant.** Suppose two distinct twists `T_x, T_y` in
   `{T_a, T_b, T_c}` generated a cyclic group `⟨h⟩`. Then `T_x = h^p` and
   `T_y = h^q` with `p, q ≠ 0`, so `T_x^q = T_y^p` and `x = y` by (F).
3. **Coincidence correspondence.** The annuli about `a` and `b` can be realized
   disjointly. Those about `c` and `a`, or `c` and `b`, cannot, since
   `i(c, a) = i(c, b) = 1`. So `Γ` is one edge `{T_a, T_b}` plus the isolated
   vertex `T_c`, and `A(Γ) = ⟨x, y, z | [x, y]⟩ ≅ Z² ∗ Z`.
4. **Powers in `L`.** Let `m = [Mod(Σ) : L]!`. For every `f ∈ Mod(Σ)`, two of
   the cosets `L, fL, …, f^{[Mod(Σ):L]}L` coincide, so `f^k ∈ L` for some
   `1 ≤ k ≤ [Mod(Σ) : L]`, and `f^m ∈ L`.
5. **Theorem 1.1.** It applies with `p = 0` and `χ = 2 − 2g < 0`. Take `n = mN`.
   The twists `T_a^n, T_b^n, T_c^n` lie in `L` and generate a copy of
   `Z² ∗ Z`.
6. **Conclusion.** An injective homomorphism `L → V` would embed `Z² ∗ Z` in
   `V`, contradicting the survey's Theorem 4.6(1). So every homomorphism `L → V`
   has nontrivial kernel. `∎`
