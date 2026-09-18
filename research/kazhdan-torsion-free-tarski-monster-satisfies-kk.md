---
rg: 2
id: kazhdan-torsion-free-tarski-monster-satisfies-kk
kind: claim
title: Every torsion-free non-elementary hyperbolic group has a torsion-free Tarski monster quotient whose reduced C*-algebra has only trivial projections; over Sp(n,1) lattices these monsters are Kazhdan, non-hyperbolic and non-linear
distinct_from:
  kk-witness-counterexample-locus-is-marked-closed: that is the general topological theorem (closed witness loci, fast limits inherit KK); this applies it to the Olshanskii--Osin--Sapir torsion-free Tarski monster construction and gets a new class of groups satisfying the root.
  osajda-monster-hosts-for-bc-module-route: that imports Gromov/Osajda monsters as hosts for a Baum--Connes module route; this proves Kadison--Kaplansky for torsion-free graded small cancellation Tarski monsters without any Baum--Connes statement for the limit group.
  fpbs-torsion-free-tarski-monster-no-amenable-wq-normal: that concerns weakly quasi-normal amenable subgroups of torsion-free Tarski monsters; this concerns projections in their reduced C*-algebras.
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that establishes the root for real-rank-one lattices themselves; this establishes it for Tarski monster quotients of such lattices, which are not lattices, not hyperbolic and not linear.
---

**ESTABLISHED** by `kazhdan-torsion-free-tarski-monster-satisfies-kk-proof`, modulo a verbatim
import of the construction in Olshanskii--Osin--Sapir, *Lacunary hyperbolic groups*, Geom. Topol. 13
(2009), arXiv:math/0701365, the theorem labelled `ExoticQuotients`, part 2, in subsection "Groups
without free subgroups" of the arXiv source (quoted in the proof), and of Olshanskii, *On residualing homomorphisms and
G-subgroups of hyperbolic groups*, IJAC 3 (1993), Corollary 1 and Lemmas 4.2, 6.7, as recorded there.

**Theorem.** Let `G` be a torsion-free non-cyclic hyperbolic group with a finite generating set
`S`. Then `G` has a quotient `Q` with the following properties.
1. `Q` is infinite, non-abelian and torsion-free, and every proper subgroup of `Q` is cyclic
   (a torsion-free Tarski monster).
2. `Q` is the direct limit of torsion-free hyperbolic groups `G = G(0) -> G(1) -> ...`, each
   obtained from the previous one by one small cancellation relator, and it has a graded small
   cancellation presentation; in particular it is lacunary hyperbolic.
3. **`C*_r(Q)` has no projection other than `0` and `1`.** Hence `k[Q]` has no idempotent other
   than `0, 1` for every field `k` of characteristic `0`.

**Corollary (the new class).** Let `G` be a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2`
(exists by Selberg's lemma; hyperbolic and Kazhdan). The quotient `Q` of the Theorem is an
infinite, finitely generated, torsion-free group satisfying the root, and:
- `Q` has Kazhdan's property (T) (quotient of a Kazhdan group), so it is not a-T-menable;
- `Q` contains no `F_2`: it would be a proper non-cyclic subgroup. Being infinite and Kazhdan, `Q`
  is not amenable, hence not virtually solvable;
- `Q` is not hyperbolic (hyperbolic groups are virtually cyclic or contain `F_2`), and not linear
  (Tits alternative);
- `Q` is not a lattice in a Lie group and has no proper action on a CAT(0) cube complex
  (property (T)), so none of the assembly-surjectivity theorems listed in the root applies.

To our knowledge (arXiv searches 2026-09-17), no theorem on the Baum--Connes conjecture or the
Kadison--Kaplansky conjecture for these groups exists. The only attempt found, M. Finn-Sell,
*Controlled analytic properties and the quantitative Baum--Connes conjecture*,
arXiv:1908.02131, claimed quantitative Baum--Connes for a class of lacunary hyperbolic groups
including such monsters, and was withdrawn on 2026-05-12 ("an argument missing for norm control
in the K-theory component").

**Mechanism.** The Kadison--Kaplansky locus of marked groups is a `G_δ`, and for each spectral
witness `ω` a group with only trivial projections keeps every marked group on a ball of radius
`r(N, ω)` out of the witness set (`kk-witness-counterexample-locus-is-marked-closed`, items A.4
and A.6). In the Olshanskii--Osin--Sapir construction the relator length `ρ_i` is chosen last and
arbitrarily large, and the small cancellation estimates bound the injectivity radius of
`G(i-1) -> G(i)` below by `λ_i(1 - 23μ_i)ρ_i - 2c_i - 4ε_i`. So one more "sufficiently large"
condition makes the limit inherit trivial projections from the torsion-free hyperbolic stages.

**Not claimed.** Baum--Connes for `Q`. The matrix form `τ_*(K_0(C*_r(Q))) ⊆ Z` is *not*
claimed either. The proof's closing remark shows that the same interleaving gives it as soon as
the stages satisfy the torsion-free trace conjecture, which for hyperbolic groups follows from
assembly surjectivity and the `L²`-index theorem (Lück, Invent. Math. 149 (2002)). That source was
not re-read here, so the matrix form is recorded as a remark, not as ESTABLISHED.
