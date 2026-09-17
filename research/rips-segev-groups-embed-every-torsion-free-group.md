---
rg: 2
id: rips-segev-groups-embed-every-torsion-free-group
kind: claim
title: Every finitely generated torsion-free group sits in a generalized Rips--Segev group, so a factor-uniform support reduction is as hard as Kaplansky
distinct_from:
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for the Rips--Segev groups; this shows that over arbitrary torsion-free factors the question is equivalent to the full conjecture, and isolates the core groups over <a>*<b> as the only non-universal part.
  rips-segev-witness-supports-carry-no-zero-divisors: that kills zero-divisor pairs inside the witness (A, B); this proves that no argument uniform in the factors can push arbitrary supports into the witness without proving Kaplansky's conjecture outright.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that gives one finitely presented torsion-free tester group U; this embeds U into a finitely presented generalized Rips--Segev group, so the tester can be taken without unique products and of Rips--Segev form.
  rips-segev-groups-are-cocompactly-cubulated: that asks for cubulations of the original groups and records the Kazhdan examples; this is a group-ring statement about the whole generalized class and does not concern cube complexes.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-groups-embed-every-torsion-free-group-proof`.

**Setting.**  Steenbock, arXiv:1307.0981 (TeX read 2026-09-17), section "Generalized Rips-Segev graphs".
- `F = G_1 * G_2` with `G_1, G_2` finitely generated torsion-free, `1 != a in G_1`, `1 != b in G_2`.
- `Gamma` is a finite generalized Rips--Segev graph labelled by `a^{+-1}, b^{+-1}`.  Its coefficients come from
  Steenbock's table `(10^{5i-4}, ..., 10^{5i})`, and its underlying graph `Phi` has girth at least 41.
- `G(Gamma) = F / <<R>>`, where `R` is the set of cycle labels of `Gamma`.
- The **core group** is `K_Gamma = (<a> * <b>) / <<R>>`, with the same `Gamma` over the free group `F_2 = <a> * <b>`.
  The original Rips--Segev groups are core groups.

**Theorem (universality).**  Let `H` be a finitely generated torsion-free group, `1 != a in H`, and `G_2 = <b> = Z`.
1. `G(Gamma)` over `H * Z` is isomorphic to the amalgam `H *_{<a>} K_Gamma`.  In general,
   `G(Gamma) = G_1 *_{<a>} K_Gamma *_{<b>} G_2`.
2. `H` embeds in `G(Gamma)`.  `G(Gamma)` is torsion-free and without unique products; the witness `(A, B)` lies in
   `K_Gamma`.
3. If `H` is hyperbolic, then `G(Gamma)` is hyperbolic.  If `H` is finitely presented, then `G(Gamma)` is finitely
   presented.

**Consequences.**  Fix a field `k`.
- **(E1) Equivalence.**  `k[G]` is a domain for every torsion-free `G` if and only if `k[G(Gamma)]` is a domain for
  every generalized Rips--Segev group in the setting above, even with `G_2 = Z` only.
- **(E1') One tester.**  Let `U` be the finitely presented tester of
  `kaplansky-three-properties-fixed-fp-torsion-free-tester`, and let `G_U = U *_{<a>} K_Gamma` for one fixed finite
  `Gamma`.  Then `G_U` is a single finitely presented, torsion-free, generalized Rips--Segev group without unique
  products, and `k[G_U]` is a domain if and only if Kaplansky's zero-divisor conjecture holds over `k`.
- **(E2) Hyperbolic case.**  The conjecture over `k` for torsion-free hyperbolic groups is equivalent to the
  conjecture over `k` for hyperbolic generalized Rips--Segev groups.
- **(E3) Obstruction to the support reduction.**  Let `SR(k)` be the statement "for every generalized Rips--Segev
  group as above, if `k[G(Gamma)]` has a zero-divisor pair, then it has one with `supp alpha` in `A` and `supp beta`
  in `B`".
  - `SR(k)` is equivalent to Kaplansky's zero-divisor conjecture over `k`.
  - One direction uses `rips-segev-witness-supports-carry-no-zero-divisors`, whose hypotheses hold for Steenbock's
    table over any factors, together with (E1).  In the other direction, `SR(k)` holds vacuously once the
    conjecture holds.
  - **Exact failing step.**  The reduction fails on pairs supported in one coset pair `(gH, Hh)`.
    - There, `alpha beta = 0` in `k[G(Gamma)]` exactly when `(g^{-1} alpha)(beta h^{-1}) = 0` in `k[H]`.
    - Every product coincidence `s t = s' t'` between such supports is a relation of `H` itself.  Its minimal van
      Kampen diagram over `R` has no faces, because `H` embeds.
    - So no small-cancellation diagram detects these coincidences.  An argument that pushes such supports into the
      witness would, applied with `H` any torsion-free group, prove the conjecture.
- **(E4) Units.**  With `H` the Promislow group, `G(Gamma)` has non-trivial units over `F_2` (Gardam).  So a
  factor-uniform proof of the unit conjecture for generalized Rips--Segev groups does not exist.

**What remains.**  The only non-universal part of the class is the family of core groups `K_Gamma` over `F_2`,
including Steenbock's original question.  The theorem gives these directions:
- The conjecture for all generalized groups with factors `G_1, G_2` whose group rings are domains follows from two
  statements: (R1) the conjecture for the core groups `K_Gamma`; and (R2) a domain-combination theorem for
  amalgamated products over infinite cyclic subgroups, applied to `G_1 *_{<a>} K_Gamma *_{<b>} G_2`.
- Conversely, the domain-factor statement implies (R1), since `Z * Z` qualifies.
- The status of (R2) in this generality is not assessed here.
