---
rg: 2
id: kac-moody-lattice-confined-subgroups-are-lim-free-and-mif
kind: claim
title: Every confined subgroup of a finitely presented simple non-affine Kac--Moody group over a finite field is lim-free and MIF
distinct_from:
  fp-simple-kac-moody-lattices-are-highly-transitive: that asks whether these groups are highly transitive; this shows that each of their confined subgroups passes every obstruction known to Le Boudec--Matte Bon, so their Corollary 1.4 cannot refute high transitivity with those obstructions.
  fp-simple-kac-moody-lattices-are-mif: that says the whole group is MIF; this says the same of every confined subgroup, and adds that subgroups with a bounded orbit in Rybak's hyperbolic space are not confined.
---

**ESTABLISHED** through `kac-moody-confined-subgroups-lim-free-proof`. Not
independently reviewed, and no novelty is claimed.

**Statement.** Let `G = G(F) = Γ(F)/Z(Γ(F))` be an infinite finitely presented simple
non-affine Kac--Moody group over a finite field [CR09]. Let it act on the hyperbolic
space `S = E(X_D)` of `fp-simple-kac-moody-lattices-are-lim-free`. Let `H ≤ G` be a
confined subgroup. Then:

1. `H` acts on `S` with general type and `Λ_S(H) = Λ_S(G)`. Its action on the limit set is
   topologically free and minimal, so `H` is lim-free.
2. `H` is MIF.
3. `H` satisfies no identity, is not partially finitary, and every nontrivial normal
   subgroup of `H` has trivial centralizer in `H`.
4. Every finite group is a subquotient of `H`.
5. No subgroup of `G` with a bounded orbit on `S` is confined. This covers the
   stabilizer in `G` of any point of `X_D`. If the curtain model has the same points
   as `X` (Petyt--Spriano--Zalloum, not re-read), it covers the stabilizers of
   chambers and of spherical residues of that building. It also covers any subgroup
   with `Λ_S(K) ≠ Λ_S(G)` or fixing a point of `Λ_S(G)`.

**What this does to BFFHZ Question 3.6, part one.**
- **The inheritance.** Le Boudec--Matte Bon, *Confined subgroups and high transitivity*,
  Ann. H. Lebesgue 5 (2022), Theorem 1.1 (p. 493, read from the PDF): if `G` has a
  faithful highly transitive action on `Ω` and is not partially finitary, then every
  confined `H` has finitely many finite orbits and acts highly transitively on the
  rest. Corollary 1.4: if some confined subgroup has no faithful highly transitive
  action, neither does `G`.
- **The obstructions they list** (§2.4, p. 498) for a group with a faithful highly
  transitive action that is not partially finitary: MIF [HO16, Theorem 5.9], trivial
  centralizers of nontrivial normal subgroups, every finite group as a subquotient,
  no identity.
- **The consequence.** By items 2--4 every confined subgroup of `G` satisfies all of
  these, so Corollary 1.4 combined with the obstructions of §2.4 cannot show that `G`
  is not highly transitive. A negative answer along this route needs a new
  obstruction to high transitivity that holds for some lim-free, MIF group.
- **Why Burger--Mozes-type obstructions miss here.** The natural candidates, such as
  chamber stabilizers, parabolics and boundary-point stabilizers, are not confined at
  all, by item 5. Stabilizers of this kind are confined only for topologically
  nowhere free actions (LBMB Lemma 2.1), which is the micro-supported situation of
  their Theorem 1.5.
