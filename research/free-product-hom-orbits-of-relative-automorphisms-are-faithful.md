---
rg: 2
id: free-product-hom-orbits-of-relative-automorphisms-are-faithful
kind: claim
title: The relative automorphism group of S * F_n acts faithfully on the orbit of (t, 1, ..., 1) in the homomorphisms to S * <t>, for every nontrivial group S
distinct_from:
  relative-automorphism-action-is-highly-transitive: that is the BFFHZ action on Hom_S(S * F_n, S), whose kernel is the mixed-identity kernel K and which is highly transitive; this is an action on homomorphisms into the free product S * <t>, which is faithful for every S but has infinitely many orbits on pairs.
  precomposition-type-a-target-is-finitely-presented: that proves the stabilizer and pair clauses for precomposition on any target (finitely presented target, finitely many normal subgroups); this proves that the remaining clause, faithfulness, can always be met, and shows which target meets it.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4; this shows the mixed-identity kernel is never the obstruction to it along relative-automorphism routes, only the double-coset clause is.
requires:
  - free-product-hom-orbit-faithfulness-proof
---

**ESTABLISHED** through `free-product-hom-orbit-faithfulness-proof`. Elementary lane
proof by bh-invent-10, not independently reviewed. No priority claimed; the input is
Hull–Osin's theorem that acylindrically hyperbolic groups with trivial finite radical
are mixed-identity-free (MIF).

## Statement

Let `S ≠ 1` be any group and `n ≥ 2`. Put `G = S * F(x_1, ..., x_n)`,
`A = Aut_S(G)` (automorphisms fixing `S` pointwise), and `Q = S * ⟨t⟩`. Let `A` act
on `Hom_S(G, Q)` by precomposition, and let `O` be the orbit of
`φ_0 = (x_1 ↦ t, x_2 ↦ 1, ..., x_n ↦ 1)`.

1. **Faithful.** `A` acts faithfully on `O`, and transitively by definition.
2. **Kernel removal for Theorem C actors.** Let `S` be finitely presented simple and
   `K = ker(A ↷ S^n)` the mixed-identity kernel of the BFFHZ action on
   `Hom_S(G, S) ≅ S^n`. Then `A ↷ S^n ⊔ O` is faithful. So, in the criterion of
   Attempt 11 on `fp-simple-groups-embed-in-fp-simple-mif-groups`, the subgroup
   `H = Stab_A(φ_0)` has `core_A(H) = 1`, in particular `core_A(H) ∩ K = 1`.
3. **What fails: exactly the double-coset clause.** The points
   `ψ_j = (t, t^j, 1, ..., 1)`, `j ≥ 1`, lie in `O`. The unordered pairs `{φ_0, ψ_j}`
   lie in pairwise distinct `A`-orbits, since their image in `Q × Q` meets `1 × Q` in
   `1 × ⟨⟨t^j⟩⟩`, and these normal closures are pairwise distinct. So `H\A/H` is
   infinite. This is the pair clause of `precomposition-type-a-target-is-finitely-presented`,
   met here in its strongest form.

The same proof gives faithfulness on the orbit of `(y_1, ..., y_k, 1, ..., 1)` in
`Hom_S(G, S * F(y_1, ..., y_k))` for every `1 ≤ k < n`.

## Consequence: where Question 3.4 lives on relative-automorphism routes

A precomposition route for BFFHZ Question 3.4 needs an image group `Q ⊇ S` of an orbit
with three properties at once:
- **(a) finite presentation**, from finitely generated stabilizers (item 1 of
  `precomposition-type-a-target-is-finitely-presented`);
- **(b) finitely many normal subgroups**, from finitely many pair orbits (item 2 there);
- **(c) no word with constants in `S` vanishing on the orbit**, from faithfulness.

This node shows that (a) and (c) together are free: `Q = S * ⟨t⟩` is finitely presented
whenever `S` is, and its orbit is faithful. But free products fail (b) as badly as
possible. So the mixed identities of `S`, the finite-basis conditions of
`bffhz-q32-forces-finitely-based-mixed-identities` and the recursiveness of `J_1(S)` are
features of the one target `Q = S`. They are not obstructions to Question 3.4. What
Question 3.4 needs is an image with (b) and (c) together, i.e. a finitely presented
overgroup of `S` with finitely many normal subgroups in which `S`'s identities die.
That is an almost simple overgroup, which is essentially the question itself.

## Lesson for general BH

Faithfulness is never the hard clause of type (A). Adjoin one free-product orbit and any
kernel disappears; the fp actor `Aut_S(S * F_n)` is unchanged. The hard clause is
oligomorphy, and along every precomposition route it is equivalent to the existence of a
finitely presented image with finitely many normal subgroups. An input cannot supply that
from its own points. It has to be imported from a combinatorial scaffold that already has
it: the clopen Boolean algebra of a finitely presented full Cantor group (Attempt 9, the
master route's gates P1 and P2), or an actor already of type (A). So BH ⇔ PBH is not a
question about mixed identities of finitely presented simple groups. It is the master
route's existence question G1 ∧ G2 for `Λ = S × H`.

## Not claimed

- That `Stab_A(φ_0)` is finitely generated. Peak reduction for the free product
  `(S * ⟨x_1⟩) * ⟨x_2, ..., x_n⟩` should give it, but this is not proved here.
- Any positive answer to Question 3.4 for a new group.
