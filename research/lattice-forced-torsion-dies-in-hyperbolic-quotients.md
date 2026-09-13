---
rg: 2
id: lattice-forced-torsion-dies-in-hyperbolic-quotients
kind: claim
title: Torsion forced invisible by a quotientless subgroup survives a hyperbolic quotient only in a non-residually-finite one, and never through a simple lattice with flats
invalidates: [non-vtf-hyperbolic-via-lattice-forced-torsion-quotient]
distinct_from:
  hull-quotients-are-not-word-hyperbolic: that shows Hull's small-cancellation quotients are acylindrically but not word-hyperbolic; this concerns every homomorphism to a word-hyperbolic group and what happens to torsion forced through a quotientless subgroup
  hyperbolic-compression-centralizer-rigidity: that kills the compression witness inside a hyperbolic ambient group; this kills the amalgam forcing mechanism (a torsion element in the normal closure of a quotientless subgroup) under passage to hyperbolic quotients
---

Let `G` be a group and `N <= G` a subgroup with no nontrivial finite quotient. Let
`s in G` lie in the normal closure `<<N>>`. Then `s in R_f(G)`, since every finite
quotient kills `N`. Let `π : G -> Q` be a homomorphism to a word-hyperbolic group.

1. **Survival presupposes a counterexample.** If `π(s) != 1`, then `π(N)` is a
   nontrivial subgroup of `Q` with no nontrivial finite quotient. So `Q` is not
   residually finite: subgroups of residually finite groups are residually finite,
   and a nontrivial residually finite group has a nontrivial finite quotient.
2. **Simple lattices with flats never survive.** If `N` is simple and contains `Z^2`,
   then `π(N) = 1` and `π(s) = 1`. This covers the torsion-free simple lattices in
   products of two trees (Burger–Mozes) and simple Kac–Moody lattices.
3. **The general mechanism is exactly as hard as the root.** Some hyperbolic group has
   a nontrivial subgroup without finite quotients iff
   `non-residually-finite-hyperbolic-group` holds. For (<=) take the quotientless group
   of `kapovich-wise-rf-iff-finite-quotients` itself; (=>) is item 1.

**Consequence for the brief's first start.** Take a CAT(0) group in which prime-order
torsion is forced invisible through a simple lattice in a product of trees, for
example `Γ *_{h=t} (Z/p x| Z)` of
`research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md` §5. No
hyperbolic quotient of it keeps that torsion, whatever the method: small
cancellation, Dehn filling or random relators. If the forcing subgroup is replaced by
a quotientless subgroup that could survive, the hyperbolic quotient is already a
counterexample.

**Calibration.**
- The hypothesis holds for a real object: in the amalgam above, `Γ` is simple and
  contains `Z^2`, and `s in <<Γ>>`, because `t` dies, and then `s = s^2`.
- A trivial model fails item 1: for `N = 1`, `<<N>> = 1` and nothing is forced.

Proof: `lattice-forced-torsion-dies-in-hyperbolic-quotients-proof`. Elementary;
no novelty claimed. Unreviewed.
