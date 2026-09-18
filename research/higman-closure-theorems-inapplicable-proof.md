---
rg: 2
id: higman-closure-theorems-inapplicable-proof
kind: route
title: Proof of the retraction lemma and of its consequences for the Higman splittings and the permutational closure theorems
target: retracts-inherit-proper-power-conjugacy
requires:
  - higman-group-splits-as-amalgams-over-free-subgroups
  - higman-group-is-the-swap-twisted-double-of-a-bs-amalgam
  - homogeneous-conjugation-invariants-vanish-on-bs-bases
---

**Step 1 (the lemma).** Let `rho : G -> C` be a retraction and let
`g c g^-1 = c^n` with `c in C`. Applying `rho`, which is a homomorphism fixing
`C` pointwise, gives `rho(g) c rho(g)^-1 = rho(c^n) = c^n`, and
`rho(g) in C`. []

**Step 2 (free groups admit no proper-power conjugacy).** In a free group,
conjugation preserves the length of the cyclically reduced form of an element.
For `c != 1` the cyclically reduced forms of `c` and `c^n` have lengths `L` and
`|n| L` with `L >= 1`, so `c` and `c^n` are not conjugate when `|n| >= 2`. By
Step 1, a free `C` is not a retract of a `G` in which some nontrivial element
of `C` is conjugate to a proper power. The same conclusion holds whenever `C`
has no infinite-order element conjugate in `C` to a proper power, for instance
by item 3 of `homogeneous-conjugation-invariants-vanish-on-bs-bases`. []

**Step 3 (the two Higman splittings).** `higman-group-splits-as-amalgams-over-free-subgroups`
gives `H4 = G_1 *_(F_ac) G_2` with `G_1 = <a, b, c>` presented by
`b^a = b^2`, `c^b = c^2`, with `G_2 = <c, d, a>` presented by `d^c = d^2`,
`a^d = a^2`, and with `F_ac = <a, c>` free of rank two in both. In `G_1` we
have `b^-1 c b = c^2` with `c in F_ac`, and in `G_2` we have `d^-1 a d = a^2`
with `a in F_ac`. Both `a` and `c` have infinite order, since they generate a
free subgroup. Steps 1 and 2 now show that `F_ac` is a retract of neither
vertex group. Applying the automorphism `a -> b -> c -> d -> a` of `H4` carries
the first splitting to `H4 = G_3 *_(F_bd) G_4` and gives the same conclusion
there. []

**Step 4 (the twisted double).** For
`E = G_1 *_F (F x|_theta Z/2)` of
`higman-group-is-the-swap-twisted-double-of-a-bs-amalgam`, with
`F = <a, c>` and `theta` the swap `a <-> c`: the `G_1` side is Step 3. On the
other side, a retraction `F x|_theta Z/2 -> F` fixing `F` pointwise sends the
involution `t` to some `w in F`, and then `w^-1 f w = theta(f)` for all
`f in F`, so `theta` is conjugation by `w`. But `theta` exchanges the basis
elements `a` and `c`, hence acts nontrivially on `F^ab = Z^2`, while
conjugation acts trivially on the abelianization. So no such retraction
exists. []

**Step 5 (perfect, hence not an HNN extension).** In `H4^ab`, written
additively, each relation `g_i g_(i+1) g_i^-1 = g_(i+1)^2` becomes
`g_(i+1) = 2 g_(i+1)`, so `g_(i+1) = 0`; as `i` runs over `Z/4` all four
generators vanish and `H4^ab = 0`. For an HNN extension
`G = <A, t | t c t^-1 = phi(c) (c in C)>` the assignment `t -> 1`, `A -> 0`
respects every defining relation, so `G` surjects onto `Z`. A perfect group is
therefore not an HNN extension. []

**Step 6 (the closure theorems).** `pbh-class-closed-under-common-retract-amalgams`
assumes the edge group is a retract of both vertex groups; Steps 3 and 4 refute
that assumption for every decomposition of `H4` recorded on main.
`pbh-class-closed-under-graph-products` part 1 is the case `Y = C x K` of the
same theorem, so its hypothesis fails as well. Clause (T) of
`pbh-class-closed-under-relative-holomorphs` outputs ascending HNN extensions
`J *_beta`, and Step 5 shows `H4` is not of that form. Finally, the
Baumslag--Gersten chain splitting has vertex group `BS(1,2) = <a, t>` and edge
group `<a>`, and `a ~ a^2` inside that vertex group, so Step 1 applies there
too. []
