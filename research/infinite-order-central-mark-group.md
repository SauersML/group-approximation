---
rg: 2
id: infinite-order-central-mark-group
kind: claim
title: A torsion-free Kazhdan compression group with an infinite-order central mark
distinct_from:
  kazhdan-clifford-non-mf-construction: that construction marks the Clifford sign, an involution, and its groups therefore have torsion; this one asks for the same architecture with an infinite-order central mark and a torsion-free ambient group.
  scaling-family-non-mf: that is the concrete affine family of the Clifford construction, again with a central involution.
  torsion-free-countable-non-mf: that claim asks for a torsion-free non-MF group with no presentation constraint; this one asks only for the group-theoretic input data of the mechanism and asserts nothing about MF.
  torsion-free-finitely-presented-non-mf: that root asserts non-MF-ness; this claim is one of its two prerequisites and carries no analytic content.
  torsion-free-higman-embedding: that claim is about embedding recursively presented torsion-free groups into finitely presented ones; this one builds a specific finitely presented group with transport data.
---

There is a **torsion-free** finitely presented group `H` carrying the full
transport data — a property-(T) subgroup `iota(Gamma)`, an element `t` with
`t iota(Gamma) t^-1 <= iota(Gamma)` proper, an element `c` centralizing
`iota(Gamma)` — such that the normal closure of the compression defect
`u = [t c t^-1, iota(a)]` contains a **nontrivial central element of
infinite order**.

Together with `commutant-projection-extraction` this yields the root; the
two claims split that branch cleanly into its group-theoretic and its
operator-algebraic halves.

This claim is now established by
`infinite-order-central-mark-group-proof`.  The construction does not need
an equivariant Heisenberg lamp kernel.  Starting from the bare torsion-free
Britton compression source, it adjoins a central integer `z` and an HNN
stable letter `s` with

```text
s u s^-1 = u z,       s z s^-1 = z.
```

The associated subgroup `<u,z>` is `Z^2`, the displayed map is a
unimodular shear, and Britton embedding proves that `z` survives with
infinite order.  The HNN torsion theorem preserves torsion-freeness, while
`z=(s u s^-1)u^-1` puts the mark in the normal closure of the defect.

This is the **secondary** branch.  The root's primary route,
`torsion-free-non-mf-from-normal-kazhdan-defect`, needs no mark at all: it
puts a normal Kazhdan subgroup in the defect and cuts the corner with its
Kazhdan projection.  What keeps this claim alive is that it needs no
small-cancellation machinery — the construction here is an explicit
presentation of the same shape as the existing Clifford witness.

## Superseded direct-lamp idea and its exact obstruction

**Heisenberg lamps instead of Clifford lamps.**  In the existing witness
the lamps are order-two Clifford generators at the sites of a coset space,
two distinct lamps anticommute, and the mark is the resulting central sign
`(e_o e_{o'})^2 = -1`.  Replace the Clifford lamp group by a Heisenberg
lamp group over `Z`: lamp generators `x_o` of infinite order at the sites,
with `[x_o, x_{o'}] = z` central of infinite order for distinct sites.
`HeisenbergCentre.lean` already computes that the centre of the Heisenberg
group over a ring is the coefficient ring on the nose, so the centre is a
copy of `Z` rather than of `Z/2`.  This design also supplies the pairing
that `exel-loring-mark-quantization` needs: the mark is a commutator of two
lamp generators, hence the value of the central extension class on the `H_2`
class carried by that one commutator relation.  The mark is then not a square but a
commutator: `u = [t c t^-1, iota(a)]` is again a product of lamps at two
distinct sites, and `z = [u, x_{o'}]` lies in the normal closure of `u`.
Clause 1 of `corona-corner-detection-criterion` is stated for the whole
normal closure precisely so that this variant is covered.

**Torsion-freeness of the pieces.**  A semidirect product of torsion-free
groups is torsion-free, and torsion elements of an ascending HNN extension
are conjugate into the base, so the mapping-telescope architecture
preserves torsion-freeness.  What must change is the base: the literal
affine base contains `SL_3(Z)`, which has torsion.  A torsion-free
congruence subgroup (Selberg) of the affine Kazhdan base still carries the
scaling compressor `v -> N v` on the translation part, which is a proper
injective self-embedding, and property (T) passes to finite-index
subgroups.  So the base can be made torsion-free without losing the
compression architecture.

At scale two the direct replacement is impossible, not merely unfinished.
For `r=t^-1 a t`, the identity `alpha(a)=a^2` gives `r^2=a in Gamma`, so
`r` swaps the two marked cosets.  Any invariant alternating integral
commutator form must vanish on that pair.  This is recorded as
`doubling-coset-heisenberg-orientation-forces-zero-mark`.  The HNN shear
avoids the orientation obstruction and supplies the mark unconditionally.
