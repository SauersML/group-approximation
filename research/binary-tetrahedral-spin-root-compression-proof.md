---
rg: 2
id: binary-tetrahedral-spin-root-compression-proof
kind: route
title: Every negative-center SL2(3) type has at most half its mass fixed by the order-three complement
target: binary-tetrahedral-conditional-e5-root-bridge
requires: []
---

The group `Q8` has one irreducible representation on which its central
involution is negative: the two-dimensional spin representation.  The
order-three automorphism permuting the three quaternion axes preserves this
type, so it has exactly three extensions to
`T=Q8 semidirect C3`, obtained by tensoring one extension with the three
characters of `T/Q8 congruent C3`.  Consequently every irreducible
`T`-representation with `ell=-1` has dimension two.

On any such extension, `y` cannot act as the identity: otherwise its
conjugation action on the represented copy of `Q8` would be trivial, whereas
it cyclically permutes the three non-scalar quaternion axes.  Since `y` has
order three, it is diagonalizable and its `1`-eigenspace therefore has
dimension at most one.  Thus on every negative-center irreducible type

```text
rank P_(y,1) <= (1/2) dim.                              (BTP1)
```

Now let `Q` and `E=Qe_chi` be as in `(BTB3)`.  The direct-product factor
`H times T` makes `e_chi` commute with `T`, and `Q` reduces `T`; hence `E`
belongs to the commutant of the represented `T`.  Decompose the negative
central sector into its three spin types with arbitrary multiplicity.
On every isotypic summand `E` is a multiplicity-space projection tensored
with the identity of the two-dimensional spin space.  Applying `(BTP1)` on
each summand and adding traces gives

```text
tr(E P_(y,1)) <= (1/2)tr(E),
```

which is `(BTB4)` because `y=Z` in the amalgam.

The injections used in `(BTB2)` are immediate from `(BTB1)`: the odd-order
subgroup `<Z>` intersects the two-group `H times <ell>` trivially, so the
left associated subgroup is the displayed direct product; the right one is
the direct product of `H` with `<y,ell>`.  Bass--Serre normal form proves
that both vertex groups embed.  The perfect extension is the universal
property of the amalgam applied to the two compatible homomorphisms stated
in the claim.

For approximate representations, exactify the fixed finite group
`H times T`, replace the prescribed carrier by its finite-group conditional
expectation followed by spectral rounding, and use the literal relator
`y=Z`.  All menus are fixed, so finite Fourier expansion and word
telescoping change the exact inequality by `O(sqrt(E_pres))` independently
of matrix dimension.
