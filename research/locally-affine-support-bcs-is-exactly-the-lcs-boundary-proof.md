---
rg: 2
id: locally-affine-support-bcs-is-exactly-the-lcs-boundary-proof
kind: route
title: Prove that locally affine support is the LCS boundary
target: locally-affine-support-bcs-is-exactly-the-lcs-boundary
requires: []
---

Assume item 1.  For every context `c`, set

```text
A_c=affineHull(supp(tau_c)).                            (LAP1)
```

Over `F_2`, a finite affine set is the common zero set of finitely many
affine linear forms.  Use those forms as the parity constraints of a binary
LCS `L`.  The spectral measure of `tau` on context `c` is supported on
`A_c`, so every new parity constraint holds in the GNS representation and
`tau` is a perfect tracial state of `L`.

If `L` had a Connes-embeddable perfect state, its context spectral measures
would be supported on `A_c`.  By `(LAS1)`, `A_c subseteq Allowed_c`; hence the same
state would be perfect for the original BCS.  This contradicts item 1, so
item 2 holds.

Conversely assume item 2 and regard the LCS as a BCS.  Its allowed set in
each context is affine.  The support of a perfect state is contained in that
allowed set, and an affine set contains the affine hull of each of its
subsets.  Thus `(LAS1)` holds and item 1 follows.

For the character description, Pontryagin duality for the finite elementary
abelian context group gives

```text
ann(intersection_(chi in S_c) ker chi)=span(S_c).      (LAP2)
```

Intersecting the character subgroup on the right with the affine central
sign slice `chi(J)=-1` gives exactly the affine hull of `S_c`, proving
`(LAS3)`.  Killing a basis of `K_c` imposes the dual parity equations whose
solution set is `(LAS3)`.  This identifies the kernel quotient with the
ordinary solution-group presentation of the extracted LCS.

The equivalence of items 2 and 3 is the established solution-group theorem,
completing the proof.
