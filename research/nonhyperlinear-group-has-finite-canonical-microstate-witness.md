---
rg: 2
id: nonhyperlinear-group-has-finite-canonical-microstate-witness
kind: claim
title: Every nonhyperlinear countable group has a finite amplification-invariant canonical microstate obstruction
distinct_from:
  canonical-profile-collapse-compactness: that gives finite windows forcing collapse of a specified rational mark for a finitely generated presentation; this gives the local microstate characterization of nonhyperlinearity for an arbitrary countable group, with no marked word.
  hyperlinear-radical-is-finitely-witnessed: that assumes a word dies in every matrix-ultraproduct representation and extracts a finite presentation prefix; this excludes the canonical delta character itself on one finite multiplication window.
---

**ESTABLISHED.**  Let `Gamma` be a countable group.  If `Gamma` is not
hyperlinear, then there are a finite symmetric set `F subset Gamma` with
`1 in F` and `epsilon>0` such that no map

```text
phi:F -> U(d)                                             (NFW1)
```

in any finite dimension simultaneously satisfies

```text
||phi(g)phi(h)-phi(gh)||_2<epsilon
       whenever g,h,gh in F,
|tr(phi(g))|<epsilon                    for g in F\{1},
||phi(1)-1||_2<epsilon.                                  (NFW2)
```

One may equivalently use pairwise separation conditions after enlarging
`F` to contain the relevant quotients.

Indeed, if no such finite obstruction existed, exhaust `Gamma` by finite
symmetric windows and choose a `1/n`-microstate on the `n`th window.  Their
tracial matrix ultraproduct is a homomorphism with canonical character.
For `g!=h`, the trace of the image of `g^(-1)h` is zero, so the homomorphism
is injective.  This is a hyperlinear embedding, a contradiction.  The
converse is immediate by restricting canonical microstates.

The obstruction is exactly invariant under common amplification.  For
`Phi(g)=phi(g) tensor I_m`, normalized trace and normalized Hilbert--Schmidt
norm give

```text
tr_(dm)(Phi(g))=tr_d(phi(g)),
||Phi(g)Phi(h)-Phi(gh)||_(2,dm)
 =||phi(g)phi(h)-phi(gh)||_(2,d).                        (NFW3)
```

Thus padding cannot evade the finite witness.  This does not make the
witness effective and does not construct the group: it is the compactness
form of nonhyperlinearity after the canonical trace obstruction is already
known.
