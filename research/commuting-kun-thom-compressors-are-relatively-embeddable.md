---
rg: 2
id: commuting-kun-thom-compressors-are-relatively-embeddable
kind: claim
title: Every finite commuting Kun--Thom compressor slice is relatively embeddable
distinct_from:
  one-kun-thom-compressor-is-relatively-embeddable: that treats one ascending-HNN direction; this allows any finite free-abelian family of commuting positive monomial compressors
  kun-thom-single-compressor-sofic-joint-nonsofic: that contrasts individual directions with the full action; this proves that even simultaneous commuting directions remain on the positive side
  sofic-coset-action-makes-amalgam-double-sofic: that is the general conditional double theorem; this proves its sofic-action hypothesis for a concrete multidirectional Kun--Thom slice
  coordinate-action-not-sofic: that is the negative theorem for the full ambient coset action; this identifies a large finite class of proper subactions where the failure cannot yet occur
---

Use

```text
Gamma=EL_r(k[N^d]) subset G=EL_r(k[Z^d]) rtimes SL_d(Z),       r,d>=3.
```

Let `A_1,...,A_m in SL_d(Z) intersect M_d(N)` be commuting positive
monomial compressors whose generated subgroup is free abelian of rank `m`.
Put `a_i=(1,A_i)` and

```text
P=<Gamma,a_1,...,a_m> subset G.
```

Then:

1. the coset action `P action P/Gamma` is sofic;
2. the symmetric double `P *_Gamma P` is sofic;
3. `L(Gamma) subset L(P)` is relatively embeddable over the scalars.

Thus simultaneous compression is not by itself the obstruction: every finite
family of commuting positive directions admits the required relative
embedding.  In particular, for `d>=3` the genuine two-direction slice

```text
A_1=I+E_12,       A_2=I+E_13
```

has all three properties.  These matrices commute, generate `Z^2), and
each gives a strict monomial self-embedding.

The mechanism is a directed `N^m` telescope.  Every iterated image

```text
alpha_1^(v_1)...alpha_m^(v_m)(Gamma)
 = EL_r(k[(A_1^(v_1)...A_m^(v_m)) N^d])
```

is separable in `Gamma` by a finite monomial truncation.  Finite windows in
the telescope reduce to finitely many of these base coset actions, and the
commuting stable letters are then adjoined one at a time by cyclic-extension
permanence for sofic actions.  The general difference-cocycle embedding of a
double into a free generalized wreath product gives items 2--3.

This does not cover noncommuting compressor families or impose their
`SL_d(Z)` relations.  Since the full Kun--Thom coset action is nonsofic,
the first possible action obstruction is now localized beyond all
free-abelian positive compressor slices.

DERIVATION
multi-telescope-coset-action-and-double-proof
