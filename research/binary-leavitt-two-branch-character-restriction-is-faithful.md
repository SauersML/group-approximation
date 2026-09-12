---
rg: 2
id: binary-leavitt-two-branch-character-restriction-is-faithful
kind: claim
title: The two binary Leavitt branch restrictions determine a global additive character
distinct_from:
  finite-branch-closure-erases-transverse-character: that rules out a nonzero transverse character on one finite branch-invariant window; this identifies the full infinite character exactly from both branch restrictions.
  leavitt-character-mass-escapes-to-finer-characters: that exhibits the finite-window marginal-coupling escape; this proves that the escape cannot be ambiguity of the pair of global branch labels.
artifacts:
  - research/binary-leavitt-two-branch-character-restriction-proof.md
---

Let the additive group of a ring `R` carry a binary Leavitt family

```text
t_i s_j=delta_(i,j),                 s_0t_0+s_1t_1=1.
```

For an additive character `chi:R->T`, define its two branch restrictions by

```text
F_i(chi)(a)=chi(a t_i),              i=0,1.             (BCR1)
```

Then

```text
F=(F_0,F_1): R^ -> R^ x R^                           (BCR2)
```

is an isomorphism of character groups.  Its inverse sends `(phi_0,phi_1)` to

```text
chi(r)=phi_0(r s_0) phi_1(r s_1).                      (BCR3)
```

In particular, two global additive characters agreeing on both right-prefix
subgroups `R t_0` and `R t_1` are equal.

For the Property-`(T)`-free corona decoder this removes one possible source
of ambiguity.  The two global branch labels jointly determine the source
label; the unresolved datum is instead operator-level **joint coupling**.
The projections obtained from the two branch conjugators need not belong to
one common abelian spectral algebra or have a nonzero controlled meet, so
label injectivity alone does not return a selected sparse atom to its own
multiplicity reservoir.

