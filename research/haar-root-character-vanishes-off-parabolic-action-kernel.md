---
rg: 2
id: haar-root-character-vanishes-off-parabolic-action-kernel
kind: claim
title: A Haar root character is regular on its parabolic away from the action kernel
distinct_from:
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that excludes the Haar profile using finite-matrix origin; this is a tracial consequence of the Haar profile and stops at the kernel of the parabolic action.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that moves one nontrivial character atom through infinitely many dual characters; this moves one parabolic group element through infinitely many orthogonal GNS vectors.
---

Let `L=L_(F_2)(1,2)` and `n>=4`.  Use either of the two orientations

```text
N_col=<x_(i n)(a):i<n,a in L>,       H_col=St_(n-1)(L),
N_row=<x_(1 j)(a):j>1,a in L>,       H_row=St_(n-1)(L),
```

where the indicated upper-left, respectively lower-right, vertex normalizes
the root module.  Let `chi` be a character of `St_n(L)` satisfying

```text
chi(v)=0                    for every 1!=v in N.       (PRH1)
```

If `g in N H` has vertex part whose conjugation action on `N` is nontrivial,
then

```text
chi(g)=0.                                                   (PRH2)
```

More precisely, `(PRH2)` holds whenever the image of
`v |-> g^(-1)vgv^(-1)` is infinite.  In the binary-Leavitt row and column
modules every nontrivial elementary vertex action has infinite image: a
nonzero matrix coefficient exposes a nonzero right ideal `rL` in the column
orientation or a nonzero left ideal `Lr` in the row orientation, and every
nonzero one-sided ideal of `L` is infinite.

Thus a Haar root character has the regular-character value zero on every
parabolic coset whose vertex action is nontrivial, in addition to its assumed
regular values on `N`.  No conclusion is asserted for cosets whose vertex
part lies in the action kernel, or outside the parabolic.  In particular this
does not exclude the Haar profile: the regular character of the whole
Steinberg group satisfies `(PRH1)--(PRH2)` exactly.

DERIVATION
haar-root-parabolic-bessel-proof
