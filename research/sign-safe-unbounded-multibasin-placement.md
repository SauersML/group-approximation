---
rg: 2
id: sign-safe-unbounded-multibasin-placement
kind: claim
title: Place the combined private sampler and additive decoder without unbounded multi-basin holonomy
distinct_from:
  random-private-matching-eliminates-fixed-multibasin-contours: that removes every fixed-radius family; this must control arbitrarily long pieces uniformly in the finite presentation.
  private-matching-free-product-separates-pauli-signs: that handles the mixed matching in isolation; this includes the same-basis parity, equality, and commutation incidences.
  cayley-module-bilinear-certificate-protects-pauli-mark: that proves a finite invariant-pairing certificate excludes every composite sign collapse; this must construct such a certificate for the private sampler.
---

OPEN.  Give the combined repeated-LDPC same-basis complex and private X-Z
matching ordinary group-word addresses such that all required prototypes
have uniform relator area and the two mixed signs remain separated in one
exact marked model.

`random-private-matching-eliminates-fixed-multibasin-contours` removes every
fixed finite obstruction while retaining the Weyl gap, but fixed-radius
avoidance is not itself an exact-model proof.

There is now a sharper positive target which does not ask for a direct
classification of all long diagrams.  By
`cayley-module-bilinear-certificate-protects-pauli-mark`, it is enough to
construct one finitely presented address group `A`, finite-rank regular
Cayley occurrence modules

```text
M_X=F_2[A]^k/R_X,       M_Z=F_2[A]^ell/R_Z,
```

whose finitely generated relation submodules contain all translated
same-basis faces, together with an `A`-invariant bilinear form

```text
beta:M_X times M_Z -> F_2
```

taking the sampled values `a_t.b_t` on the two mixed prototype orbits.  The
translation/phase representation on `ell^2(M_X)` then keeps `J=-I` and
automatically defeats every composite contour, regardless of length or
piece overlap.

Equivalently, in the diagonal coinvariants

```text
C=(M_X tensor_F2 M_Z)_A,
```

the mixed prototype tensors must have no binary linear dependence whose
prescribed signs sum to one.  This is the exact algebraic obstruction which
an unbounded sign-colliding contour would witness.

The first nontrivial dependence now has a closed-form test.
`opposite-sign-double-coset-collapses-pairing` shows
that, for base classes `x,z` and sign offsets `p_0,p_1`, the quotient-module
stabilizers

```text
H_X=Stab_A(x),                 H_Z=Stab_A(z)
```

must satisfy

```text
H_X p_0 H_Z  intersect  H_X p_1 H_Z = empty.
```

This separation must be checked after adjoining all equality and parity
submodule relations.  A path which fixes `x` and carries `p_1 z` to
`p_0 z` makes the two prototype tensors equal in diagonal coinvariants and
immediately forbids opposite values.  Thus a free-product separation before
the same-basis quotient is not sufficient.

There is an algebraic model with no such collision: the natural and
contragredient modules of the finitary linear actor, paired by evaluation,
separate the two values by definition.  It does not close this claim.
`oligomorphic-gl-has-unbounded-stabilizer-fillings` shows that the contextual
transporters in that model cannot be replaced by fixed ordinary group-word
occurrences with uniform relator area.  The surviving construction must
therefore give literal Cayley-module representatives satisfying the displayed
post-quotient separation, rather than only an abstract vector/covector
orbit model.

Thus relative small cancellation is only one possible construction method,
not part of the necessary conclusion.  The remaining issue is genuinely
global: realize the recursive private sampler and the repeated-LDPC face
submodules in finitely many Cayley orbits while extending their prescribed
mixed signs to the invariant quotient pairing above.  Bounded occurrence
and avoidance of every fixed-radius obstruction do not imply that extension.
