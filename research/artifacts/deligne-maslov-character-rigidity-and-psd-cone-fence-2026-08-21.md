# Character rigidity fixes the Maslov trace; strict Gram regularization still fails

## 1. Exact trace classification

The recent character-rigidity theorem of Dogon, Glasner, Gorfine, Hanany,
and Levit applies directly to the Deligne lattice `E_3`, because their
Theorem 1.5 allows arbitrary center.  Every extreme trace of `E_3` is either
finite-dimensional or induced from the center.

In a nontrivial Maslov sector the first alternative is excluded by Deligne's
finite-dimensional central invisibility.  The center of `E_3` is the
six-element preimage of the center of `Sp_4(R)`.  Fixing the order-three
covering character leaves two possible full central characters.  Hence the
trace simplex of the twisted fibre is exactly the segment joining their two
central-regular traces.  Cutting the remaining order-two center gives two
unique-trace fibres.

This is useful but not a Maslov gap.  It proves that any hypothetical
tracial-matricial model already has the canonical regular trace profile.  It
does not decide whether that trace is Connes embeddable, and it cannot make a
ucp coordinate lift: such a lift would make the trace amenable and contradict
the already established no-amenable-trace theorem.

## 2. Why strict positive-kernel regularization cannot supply the lift

A tempting repair is to mix an approximately label-compatible positive Gram
matrix with a strictly positive, exactly label-compatible regular kernel,
then project back to the affine label space.  The hoped-for estimate is an
error bound proportional to the label defect divided by the mixing weight.
It is false even for bounded diagonal matrices.

Let

```text
A_d=diag(-1,1,...,1),
L_d={I+sA_d:s in R},
H_d=diag(1,3,...,3).
```

Although `H_d>=I` and is only `2/sqrt(d)` from `L_d`, it is distance exactly
one from `PSD intersect L_d`.  Moreover, for every fixed `0<t<1`, it has the
strictly regularized form

```text
H_d=(1-t)G_d+tI,   G_d=(H_d-tI)/(1-t)>=0.
```

The one bad affine eigenvalue is invisible in normalized Hilbert--Schmidt
distance, while positivity forces the single affine parameter to move on all
`d-1` remaining coordinates.  Therefore a Maslov Gram argument needs a
specific uniform angle theorem for its arithmetic label space; the Slater
margin itself gives no dimension-free control.

## 3. Remaining target

After the Kassel rank-one braid closes approximate centrality and character
rigidity fixes the trace, the unresolved assertion is now precisely:

> exclude a Connes-embeddable central-regular trace in either nontrivial full
> central character fibre, by a genuinely matrix-specific argument whose
> positivity/affine cone angle is uniform in dimension.

Finite tracial SOS, fixed Choi levels, finite root atlases, and generic strict
PSD regularization do not provide that argument.
