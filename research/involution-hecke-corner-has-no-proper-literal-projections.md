---
rg: 2
id: involution-hecke-corner-has-no-proper-literal-projections
kind: claim
title: An involution Hecke corner has no proper literal group projections
distinct_from:
  augmentation-one-corner-retains-a-character: that rules out a global characterless BCS map because the plus corner retains augmentation; this gives a canonical-Plancherel obstruction to even one proper projection of the form qgq.
  common-corner-literal-contexts-stop-at-bass-serre: that proves a compressed group element which is a corner unitary must stabilize the corner and then excludes finite Bass--Serre hosts globally; this classifies compressed group elements which are corner projections, in every host group, before gluing.
  single-involution-cannot-be-a-nonlinear-selector-carrier: that computes how one involution cuts the characters of a separate finite selector subgroup; this fixes the corner q=(1+h)/2 and compresses arbitrary literal group elements through it.
---

Let `Gamma` be any discrete group, let `h in Gamma` be a nontrivial
involution, and put

```text
q=(1+h)/2 in C[Gamma].                                  (IHC1)
```

For every group element `g in Gamma`, if

```text
p=q g q                                                  (IHC2)
```

is a projection in the finite corner `q L(Gamma) q`, then

```text
p=q  if g=e or g=h,
p=0  otherwise.                                         (IHC3)
```

Indeed the canonical trace gives

```text
tau(p)=tau(gq)
      =(1/2)(1_(g=e)+1_(gh=e)).                         (IHC4)
```

If `g` is neither `e` nor `h`, `(IHC4)` is zero, and faithfulness of the
canonical trace forces the positive element `p` to vanish.  The other two
cases are immediate from `(IHC1)`.  No finiteness, amalgam, HNN, or
presentation hypothesis on `Gamma` is used.

Consequently the proposed literal Halmos compiler cannot model the fixed
non-`R^U` Paddock--Slofstra BCS using one shared corner `(IHC1)`.  If every
Boolean projection had the advertised form

```text
p_x=q g_x q,
```

then `(IHC3)` would make every `p_x` either `0` or the corner unit `q`.
The BCS relations would therefore give a classical satisfying assignment,
hence a one-dimensional `R^U` model, a contradiction.  This fails already
for a single nonconstant Boolean coordinate; cross-context holonomy never
arises.

This also pinpoints what the familiar D8/Halmos calculation actually proves.
In a chosen matrix representation one can take

```text
h = [1 0; 0 -1],
g = [p 1-p; 1-p -p]
```

for a projection `p`; then `h` and `g` are involutions, `(hg)^4=1`, and the
upper-left compression of `g` is `p`.  But this is a **selected
representation sector**, not the regular D8 group algebra with only the
corner `(1+h)/2`.  In the canonical regular algebra, `(IHC4)` says that
`qgq` has trace zero for the distinct reflection `g`; it is a nonzero
self-adjoint Hecke operator in the generic D8 packet, hence cannot be a
projection.

To retain the matrix Halmos block inside a canonical group corner one must
first multiply by a finite-type central idempotent `z_rho` selecting the
desired irreducible sector and use

```text
Q=q z_rho,       Q g Q.
```

For a nontrivial higher-dimensional type, `epsilon(z_rho)=0`, so this also
removes the independent augmentation obstruction.  This is exactly the
existing signed-Hecke finite-type lane; sharing its noncentral subprojection
`Q` across cyclic contexts is the recorded block-escaping holonomy problem,
not a consequence of the bare D8/Halmos dilation.

The minus corner `(1-h)/2` does not provide a literal-projection escape:
the same trace computation is zero away from `g=e,h`, while `g=e` gives the
corner unit and `g=h` gives its negative rather than a projection.

