---
rg: 2
id: prime-field-weyl-uniqueness-proof
kind: route
title: Use the regular split-torus normalizer and the first cubic trace
target: prime-field-iwahori-weyl-endpoint-is-unique-away-from-three
requires: []
---

Because the characteristic is not three, the eigenvalues `2` and `2^(-1)`
of `r` are distinct.  Hence `r` is regular split semisimple.  Every element
conjugating `r` to `r^(-1)` lies in the nontrivial coset of the split-torus
normalizer, so it has a lift

```text
X=h(a)w=[0 -a; a^(-1) 0]                              (PFW1)
```

for some `a in k^*`, up to the central sign.  Such `X` automatically squares
to `-I`, so the involution row adds no further restriction in `PSL_2(k)`.

Now

```text
X t=[0 -a; a^(-1) a^(-1)]                             (PFW2)
```

has determinant one and trace `a^(-1)`.  The equation `(xt)^3=1` in the
projective group says `(Xt)^3` is `I` or `-I`.  Since the characteristic is
not three and `(PFW2)` is not central, its two eigenvalues are the two
nontrivial compatible cube roots.  Equivalently by Cayley--Hamilton,

```text
tr(Xt)=-1  if (Xt)^3= I,
tr(Xt)= 1  if (Xt)^3=-I.                              (PFW3)
```

Therefore `a^(-1)=+-1`, so `a=+-1`.  But `h(-1)=-I` is central and vanishes
in `PSL_2(k)`.  Both choices in `(PFW1)` thus give the same projective
element `w`, proving uniqueness.

