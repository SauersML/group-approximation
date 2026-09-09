---
rg: 2
id: ascending-hnn-finitary-linear-family-is-sofic-non-mf
kind: claim
title: Every finitely generated Kazhdan group with a proper finite-index self-embedding yields a finitely generated sofic non-MF finitary linear group
distinct_from:
  kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family: that is the ordinary restricted wreath product with a finite perfect lamp, and needs residual finiteness of the base both for soficity and for its radical computation; this has a finitary linear kernel, needs no residual finiteness of L because it passes to the faithful quotient of the coset action, and its kernel is simple rather than a restricted direct sum.
  compression-action-theorem-for-finitary-linear-extensions: that is the general action theorem over an arbitrary base action; this is its canonical instance at the coset action of an ascending HNN extension, and supplies the group theory verifying its hypotheses.
  finitary-linear-extension-kazhdan-defect-kills-kernel: that is the earlier adjoined-point form of the non-MF criterion, with a single dyadic instance and no soficity claim; this is a family statement over every admissible self-embedding, with soficity, finite generation and the absence of finite normal subgroups.
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

**ESTABLISHED.** Let `L` be a finitely generated Kazhdan group and
`alpha : L -> L` injective with `1 < [L : alpha(L)] < infinity`. Put

```text
V = <L, u | u l u^-1 = alpha(l)>,   X = V/L,
B = ker(V -> Sym(X)),               Q = V/B.
```

Then

```text
GL_fin(F_2^(V/L)) x| Q
```

is finitely generated, sofic, not MF, and has no nontrivial finite normal
subgroup, and the two inverse-image identities hold with `Q` and the
image of `L` in place of `V` and `L`. In particular both equal the
finitary linear kernel whenever `Q` is residually finite.

**No residual finiteness of `L` is assumed.** After passing to the
faithful quotient `Q`, each level `L_j/B` acts faithfully with finite
orbits, so finite orbit actions separate its elements and it is
residually finite for free; the finite-index hypothesis is what makes the
orbits finite. Infinite motion comes from the parent map
`tau(gL) = g u^-1 L`, which is surjective and equivariant and decreases
height, so an element moving one point moves points at every height above
it.

DERIVATION
ascending-hnn-finitary-linear-family-proof
