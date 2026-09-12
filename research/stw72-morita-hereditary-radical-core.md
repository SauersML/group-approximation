---
rg: 2
id: stw72-morita-hereditary-radical-core
kind: claim
title: Every LXXII counterexample has a stable sigma-unital Morita-hereditarily radical-free core
distinct_from:
  stw72-purely-infinite-radical-reduction: that theorem removes all purely infinite ideals and controls the remaining ideals; this theorem shows that the obstruction persists in every nonzero hereditary subalgebra, is invariant under Morita localization, and admits a stable sigma-unital normal form.
artifacts:
  - research/artifacts/stw72-morita-hereditary-core-audit-2026-08-30.md
---

Suppose `A` is weakly purely infinite but not purely infinite, and let

```text
B=A/P_pi(A)
```

be its nonzero purely-infinite-radical-free quotient.  Then every nonzero
hereditary C-star subalgebra `C subset B` is weakly purely infinite, is not
purely infinite, and has zero purely infinite radical.  Equivalently, no
nonzero hereditary subalgebra of `B` has the Global Glimm Property.

If `n` witnesses weak pure infiniteness of `B`, then every nonzero hereditary
subalgebra `C subset B` contains a class `x in Cu(C)` satisfying

```text
x < 2x <= ... <= nx = infinity x.
```

Thus the residual obstruction is local in every hereditary corner: uniform
finite saturation holds there, but Cuntz idempotence still fails there.

In particular, choosing any nonzero `b in B_+` and putting

```text
D=Her(b) tensor K
```

produces a stable sigma-unital weakly-but-not-plain purely infinite algebra
with zero purely infinite radical, and every nonzero hereditary subalgebra of
`D` has the same radical-free property.  Therefore Problem LXXII is equivalent
to its restriction to stable sigma-unital algebras with this
Morita-hereditary radical-free property.  Nuclearity, exactness, and
separability are preserved when present.

There is also an exact firewall for a purely infinite seed that first appears
in a quotient.  If `0 != Q ideal B/I` is purely infinite and `J` is its
inverse image in `B`, then `I` is nonzero and

```text
0 -> I -> J -> Q -> 0
```

has radical-free weakly-but-not-plain purely infinite algebras at both `I`
and `J`, but a purely infinite quotient `Q`.  Thus the only quotient seed not
already killed by the radical must cross a non-purely-infinite lower
boundary.
