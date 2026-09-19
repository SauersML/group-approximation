---
rg: 2
id: every-noninjective-star-fold-has-kernel-f-infinity
kind: claim
title: Every noninjective star fold has free kernel of countably infinite rank
distinct_from:
  permutation-camouflage-realizes-countable-actions: that proves a star-fold kernel is free and obtains infinite rank from infinitely many nontrivial fibers; this proves infinite rank from a single identified pair and therefore covers every noninjective fold.
  one-mf-black-hole-has-universal-endomorphism-monoid: that embeds the full transformation monoid and identifies partition kernels abstractly; this computes every nonzero such kernel as F_infinity.
artifacts:
  - non_mf_groups_exist.tex
  - notes/MF_REFLECTION_AND_CORONA_SUPPORT_CALCULUS.md
---

Let `B` be a nontrivial countable group with full MF radical, let `D<B` be a
proper subgroup, and for every nonempty countable set `X` put

```text
K_X=*_(D,x in X) B_x.
```

Every map of sets `p:X->Y` induces the factor-fold homomorphism

```text
P_p:K_X->K_Y,
```

which sends `B_x` identically onto `B_(p(x))`.  If `p` is noninjective, then

```text
ker(P_p) ~= F_infinity.                              (SFK1)
```

The conclusion already holds for the fold

```text
mu:B *_D B -> B.
```

Its kernel acts freely on the Bass--Serre tree, and its quotient graph has
two vertices and one edge for every coset in `B/D`.  A full-MF-radical group
has no proper subgroup of finite index, so `B/D` is countably infinite and

```text
ker(mu) ~= F_infinity.                               (SFK2)
```

For a general noninjective `p`, any identified pair of factors supplies a
retraction

```text
ker(P_p) -> ker(mu).
```

Since `ker(P_p)` is itself a countable free group, the retraction onto
`F_infinity` forces `(SFK1)`.

Consequently:

1. every noninjective morphism in the permutation-camouflage functor has
   kernel `F_infinity`;
2. every noninjective endomorphism `Phi_f` arising from a self-map of the
   universal star kernel has kernel `F_infinity`;
3. every nonzero partition kernel `N_E` in that group is `F_infinity`;
4. identifying even one pair of hidden factors gives an MF-equivalence with
   an infinitely generated MF kernel.

