---
rg: 2
id: hrf-alt-psl2-detector-composition-obstruction-proof
kind: route
title: Cyclic Sylow inversion and defining-characteristic torus weights kill PSL2 degree-two cohomology, then unique splittings propagate
target: hrf-alt-psl2-detectors-need-new-composition-factors
requires:
  - hrf-alt-edge-twist-finite-detector-spectrum
---

Write `C=F_p`, with trivial action and `p>=5`. Every group
`PSL_2(q)`, `q>=4`, is perfect, hence has `H^1(-;C)=0`. We prove
`H^2(PSL_2(q);C)=0` for every prime power `q`.

If `p` does not divide the group order, transfer gives vanishing.
If `p` divides the group order but not `q`, its Sylow `p`-subgroup is
cyclic of order `p^a`, lies in a split or nonsplit torus, and is inverted
by an element of the torus normalizer. Restriction on `H^2` to the Sylow
subgroup is injective by transfer, with image invariant under inversion.
But `H^2(C_(p^a);C)=C`, and inversion acts by `-1`: in a central
extension a lift `t` of a generator has `t^(p^a)=z^b`, and inverting
the generator replaces `b` by `-b`. Thus the invariant subspace is zero.

It remains to treat `q=p^f`. The Sylow subgroup is
`P=(F_q,+)`, and diagonal matrices act on it by `x -> a^2 x` for
`a in F_q^*`. A central extension of this elementary abelian group by
`C` is determined injectively by its alternating commutator map
`b:Λ^2 P -> C` and its power map `h:P -> C` sending `x` to the
`p`th power of any lift. The map `h` is additive: the extension is
nilpotent of class at most two, and `binom(p,2)` is divisible by `p`.
If both `b` and `h` vanish, the extension is an elementary abelian
group and splits as a vector-space extension. Both constructions are
natural under automorphisms of `P`.

Extend scalars to an algebraic closure of `F_p`. On the dual of `P`,
the square torus has weights `a^(2p^i)`, `0<=i<f` (or their inverses,
depending on the action convention). On alternating bilinear forms the
weights are `a^(2(p^i+p^j))`, `0<=i<j<f`, with the same sign convention.
No listed exponent is divisible by `q-1`: the linear exponents satisfy
`0<2p^i<=2p^(f-1)<p^f-1`; when `f>=2` the alternating exponents satisfy

```
0 < 2(p^i+p^j) <= 2(p^(f-1)+p^(f-2)) < p^f-1.
```

For `f=1` there is no alternating term and `2<p-1`. Thus there is no
torus-invariant nonzero `b` or `h`, hence no torus-invariant class in
`H^2(P;C)`. Restriction from `PSL_2(q)` is injective and has invariant
image, proving the required vanishing in defining characteristic too.

For each cyclic `C_l` with `l != p`, both `H^1` and `H^2` vanish. For
`H^2`, a central extension has a lifted generator with `t^l=z^a`;
replacing `t` by `t z^b`, choosing `a+lb=0` in `F_p`, gives a section.
The section is unique since `Hom(C_l,C)=0`.

The property `H^1(-;C)=H^2(-;C)=0` is closed under group extensions with
trivial coefficients. Indeed let `1 -> K -> Q -> L -> 1` have this
property for `K,L`. Every homomorphism `Q -> C` vanishes on `K` and
factors through `L`, so `H^1(Q;C)=0`. Any central extension of `Q` by
`C` splits uniquely over `K`; uniqueness makes the lifted copy of `K`
normal under the whole extension. Quotienting by that copy gives a
central extension of `L`, which splits. The original extension is its
pullback to `Q`, hence also splits. This proves `H^2(Q;C)=0`.

Induction along a composition series now proves that any `Q` with all
composition factors in the displayed collection has `H^2(Q;C)=0`.
The detector-spectrum theorem then forces its lift discrepancy to be
zero. It cannot detect a nonzero twist, proving the main assertion.

For the product-image corollary, an image in a product of surjective
maps onto nonabelian simple groups is subdirect. Goursat's lemma,
inducted over the factors, identifies it with a product of simple
factors, allowing diagonal identifications between isomorphic ones.
Its composition factors therefore stay in `S`. Equivalently, the
induction projects away one factor; its kernel is either that simple
factor or trivial, since the projection onto that factor is surjective
and the kernel's image is normal. This suffices without a classification
of the diagonal identifications.

No conclusion about the first cohomology of deeper kernels is used.
In particular this obstruction does not incorrectly replace a fixed-
quotient wreath moment test by a central-extension test.
