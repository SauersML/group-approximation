---
rg: 2
id: stw74-separable-two-level-projection-descent
kind: claim
title: In a separable LXXIV algebra a hereditary subalgebra whose 2x2 matrices contain a projection contains one
distinct_from:
  stw74-hypothesis-forces-property-sp: that asks for a projection in every nonzero hereditary subalgebra of an arbitrary LXXIV algebra; this asks only for level-two descent in separable LXXIV algebras.  The two are equivalent through the routes stw74-separable-two-level-descent-forces-sp and stw74-property-sp-gives-separable-two-level-descent, but the statements differ.
  stw74-lxxiv-hinge-is-two-level-descent: that is a proved equivalence inside each LXXIV algebra; this is the open level-two statement itself, restricted to separable algebras.
  stw74-two-level-failure-has-full-spectrum-sphere: that is the proved structure theorem for a failure of this claim; this is the open claim that no such failure exists.
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Let `B` be a separable unital simple C\*-algebra in which every nonzero
projection is infinite.  If `H` is a hereditary C\*-subalgebra of `B` and
`M_2(H)` contains a nonzero projection, then `H` contains a nonzero
projection.

By `stw74-lxxiv-hinge-is-two-level-descent` and
`stw74-counterexamples-have-separable-subcounterexamples` this is equivalent
to `stw74-hypothesis-forces-property-sp`; by
`stw74-two-level-failure-has-full-spectrum-sphere` a counterexample `(B,H)`
carries `x,y in B` with `x*x+y*y=1`, all four products `xx*,xy*,yx*,yy*` in
`H`, and both `Her(x*x)` and `Her(y*y)` projectionless.

## Attempts

1. **Column normal form (proved).**  Proper infiniteness of the projection in
   `M_2(H)` (stabilized claim) plus the fullness normal form give an
   isometric column `v=(x,y)^T`, `v*v=1`, `vv* in M_2(H)`.  So the claim is
   equivalent to: *for such `x,y`, `H` has a nonzero projection*.  What is
   missing is an element `z` with `zz* in H` and `z*z` invertible (Lemma K
   of the artifact then gives the projection).  The natural candidates
   `z=c_1 x + c_2 y` with `c_i in B` give `zz* = sum c_i (xx*-type) c_j*`,
   which leaves `H` unless the `c_i` lie in the multiplier-type set
   `{c : cHc* subset H}`; this is where the attempt stops.
2. **Scalar mixing (dead).**  With scalar `c_i`, `zz* in H` holds, but no
   `z*z` need be invertible: in `M_2(C)`, `x=e_11`, `y=e_12` satisfy the
   algebraic data with `T=x*y` nilpotent of norm `1` and every scalar mix of
   rank one.  In a counterexample every scalar mix has `sigma(z*z)=[0,1]`
   and projectionless support (proved in the full-spectrum-sphere claim),
   so the sphere of scalar mixes is uniformly non-invertible.
3. **Gram-matrix reformulation (circular).**  Writing `G=[[x*x,x*y],[y*x,y*y]]`
   and asking for a left-invertible compression of `G` inside `H` returns
   exactly the statement "some `M_2(H)`-projection equivalent to `1` has a
   corner equivalent to `1` inside `H`", i.e. the claim again.
4. **Unit splitting (equivalent, open).**  By the dichotomy in the
   full-spectrum-sphere claim, the claim fails for some `B` iff some
   separable LXXIV algebra has a positive contraction `e` with `Her(e)` and
   `Her(1-e)` both projectionless.  No argument excluding this was found:
   properly infinite projections in `Her(e)` would have to be created from
   `e(1-e)`, whose spectrum is `[0,1/4]` when `sigma(e)=[0,1]`, and no
   comparison principle is available.
5. **Subhomogeneous models (not applicable).**  By
   `stw74-every-matrix-descent-threshold-occurs-subhomogeneously` (with
   `r=1`, `s=2`, so `m_0=2`) level-two descent genuinely fails for the
   projectionless type-I algebra `D_(1,2)`; so any proof must use the ambient
   LXXIV hypothesis, not only intrinsic properties of `H`.  The algebras
   `D_(r,s)` are non-unital and not simple, so they are not candidates for
   `B`; the claim asks to exclude hereditary subalgebras `H` of a simple
   LXXIV algebra that behave at level two as `D_(1,2)` does.
6. **Relative (SP) through inclusions (known, insufficient).**  Passing to an
   inclusion with a conditional expectation and asking for a relative (SP)
   is already in Gow--Hernandez Palomares, *Property (SP) and Inclusions of
   C\*-algebras*, arXiv:2608.30057v1 (2026-08-30).  There `A subset B` is an
   SP-inclusion when `closure(aBa)` contains a nonzero projection for every
   nonzero `a in A_+`, and Theorem 4.4 (numbering as read from the TeX
   source) says that if `A subset B` has a faithful conditional expectation
   with the pinching property, then `A subset B` is an SP-inclusion iff `B`
   has (SP).  This moves (SP) between the inclusion and the larger algebra;
   it does not produce projections in an LXXIV algebra, so it does not
   address this claim.
7. **Nuclear version.**  The same argument using the CPAP clause of the
   separable-subcounterexample claim shows that the nuclear form of Problem
   LXXIV follows from this claim restricted to separable CPAP algebras; no
   nuclear-specific tool (for example tracial or `Z`-stability arguments) is
   available, since counterexamples are traceless (a tracial state would
   vanish on the nonzero projection `1-vv*` for an isometry `v` with
   `vv*!=1`, contradicting faithfulness on a simple algebra) and not
   `Z`-stable (by `stw74-z-stability-and-finite-nuclear-dimension-close-hinge`).
