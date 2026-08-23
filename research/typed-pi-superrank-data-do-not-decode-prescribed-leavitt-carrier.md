---
rg: 2
id: typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier
kind: claim
title: Typed PI and superrank data do not decode the prescribed Leavitt root carrier
distinct_from:
  first-leavitt-weyl-cell-has-exact-rectangular-model: that supplies the depth-one rectangular Weyl model and its two separate factor degrees; this adds the prescribed nontrivial root carrier and the quantitative failure of the three Leavitt products.
  mixed-steinberg-loops-admit-morita-rectangular-model: that treats arbitrary typed commutator triangles; this shows that adjoining every typed PI identity and both normalized Reynolds ranks still does not turn the two object identities into one carrier.
  controlled-fine-reflection-superrank-orientation-law: that computes an orientation ambiguity inside one controlled Pauli extension; this is the source-versus-two-child Morita ambiguity before any controlled-reflection orientation is chosen.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: that asks the full finite presentation to overcome the ambiguity; this is a firewall for the typed finite-coordinate language only, not a refutation of that decoder.
  target-saturated-reynolds-return-does-not-lock-leavitt-reservoir: that computes the exact nesting of the two adjoint Reynolds ranges and distinguishes target saturation, which the countermodel satisfies, from the source saturation actually needed to exclude it.
---

**ESTABLISHED FIREWALL.**  Fix the packet characteristic `p>=5`.  The
following entire depth-one data set has an exact finite-dimensional model
on a nontrivial order-`p` root phase:

1. the source Heisenberg packet and the two-child Heisenberg packet, with
   their full multiplication and commutator tables;
2. both branch transports and both diagonal returns;
3. every typed rank-five/six Steinberg multiplication triangle obtained by
   composing the rectangular branch coefficients;
4. the complete polynomial-identity data of the source label algebra
   `M_p` and target label algebra `M_(p^2)`, including a nonzero prescribed
   `s_(2p)` evaluation in the target; and
5. the two normalized adjoint Reynolds ranks

```text
c_source=p^(-2),                 c_target=p^(-4).       (TPS1)
```

The central root word is the scalar `zeta I`, for a fixed nontrivial
`p`th root `zeta`.  Consequently its prescribed nontrivial spectral
carrier is

```text
P=1-1_{ {1} }(zeta I)=I.                              (TPS2)
```

Nevertheless no contractions `S_0,S_1,T_0,T_1` on this carrier can make
all three relative Leavitt residuals smaller than `1/3`.  More precisely,

```text
epsilon=max(
 ||T_0S_0-P||_2,
 ||T_1S_1-P||_2,
 ||S_0T_0+S_1T_1-P||_2)
```

satisfies

```text
epsilon>=tr(P)/3=1/3.                                (TPS3)
```

Indeed cyclicity gives `tr(T_iS_i)=tr(S_iT_i)`.  The first two residuals
give

```text
tr(S_0T_0)+tr(S_1T_1)>=2tr(P)-2epsilon,
```

whereas the third gives, after taking real parts,

```text
tr(S_0T_0)+tr(S_1T_1)<=tr(P)+epsilon.
```

This proves `(TPS3)`.

Thus PI degree and normalized superrank are valid *detectors* of the
rectangular escape but not authenticators of a common reservoir.  In the
exact model they correctly report that the source is `M_p` and the target
is `M_(p^2)`; those reports coexist because the source identity is `1_E`
and the target identity is `1_(E direct_sum E)`.  Typed Steinberg triangles
preserve these object labels.  A standard polynomial evaluated separately
in either typed algebra, or a Reynolds rank computed separately for either
packet, never asserts that the two identities are the same physical
projection.

Consequently no derivation of
`affine-leavitt-prescribed-root-spectral-carrier-decoder` can end by merely
collecting more typed PI evaluations or more individual packet superranks.
It must add one genuinely **cross-typed** finite-matrix assertion: a common
intertwiner carrying a full target tuple into the source factor, equality
of the returned Reynolds ranges on one reservoir, or an HS-visible payment
for failure of such a return.  This firewall does not refute the full
decoder, because the exact rectangular model is not a representation of
the full affine-Leavitt Steinberg presentation.

The Reynolds formulation has a necessary direction.  By
`target-saturated-reynolds-return-does-not-lock-leavitt-reservoir`, the
rectangular model already has complete overlap of the smaller returned
target commutant with the larger source commutant.  That overlap is
`p^(-4)` and proves nothing.  The minimal scalar which excludes the model is
instead **source saturation**: the same overlap must be at least
`p^(-2)-o(1)`.  Its universal rank ceiling is `p^(-4)`, giving the fixed
payment `p^(-2)-p^(-4)`.  Thus “equality of returned Reynolds ranges” must
not be weakened to preservation of all target invariants under return.
