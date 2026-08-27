---
rg: 2
id: mihailova-nonseparable-coset-stabilizer
kind: claim
title: A Mihailova fiber product gives an effective nonseparable stabilizer in the replacement actor
distinct_from:
  graph-coset-mixed-module-is-sofic: that proves separability when projection to the virtually-free factor is injective; this stabilizer has a nontrivial vertical kernel and is explicitly nonseparable.
  coordinate-action-not-sofic: that imports nonsoficity of one arithmetic coset action; this proves only failure of residual finiteness for a new explicit coset action and does not silently promote it to nonsoficity.
  algebraic-compact-action-envelope-for-non-ce-relation: that requires the fixed non-CE factor to embed in an algebraic crossed product; this supplies an effective Haar coset-module candidate but not that embedding.
---

Let `Gamma_0` be the virtually-free Manzoor source actor.  There is an
explicit finitely generated subgroup

```text
P < Gamma_0 x SL_3(Z)                                  (MFP1)
```

which is not separable in the ambient group.  It can be chosen as follows.
Take a fixed finitely presented nonsofic group

```text
Q=<x_1,...,x_m | r_1,...,r_k>
```

from `finitely-presented-nonsofic-group-exists` (for example the published
Fournier--Facio witness), embed two copies of the rank-`m` free group into
`Gamma_0` and `SL_3(Z)`, and take the pullback of the diagonal subgroup of
`Q x Q`:

```text
P_Q={(u,v) in F_m x F_m : ubar=vbar in Q}.              (MFP2)
```

The generators

```text
(x_i,x_i)  (1<=i<=m),       (r_j,1)  (1<=j<=k)          (MFP3)
```

generate `P_Q`, so `(MFP1)` is effective and finitely generated.  It escapes
the injective-projection fence maximally:

```text
P_Q cap ({1} x F_m) = {1} x ker(F_m -> Q).
```

Since `Q` is nonsofic it is not residually finite.  The diagonal in `Q x Q`,
and hence `P_Q` in `F_m x F_m`, is nonseparable.  Nonseparability persists in
`Gamma_0 x SL_3(Z)`.

Consequently the transitive coset action on
`X=(Gamma_0 x SL_3(Z))/P` is not residually finite.  The compact Haar coset
module

```text
K=(Z/2)^X,
W=(direct_sum_X Z/2) rtimes (Gamma_0 x SL_3(Z))         (MFP4)
```

is effective: `W` is finitely generated and recursively presented.  This is
the first explicit mixed coset module in the replacement actor that survives
all separability and spectator fences.

It also survives the homoclinic-density screen for a structural reason.
`infinite-stabilizer-coset-bernoulli-has-trivial-homoclinic-group` gives
`Delta(K,Gamma_0 x SL_3(Z))={1}` because `P` is infinite.  Thus this is not a
dense-finite-support algebraic shift in disguise; the Hayes model-measure
criterion has no hypothesis to act on here.

No stronger conclusion is asserted.  In particular, nonseparability does not
by itself prove that the coset action is nonsofic, and nonsoficity of the
quotient `Q` cannot simply be pushed through the free-group kernels in
`(MFP2)`.  In fact Gao--Kunnawalkam Elayavalli--Patchell prove that **every**
action of a free group on a countable set is sofic, so each coordinate action
on `(Q x Q)/Delta Q` is sofic regardless of `Q`.  The combined `F_m x F_m`
action is not residually finite; deciding whether it is sofic is precisely a
commuting-actions problem.  Whether `L(W)` contains the fixed non-CE relation
factor (or is itself non-CE) is the remaining analytic question.

The weakest orbit-chart attack is now closed.
`mihailova-left-right-local-models-do-not-see-q` applies Alekseev--Thom to
show that the left-right action has finite local isometric models for every
quotient `Q`, because the actor `F_m x F_m` is residually finite.  This remains
true for the nonsofic `Q` used here.  Such models therefore cannot decide the
combined action.  What remains is exactly the upgrade from arbitrary finite
metric patches to positive-density Hamming orbit charts, or equivalently an
operator-level promotion toward finite-dimensional approximation of the
left-right representation on `ell^2(Q)`.

The operator promotion is now isolated in
`mihailova-actor-liftable-ce-forces-q-hyperlinear`.  If a Connes embedding of
the Bernoulli crossed product represents the canonical `F_m x F_m` actor by
exact finite-dimensional projective representations at every matrix level,
conjugating
the centered base lamp gives finite-dimensional coefficients converging to
the quasi-regular coefficient of `ell^2(Q)`.  Hence `Q` would be hyperlinear.
This needs no Cartan assumption, but it is only a boundary: the explicit `Q`
here is known nonsofic, not nonhyperlinear, so hyperlinearity of `Q` would not
contradict the input.  The unresolved gap in bare Connes embeddability is
exactly that its actor matrices obey the cross-commutation relations only
modulo normalized Hilbert--Schmidt error, rather than merely scalar error,
at each level; a diagonal Cartan does not by itself exactify those
normalizers even projectively.

There is also no shortcut through a canonical quotient corner.
`infinite-kernel-canonical-compression-is-zero` shows that if a projection
`p` anywhere in this full Bernoulli crossed product satisfied
`p u_n p=p` for the infinite free-cover kernel, then `p`, viewed in the
regular `L^2` space, would be an invariant vector for an infinite subgroup
and hence zero.  Thus the quotient `Q` cannot be installed by compressing the
canonical actor unitaries, even with a non-base and non-Cartan projection.
The projective cross-stability/state-specific promotion boundary is not a
disguised quotient-corner construction.

The first genuinely Fourier-mixed normalizer ansatz now has an exact normal
form.  By `orthogonal-finite-fourier-reps-are-orbit-cocycles`, a unitary
written as a finite orthogonal sum `sum_g u_g p_g` is a finite-valued
full-group transformation, and a family of such unitaries obeys a source
group multiplication table exactly when its source partitions satisfy the
explicit cocycle equations `(OFC3)`.  Three grades already give a
nonhomogeneous exact involution by swapping two measurable pieces, so support
orthogonality cannot force collapse beyond the existing two-grade theorem.
For the Mihailova candidate, the bounded-support normalizer problem is
therefore precisely a regular-trace finite-range cocycle problem inside the
left-right Bernoulli orbit relation.  Arbitrary nonnormalizing coefficients
remain the separate Hadamard-cell branch.

For the property-`(T)` Fournier--Facio choice of `Q`, in fact the entire
orthogonal cocycle branch closes.  `kazhdan-finite-cocycles-cannot-enter-haagerup-actions`
uses that `F_m times F_m` is Haagerup.  Adding its free Bernoulli shift
preserves the partition equations and makes the represented `Q`-action free.
Its relation would be a subrelation of a Haagerup orbit relation and hence
Haagerup, while property `(T)` of `Q` makes it a property-`(T)` relation.
Such a relation has finite classes, contradicting freeness of the infinite
group `Q`.  Therefore no regular-trace orthogonal finite-range cocycle exists,
even with genuinely mixed left-right labels.  Only the nonnormalizing
Hadamard-cell/full-envelope branch survives.

Inside the simplified left-right crossed product, even that nonnormalizing
branch is now closed for the property-`(T)` choice of `Q`.
`regular-kazhdan-reps-avoid-haagerup-crossed-products` observes that any
exact regular-trace unitary image of `Q`, with arbitrary Fourier
coefficients, generates a diffuse relatively rigid copy of `L(Q)`.  Popa's
relative-Haagerup exclusion forbids it because the base is abelian and
`F_m times F_m` is Haagerup.  This does not dispose of the original full
`Gamma_0 times SL_3(Z)` coset-module host: cells using arithmetic grades
outside the free left-right subgroup see a non-Haagerup actor.  Those grades,
or a direct embedding of the fixed non-CE factor which bypasses `Q`, are now
load-bearing.

The arithmetic-grade survivor has one canonical form.
`mihailova-sl3-restriction-is-coset-amplification` computes the restriction
of `(Gamma_0 times SL_3(Z))/P` to `SL_3(Z)` as a disjoint union of copies of
`SL_3(Z)/N`, where `N=ker(F_m->Q)` is the vertical Mihailova kernel.
Moreover `mihailova-envelope-forces-one-sl3-coset-wreath` combines this with
finite module extraction: if the mixed envelope worked, the single group

```text
(direct_sum_(SL_3(Z)/N) C_2) rtimes SL_3(Z)
```

would already be nonhyperlinear.  Finite orbit multiplicity cannot conceal
the obstruction, since the `n`-copy diagonal semidirect product embeds in the
`n`th power of the one-copy wreath.  Deciding this one vertical coset action
is therefore the exact remaining Mihailova problem.
