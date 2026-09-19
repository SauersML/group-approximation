---
rg: 2
id: stw84-commensurable-stabilizer-field-proof
kind: route
title: Resolve each nonsplit stabilizer fiber over the dual of its central core
target: stw84-commensurable-stabilizer-wreath-bound
requires:
  - stw84-directed-union-uniform-bound
  - stw84-abelianization-rank-lower-bound
artifacts:
  - research/artifacts/stw84-commensurable-stabilizer-wreath-2026-08-30.md
---

We use Eckhardt--Wu, arXiv:2408.07223v2, Theorem 5.1, Theorem 4.6,
Lemma 5.13, and Theorem 5.9, together with the continuous-field estimate in
their Lemma 2.2(5).  The point of the proof is that none of these inputs
requires the central extension below to split.

## The finite-stage stabilizer bound

Let `F` be finite, let `V<=A` be finitely generated, and let `V` act on a
countable invariant subset `T<=S`.  Write `D=C*(F)` and let

`Omega=Spec Z(D^(tensor T))`.

This is zero-dimensional.  For `x in Omega`, the coefficient fiber `D_x` is
an infinite tensor product of full matrix algebras.  Fix `N<=V_x`, and put

`J=N intersection H`, `M=N/J`.

The subgroup `J` acts trivially on `D_x` and is central in `N`.  Consequently
`D_x rtimes N` is a `C*(J)=C(J_hat)`-algebra.  Its fiber at a character
`chi in J_hat` is

`D_x rtimes_(alpha_bar,omega_chi) M`,                    `(CMW3)`

where `omega_chi` is the scalar cocycle supplied by the central extension
`0 -> J -> N -> M -> 0`.  This is the standard central-extension field;
it is valid without a section homomorphism.

Here the field hypothesis is precise.  All groups involved are amenable, so
the reduced crossed-product picture shows that the subgroup map
`C*(J)->D_x rtimes N` is injective; it is unital and its image is central.
It therefore supplies the nondegenerate central `C(J_hat)`-map required of an
`J_hat`-C*-algebra.  Eckhardt--Wu Lemma 2.2(5), citing Carrion Lemma 3.1,
applies to every separable `X`-C*-algebra; it does not require an additional
continuity assertion for the associated upper-semicontinuous bundle.

The action of `M` on `T` has finite point stabilizers.  Indeed,

`N_t/J -> A_t/H`

is injective for every `t`, and the group on the right is finite.  Choose a
torsion-free finite-index subgroup `K<=M`.  Then `K` acts freely on `T`.
Since `x` is `N`-invariant, regrouping along the `K`-orbits gives a
`K`-equivariant identification

`D_x = B^(tensor K)`,                                    `(CMW4)`

where `B` is scalar, a full matrix algebra, or a UHF algebra.

If `B` is non-scalar, every nonidentity Bernoulli shift in `(CMW4)` is
strongly outer.  Eckhardt--Wu Theorem 4.6 applies also to the scalar-twisted
action, so the crossed product by `K` is in their class `C`.  Iterating the
twisted crossed product through the finite group `M/K`, their Lemma 5.13 and
Sato's finite-group permanence show that `(CMW3)` is finite-dimensional or
a finite sum of simple nuclear `Z`-stable algebras.  Hence

`dim_nuc((CMW3))<=1`.                                    `(CMW5)`

If `B=C`, then `D_x=C` and `(CMW3)` is the twisted group algebra
`C*(M,omega_chi)`.  Now `M` is finitely generated abelian and
`rank_Q(M)<=q`, so its nuclear dimension is at most `t(q)` by definition.
Eckhardt--Wu Theorem 5.9 proves that `t(q)<infinity`: for abelian rank at
most `q`, the second-homology rank is uniformly bounded by `q choose 2`, so
their bound depends only on `q`.

The dual `J_hat` has covering dimension `rank_Q(J)<=h`.  Applying the
continuous-field estimate to `(CMW3)` therefore yields

`dim_nuc(D_x rtimes N)+1 <= (h+1)(b(q)+1)`.              `(CMW6)`

Eckhardt--Wu Theorem 5.1 and their equation (5.1) now give the exact
prefactor used here: for the finitely generated abelian group `V`, its
polynomial-growth degree is `rank(V)`, the two dynamical factors are bounded
by `3^rank(V)` and `3^rank(V)(dim(Omega)+1)`, and `dim(Omega)=0`.  Hence

`dim_nuc(D^(tensor T) rtimes V)+1`

`   <= 9^rank(V) (h+1)(b(q)+1)`

`   <= 9^r (h+1)(b(q)+1)`.                              `(CMW7)`

The estimate is independent of the finite lamp, the actor torsion, the
orders of the residual stabilizers, and the choice of finite stage.

## Exhaustion and the rank-zero residual case

Exhaust `L` by finite subgroups, `A` by finitely generated subgroups, and
`S` by invariant hulls of finite sets, exactly as in
`stw84-almost-free-permutation-limit-proof`.  The stabilizer hypothesis is
inherited because

`(V intersection A_s)/(V intersection H) -> A_s/H`

is injective.  Equation `(CMW7)` and
`stw84-directed-union-uniform-bound` prove the upper bound in `(CMW1)`.
Killing the lamp kernel gives the quotient onto `A`, so
`stw84-abelianization-rank-lower-bound` gives the lower bound `r`.

Suppose finally that `q=0`.  In the full group

`G=(direct_sum_S L) rtimes A`,

the subgroup `H` is central and `G/H` is locally finite: its lamp kernel is
locally finite and its actor quotient `A/H` is torsion abelian.  Thus `C*(G)`
is a `C(H_hat)`-algebra whose fiber at `chi` is a twisted group algebra of
the locally finite group `G/H`.  Every such twisted group algebra is AF,
being the inductive limit of the finite-dimensional twisted algebras of its
finite subgroups.  Since `dim(H_hat)=h`, the field estimate gives
`dim_nuc C*(G)<=h`.  The quotient onto `A` gives the reverse inequality,
proving `(CMW2)`.

As above, the `C(H_hat)`-algebra structure comes from the injective unital
central map `C*(H)->C*(G)`.  Injectivity follows in the reduced picture from
amenability, and the same general `X`-C*-algebra estimate applies; no claim of
norm-continuity of the bundle is being smuggled into `(CMW2)`.
