---
rg: 2
id: thompson-t-has-full-mf-radical
kind: claim
title: Thompson's group T has full MF radical, equivalently T is not MF
distinct_from:
  thompson-v-is-not-mf: that is the same exclusion for V, which contains T; this is strictly stronger, because T <= V makes Rad(T) = T imply Rad(V) = V, while an MF model of T says nothing about V.
  lifted-thompson-t-is-not-mf: that is the exclusion for the torsion-free central extension T-bar; this is its quotient. Item 3 of lifted-thompson-t-mf-radical-dichotomy gives that implies this, and lifted-thompson-t-not-mf-via-central-eigencorners shows the gap between the two is one corona-commutant statement about the central unitary.
  jz-question-5-for-thompson-t-implies-f-nonamenable: that concerns a question of Juschenko--Zheng about T; this is an operator-norm approximation statement.
---

**OPEN.**  Thompson's group `T` (piecewise-dyadic homeomorphisms of the circle)
does not embed in the unitary group of a norm matrix corona
`prod M_(k_n) / (+) M_(k_n)`.

`T` is simple (Cannon--Floyd--Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996), Thm 5.8).  So the following are
equivalent:
- `T` is not MF;
- `Rad_MF(T) != 1`;
- `Rad_MF(T) = T`.

## Position in the graph

- **Upward.**  It implies `thompson-v-is-not-mf`, because `T <= V` and `V` is
  simple (route `thompson-v-not-mf-via-thompson-t`).  Through
  `property-t-free-leavitt-via-thompson-v-not-mf` it therefore implies the
  binary-Leavitt endpoint `property-t-free-leavitt-full-mf-radical`.
- **Downward.**  It is implied by `lifted-thompson-t-is-not-mf` (item 3 of
  `lifted-thompson-t-mf-radical-dichotomy`).
- **Towards the seed.**  Together with
  `lifted-thompson-t-centre-has-commutant-eigencorners`, it implies
  `lifted-thompson-t-is-not-mf` (route
  `lifted-thompson-t-not-mf-via-central-eigencorners`), and hence both deep
  inputs of `property-t-free-manuscript-results`.

## What a refutation looks like

The claim is refuted by an MF model of `T`, that is, operator-norm
asymptotic unitary representations of `T`'s finite presentation that
separate points.  Two remarks limit the search.
- `T` has no nontrivial finite-dimensional unitary representation, since it
  is infinite simple and finitely generated, and so is not residually
  finite.  An MF model must have unbounded dimension and must be only
  asymptotically multiplicative.
- Finite subgroups of `T` are cyclic (`finite-subgroups-of-thompson-t-are-cyclic`),
  and the rotation subgroup `Q/Z cap Z[1/2]` is locally cyclic.  So local
  obstructions of the finite-subgroup kind that are used for `V` (for example
  through `S_4 *_(S_3)` gluings) are not available for `T`.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-ptm-last1, reframing): attack deferred;
  node created to carry an exact decomposition.**  This node was created to
  record that the flagship hole `lifted-thompson-t-is-not-mf` is equivalent to
  this claim plus `lifted-thompson-t-centre-has-commutant-eigencorners`.  No
  direct attack was made.  Two routes that one might copy from `V` do not
  carry over.
  - *Kazhdan transport.*  `T <= V` has the Haagerup property
    (`thompson-v-has-haagerup-property`), so it has no infinite Kazhdan
    subgroup to transport from.
  - *Finite-subgroup gluing.*  The `S_4 *_(S_3) S_3` presentation of `V`
    (`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`) and the op-norm
    defect-gap criterion for `V` posted on the live bus in wave 16 use
    non-cyclic finite subgroups.  `T` has only cyclic ones.

  The first falsifiable step for the next worker is to find the analogue for
  `T` of that defect-gap criterion.  A candidate is a presentation of `T` or
  of `C_T(r_1)` as a quotient of an amalgam of finite cyclic groups.  By item
  4 of `central-eigencorners-die-over-full-radical-quotients`, any single
  `C_T(r_k)` may be used instead of `T`.
