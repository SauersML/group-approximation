---
rg: 2
id: phase-free-cartan-observables-force-joint-lamp-targets
kind: claim
title: Collision localization and phase-free Cartan mass force joint lamp targets
distinct_from:
  finite-lamp-targets-glue-after-action-groupoid-completion: that glues a finite groupoid after its objects and arrows are supplied; this gives matrix observables sufficient to extract the arrows as approximately multiplicative permutations.
  finite-schreier-holonomy-is-the-lamp-gauge-obstruction: that asks whether supplied normalizers are related to a prescribed target by commutant gauge; this rounds near-Cartan normalizers and then discards all phases.
  invariant-cartan-completion: that asks abstractly for an actor-invariant Cartan in the ultraproduct; this identifies two finite-dimensional numerical observables, proves quantitative target bounds, and shows why deriving them from ordinary moments is the same open theorem.
  elementary-abelian-regular-normalizers-have-diffuse-fibers: that supplies exact diffuse normalizers far from monomials; this isolates the extra collision statistic which those local hypotheses do not control.
  canonical-regular-packets-leave-an-unbounded-cartan-reservoir: that tests fixed nonabelian and paired central-character packets; canonical trace leaves an unbounded multiplicity commutant, so the packet cannot select the rank-one masa assumed here.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED QUANTITATIVE SUFFICIENCY; EXTRACTION OPEN.**  Let
`D_d subset M_d` be a rank-one masa with minimal projections
`e_1,...,e_d`.  In a basis diagonalizing `D_d`, define for a unitary
`U=(u_ij)`

```text
Col_D(U)=d^(-1) sum_(i,j)|u_ij|^4,                      (CPC1)
Fix_D(U)=d^(-1) sum_i |u_ii|^2
        =||E_D(U)||_2^2.                                (CPC2)
```

The first number is a collision/localization moment; the second is
phase-free diagonal mass.  Suppose `Col_D(U)>=1-eta` with
`0<=eta<1/4`.  Then there is a monomial unitary `M` such that

```text
||U-M||_2^2 <=3 sqrt(eta).                              (CPC3)
```

Let `sigma_U` be the permutation underlying `M`; diagonal phases are
discarded.  For a tested actor product `gh=k`, put

```text
delta_(g,h,k)=||U_g U_h-U_k||_2,
a_s=sqrt(3) eta_s^(1/4).
```

Then the permutations obtained from `(CPC3)` satisfy

```text
d_H(sigma_g sigma_h,sigma_k)
 <=(1/2)(delta_(g,h,k)+a_g+a_h+a_k)^2.                 (CPC4)
```

If lamp cylinder projections `P_chi,P_(g chi)` lie in `D_d` and

```text
||U_g P_chi U_g^*-P_(g chi)||_2 <=epsilon_(g,chi),
```

then

```text
d_mu(sigma_g(supp P_chi),supp P_(g chi))
 <=(epsilon_(g,chi)+2a_g)^2.                           (CPC5)
```

Finally, for every tested nonidentity word `w`,

```text
FixFrac(sigma_w)
 <=(sqrt(Fix_D(U_w))+a_w)^2.                           (CPC6)
```

Consequently a common sequence of rank-one masas refining the growing lamp
PVMs, with

```text
Col_D(U_w)->1,       Fix_D(U_w)->0,
```

and vanishing covariance and product errors, produces one joint finite
permutation action on the cylinder atoms.  All actor multiplication,
cylinder covariance, and freeness estimates are simultaneous and explicit.
This is a direct target construction; it does not conjugate the supplied
normalizers to canonical lamp permutations.

## Why both observables are genuinely extra

Ordinary canonical traces do not control `(CPC1)--(CPC2)`.

- A Fourier matrix has `Col_D(F_d)=1/d` and
  `Fix_D(F_d)=1/d`.  Phase-free diagonal mass can be small while the
  unitary is maximally delocalized and far from every monomial.
- The multiplicity-one bent normalizer in
  `finite-schreier-holonomy-is-the-lamp-gauge-obstruction`
  is diagonal in its lamp-character masa.  It has
  `Col_D(U_m)=Fix_D(U_m)=1`, even though its scalar trace and every fixed
  nonidentity group trace tend to zero.  Collision localization can be
  perfect while diagonal phases hide a permutation with fixed-point
  fraction one.

Thus scalar mixed traces, even together with exact covariance and actor
products, supply neither the collision nor the phase-free condition.  These
statistics sum over the growing minimal projections of a chosen Cartan; they
are not moments of a fixed finite list of group words.

The same remains true after adjoining a fixed nonabelian basis packet.
`canonical-regular-packets-leave-an-unbounded-cartan-reservoir` proves that
canonical regular trace represents every selected simple sector as a fixed
matrix factor tensored with an unbounded multiplicity algebra.  Even an ideal
left/right pair leaves the external amplification.  The packet rigidifies
coarse atoms but supplies neither the rank-one refinement nor collision
control on the multiplicity actor.

## Exact circularity barrier

For a p.m.p. action with Connes-embeddable crossed product, suppose one could
derive such masas and `(CPC1)--(CPC2)` from every sufficiently accurate
finite Boolean crossed-product microstate, uniformly along an exhaustion.
Then `(CPC3)--(CPC6)` would give diagonal cylinder models and permutation
actor models.  Diagonalization over the finite windows is exactly a
Păunescu-sofic model of the action.

Conversely, a sofic action supplies diagonal algebras and permutation
unitaries from the outset.  For them `Col_D=1`, and the sofic trace
condition is precisely `Fix_D(U_w)->0` for every nonidentity word.
Therefore the proposed uniform Boolean crossed-product Ulam theorem is not
an independent stability lemma:

```text
CE crossed product + uniform Cartan collision extraction
        implies sofic action,                              (CPC7)
```

and, at the existential asymptotic level, the extracted data are equivalent
to the desired sofic action model.

For the Kun--Thom Bernoulli action, `(CPC7)` is exactly the missing
nonhyperlinearity implication.  Fixed finite groupoids are harmless by
`finite-lamp-targets-glue-after-action-groupoid-completion`; what is open
is producing one common growing masa with the collision and phase-free
bounds.  Assuming such a Cartan, or citing generic finite-dimensional
stability without proving these two bounds uniformly in the window, merely
restates the target.  The global route remains OPEN.

DERIVATION
cartan-collision-rounding-proof
