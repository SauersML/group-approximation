---
rg: 2
id: kernel-section-builds-relative-p13-chart
kind: claim
title: A finite quotient section turns the triangle kernel defects into a relative approximate P13 chart
distinct_from:
  summed-reynolds-cut-synchronizes-kernel-corners: that cuts the kernel energy to obtain one P0-invariant carrier; this uses the finite quotient E/N=P13 to construct all P13 multiplication cells directly and agrees exactly with the tree chart on P1 and P3 before exactification.
  km-triangle-local-bimodules-have-finite-nonflat-models: that retains a nontrivial kernel word when no kernel relation is consumed; this estimate is proportional to the actual kernel-basis defects and therefore vanishes only on the flat branch.
  gowers-hatami-finite-group-hs-stability: that exactifies an arbitrary all-pairs finite-group table; this supplies that table from the native free kernel basis with a presentation-dependent but dimension-independent constant.
  relative-finite-group-gh-cannot-fix-two-generating-subgroups: that shows finite-group exactification cannot in general preserve the exact P1 and P3 restrictions of the pre-correction table, even on a positive old support; this claim supplies exact agreement only before correction.
  three-reynolds-plus-kernel-energy-has-vanishing-gap: that shows three regular subgroup expectations plus all quotient kernel-word adjoint energies still have vanishing diagram gap on an exactly regular approximate quotient table; this construction must preserve the native rank-two coefficient maps to seek coercivity.
---

**ESTABLISHED.**  In the native triangle notation, put

```text
E=P_1 *_(P_0) P_3,          N=ker(E ->> P_13),
N=Free(n_1,...,n_r).                                      (KSP1)
```

Fix a set-theoretic section `sigma:P_13->E` which is the identity on the
embedded copies of `P_1` and `P_3`.  There is a finite constant

```text
L_sigma=max_(g,h in P_13)
 |sigma(g)sigma(h)sigma(gh)^(-1)|_(n_1,...,n_r) < infinity. (KSP2)
```

For every exact unitary representation `rho:E->U(D)`, define

```text
psi(g)=rho(sigma(g)),
d=max_a ||rho(n_a)-I||_2.                                (KSP3)
```

Then

```text
max_(g,h in P_13)||psi(g)psi(h)-psi(gh)||_2 <=L_sigma d,   (KSP4)
psi|_(P_i)=rho|_(P_i)                   (i=1,3).           (KSP5)
```

Consequently finite-group HS stability flexibly exactifies `psi` to a
genuine `P_13` representation whenever `d->0`.  If `rho` lies on the
canonical regular branch, then `tr(psi(g))->0` for every `g!=1`; the
exactified `P_13` chart therefore has a `1-o(1)` regular core.

Thus the kernel relations themselves manufacture the missing rank-two
chart, with a dimension-independent modulus and with exact pre-correction
agreement on both overlap groups.  What remains is a **relative simultaneous
exactification** problem: perturb the `P_12`, `P_23`, and newly obtained
`P_13` charts so that all three overlap restrictions agree exactly while
preserving the regular core.  An independent `P_13` chart or another
carrier-positivity argument is no longer required.

The word "relative" in the construction must not be transferred through
ordinary finite-group exactification.  The section table satisfies `(KSP5)`
before correction, but
`relative-finite-group-gh-cannot-fix-two-generating-subgroups` gives
arbitrarily accurate canonical-regular finite tables with exactly this
two-subgroup property and no nonzero joint support on which an exactification
can keep both subgroup actions literally fixed.  Thus the exactified
`P_13` chart may perturb both restrictions by `o_2(1)`.  Synchronizing those
perturbations with the other two vertex charts is the remaining native
triangle problem.

Nor is it enough to append the norms of the section cocycles to the three
overlap projection energies.  The explicit matrix in
`three-reynolds-plus-kernel-energy-has-vanishing-gap` has every abstract
ingredient of that sum and gap tending to zero.  The only surviving spectral
test is therefore the unreduced finite coefficient operator coming from the
specific `P_12,P_13,P_23` restriction maps; passing first to Reynolds
expectations and kernel-word adjoint norms discards too much information.
