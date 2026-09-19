---
rg: 2
id: manzoor-relator-quotient-has-infinitely-generated-isotropy
kind: claim
title: Factoring Manzoor's forced relators leaves infinitely generated random isotropy unless the group problem is already solved
distinct_from:
  manzoor-natural-subgroup-subshift-is-not-a-haar-envelope: that observes the forced normal subgroup lies in almost every stabilizer and uses it to distinguish subgroup from normalizer; this factors the IRS and its GNS algebra through the resulting finitely presented quotient and determines the residual stabilizers' generation properties.
  ergodic-nonce-irs-fg-support-is-terminal: that treats finite generation of the original random subgroup for an arbitrary ergodic non-CE IRS; this proves the stronger source-specific statement after quotienting all finitely many forced strategy relators.
  atomic-noncohyperlinear-irs-forces-nonhyperlinear: that turns an already supplied atom into a group-factor witness; this proves that finite generation of the residual Manzoor subgroup, a finite-index forced core, or a nontrivial finitely generated normal core would supply such an atom.
---

Let `F` be the finite-rank free group on the strategy generators in the
Manzoor/ZPC construction.  Let `R_str` be the finite structural relator set

```text
u^2, J^2, [u,J], and [u,v] for u,v in one question,
```

and put

```text
N=normalClosure_F(R_str),        Q=F/N.                  (MFR1)
```

Let `mu` be an ergodic perfect strategy IRS whose character `chi_mu` has
non-Connes-embeddable GNS algebra, and write `H~mu`.  Then:

1. `N<=H` almost surely.  Hence `H |-> H/N` defines an ergodic IRS
   `bar(mu)` on the finitely presented group `Q`.
2. `chi_mu` factors through `Q`, and the GNS algebra of the quotient IRS
   character is exactly the original non-CE GNS algebra.
3. `N` has infinite index in `F`; equivalently, `Q` is infinite.  Moreover
   `N` is nontrivial, finitely normally generated, but infinitely generated
   as an abstract subgroup of `F`.
4. Either a countable non-hyperlinear group already exists, or

   ```text
   H/N is infinitely generated for bar(mu)-almost every H/N. (MFR2)
   ```

5. In the same unresolved branch, the deterministic IRS core

   ```text
   C_mu={g in F:chi_mu(g)=1}                              (MFR3)
   ```

   is an infinite-index, infinitely generated normal subgroup containing
   `N`.  No nontrivial finitely generated normal subgroup `K normal F` can
   satisfy `Pr(K<=H)>0`.

Thus the explicit structural relations do give a useful exact reduction: the
non-CE IRS already lives on one concrete finitely presented quotient `Q`, and
the central involution `bar(J)` survives because `Pr(J in H)=0`.  But they do
not give a finite-index normal closure, a finitely generated core, or an
atomic quotient.  Any one of those strengthenings would already trigger
`atomic-noncohyperlinear-irs-forces-nonhyperlinear`; absent that endpoint,
all residual randomness remains supported on infinitely generated subgroups
of `Q`.

The theorem uses only the structural probability-one constraints preserved
by the perfect ZPC witness and the later ergodic non-CE choice.  It does not
assert that the existentially selected game or IRS has a computable cylinder
law.
