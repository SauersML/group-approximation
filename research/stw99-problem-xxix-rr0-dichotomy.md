---
rg: 2
id: stw99-problem-xxix-rr0-dichotomy
kind: claim
title: Simple real rank zero C*-algebras are stably finite or purely infinite (STW Problem XXIX, Rordam's dichotomy)
root: true
distinct_from:
  stw99-problem-lxxiv-infinite-projections-purely-infinite: that asks whether a simple algebra in which every nonzero hereditary subalgebra contains an infinite projection is purely infinite without any real rank hypothesis; this asks whether real rank zero excludes the coexistence of finite and infinite projections in the first place.
artifacts:
  - research/artifacts/stw99-rr0-cluster-2026-08-30.md
---

**Problem XXIX of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Rordam, Acta 2003, Question 7.6, contrapositive form).  Is every
simple (nuclear) C\*-algebra with real rank zero either stably finite
or purely infinite?  Equivalently: can a simple nuclear RR0 algebra
contain both a finite and an infinite projection?  Open even without
nuclearity.

Known: Rordam's finite-and-infinite-projection algebra does NOT have
real rank zero (Rordam 2005); real rank zero plus the corona
factorization property gives the dichotomy (Ortega--Perera--Rordam;
Zhang unpublished); by the footnote reduction, a non-stably-finite
simple RR0 counterexample must have a hereditary subalgebra whose
projections are all finite while an infinite projection lives
elsewhere — RR0 makes "infinite projection in every hereditary
subalgebra" the exact pure-infiniteness criterion.

## Attempts

* Any counterexample fails the corona factorization property, so its
  stabilization has a full projection that is not properly infinite
  despite unbounded multiplicity room — CFP failures all come from
  Villadsen-type characteristic-class obstructions, and those
  constructions are trace-rich, pulling AGAINST real rank zero (dense
  pairing image needed): the two requirements fight over `K_0`.  In
  the Euler calculus of the LXVI arc
  (`uniformly-doubled-rordam-steps-force-proper-infiniteness`, the
  mod-`ell` Chern no-gos of the XXVII lane): Rordam's finiteness
  mechanism needs nonvanishing Euler classes of high-codimension seed
  bundles; RR0 needs enough projections to cut every self-adjoint
  spectrum, and each new projection class inserts a comparison node
  that the induced-limit Euler obstruction must dodge.  Rordam 2005
  proves his specific example fails RR0; no abstract theorem yet says
  every finite+infinite simple algebra must — that abstract question
  (does the existence of both kinds of projection force a
  non-splittable spectral element?) is the sharp open residue.
* Positive route: `stw99-xxx-implies-xxix` — Z-stability from RR0
  would settle this via Kirchberg's dichotomy.
