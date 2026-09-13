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
  - research/artifacts/stw29-projection-monoid-dichotomy-audit-2026-08-30.md
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
* The projection-monoid obstruction is now exact
  (`stw29-projection-qq-characterizes-rr0-dichotomy`).  For a simple RR0
  algebra the desired dichotomy is equivalent to projection-level `(QQ)`:
  if `nx` is properly infinite in `V(A)`, then `x` is properly infinite.
  Indeed one infinite projection is properly infinite and simplicity makes
  a finite multiple of every nonzero projection properly infinite; `(QQ)`
  reflects this back to the projection itself, and RR0 then gives pure
  infiniteness.  In particular, almost unperforation of `V(A)` settles
  XXIX.  Every counterexample must contain a finite `q` and `n` with `nq`
  properly infinite, hence the explicit compact-order almost-perforation
  witness `(n+1)(2q)<=nq` but `2q not <=q`.
* Literature state, verified from the sources on 2026-09-12.
  `opr-cfp-rr0-dichotomy` (OPR Corollary 5.16) is the CFP theorem, routed
  here as `stw29-via-rr0-corona-factorization` from the open claim
  `rr0-simple-algebras-have-corona-factorization`.
  `rordam-mixed-examples-not-real-rank-zero` gives the mechanism of Rordam
  2005: the Euler certificate survives Villadsen transversality on generic zero
  sets, and his examples have property (SP).
  `opr-mixed-simple-refinement-monoid` shows that refinement, simplicity and
  weak divisibility of `V(A)` cannot force `(QQ)`, so a proof needs analytic
  input.
* Level-two normal form (`stw29-counterexample-level-two-fingerprint`).
  XXIX fails iff some unital simple real-rank-zero `C` is finite while `M_2(C)`
  is infinite.  Such a `C` has an orthogonal sequence `e_i` with
  `1 direct_sum 1 <~ e_i direct_sum e_i`, no quasitrace, and infinite stable
  rank.  Its monoid carries the separativity failure `x = [1]`, `y = [1] + r`.
  So a counterexample is a simple non-separative exchange ring with wild `V`,
  and it would answer the Ara--Goodearl--O'Meara--Pardo separativity problem
  negatively.  Rordam's non-RR0 example already has this normal form
  (Acta 2003, page 20: `Q direct_sum Q ~ 1` and `M_2(QBQ) = B`).
* Positive classes (`stw29-separative-projection-monoid-dichotomy`).
  The dichotomy holds for every simple algebra with (SP) and separative
  `V(A)`: tame `V(A)`, or inductive limits of separative building blocks with
  arbitrary connecting maps.
* Weaker premises routed here.  `stw29-via-finite-simple-rr0-weak-cancellation`
  needs weak cancellation only for finite simple real-rank-zero algebras
  (implied by LX(1)), and stable rank one of those algebras suffices
  (`finite-simple-rr0-algebras-have-stable-rank-one`, Rordam's 2005 open
  question).
* Crossed-product firewall (unreviewed).
  `coinvariant-tarski-lemma-simple-dimension-groups` forces `(QQ)` in the
  `K_0` type semigroup of any group action on a state-ordered, dense simple
  `K_0`.  Hence `simple-coefficient-crossed-products-dichotomy`: crossed
  products of simple exact real-rank-zero stable-rank-one coefficients (e.g.
  simple AF) by properly outer actions of any countable group are
  dichotomous, which removes Rainone's almost-unperforation hypothesis
  (`rainone-type-semigroup-crossed-product-dichotomy`).
  `simple-af-integer-crossed-products-dichotomy` covers non-unital AF
  coefficients over `Z`.  So a mixed crossed product needs coefficients whose
  finiteness obstruction is invisible to a dense state-ordered `K_0`.  This
  matches Rordam's `D rtimes Z`, whose coefficient algebra is non-simple and
  carries Euler data.
* Non-simple zero-dimensional coefficients (unreviewed).
  * `coinvariant-tarski-lemma-minimal-nowhere-scattered` extends the lemma to
    minimal actions on dimension groups whose positive elements divide with
    order-small remainders.  The margin comes from minimality, and the division
    error is controlled in the order, with no states.
  * `K_0` of an AF algebra has this property iff the algebra has no elementary
    subquotient (`af-k0-order-divisible-iff-no-elementary-subquotient`).
  * Hence the dichotomy holds for unital AF coefficients and any countable
    group (`nowhere-scattered-af-crossed-products-dichotomy`), and for
    non-unital AF coefficients and `Z`
    (`nowhere-scattered-af-integer-crossed-products-dichotomy`).
  * `af-crossed-product-counterexample-normal-form` records what
    a zero-dimensional crossed-product counterexample must still have: an
    elementary subquotient, a non-amenable group, and a non-separative
    coefficient type semigroup with a finite class that has a paradoxical
    multiple.
  * The design is `stw29-mixed-rr0-af-crossed-product-exists`.  Its commutative
    core is `measure-free-minimal-cantor-action-with-finite-clopen-type`, a
    sharpened form of Rainone's page-33 question.
  * The dichotomy holds beyond AF: for exact real-rank-zero stable-rank-one
    coefficients with unperforated `K_0` and no integer layer
    (`rr0-sr1-coefficient-crossed-products-dichotomy`,
    `dimension-group-divisible-iff-no-integer-subquotient`).
  * In the Cantor regime, a normal infinite cyclic or locally finite subgroup
    acting minimally smooths `K_0` enough for the lemma
    (`smoothing-normal-subgroup-cantor-dichotomy`).
  * The remaining commutative rounding problem reads as a continuous
    sourceless-orientation problem, the standard separator of Borel from
    clopen combinatorics.
