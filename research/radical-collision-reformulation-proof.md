---
rg: 2
id: radical-collision-reformulation-proof
kind: route
title: Close the converse of the collision criterion and read off the excluded certificates
target: radical-collision-reformulation
requires: [sofic-radical-soficization, radical-collision-criterion]
artifacts:
  - GroupApproximation/Sofic/RadicalSeparation.lean
---

## Why sufficient

**1.**  Let `q:H->Q` with `q(x)!=1`.  Functoriality of the radical gives
`q(x) in Rad_sof(q(H))`, and it is nontrivial by hypothesis; by the
established detection statement `Rad_sof(q(H))!=1` forces `q(H)` nonsofic.
(Directly: if `q(H)` were sofic then `q` itself would be one of the
homomorphisms defining `Rad_sof(H)`, so `q(x)=1`.)

**2.**  The forward implication is the established collision criterion.
For the converse, let `Q` be a countable hyperlinear nonsofic group.  By the
detection statement `Rad_sof(Q)!=1`; choose `1!=x in Rad_sof(Q)`, take
`H=Q`, and take the identity of `Q` as the homomorphism to a hyperlinear
group.  It does not kill `x`.  Hence the two existence statements are
equivalent, and any instance of the second produces a witness for the first
whose hyperlinearity is exactly the hyperlinearity supplied as input.

**3.**  By 1 the detecting range `q(H)` is nonsofic.  Therefore it cannot lie
in any class `C` with `C ⊆ {sofic}`.  Each item of the list is such a class:

* subgroups, countable direct products, increasing unions of sofic groups,
  and locality of soficity — proved outright in
  `sofic-radical-soficization-proof` (an increasing union is covered by
  locality), so no citation is load-bearing here;
* residually finite, residually amenable, residually sofic, LEF, LEA — all
  give trivial sofic radical by the same product argument (amenable groups
  are sofic; a residually-`C` group embeds in a product of `C` groups; LEF
  and LEA groups satisfy the local approximation definition directly);
* linear over a field — a finitely generated linear group is residually
  finite (Malcev), and soficity is local, so every linear group is sofic;
* sofic-by-amenable, i.e. `1->N->E->A->1` with `N` sofic and `A` amenable —
  the amenable-extension permanence theorem, proved in Elek--Szabó,
  arXiv:math/0305352 (J. Group Theory 9 (2006)); this pin is the one recorded
  in notes/ADVERSARIAL_AUDIT_NON_MF_2026-08-13.md, which separates it from the
  survey list in the other Elek--Szabó paper.  Note the opposite order,
  amenable-by-sofic, is exactly what Kun--Thom refute, and is not excluded
  here;
* amalgams of sofic groups over an amenable subgroup, free products being
  the trivial-subgroup case — Păunescu, *On sofic actions and equivalence
  relations*, arXiv:1002.0605 (abstract: "amalgamated product of sofic groups
  over an amenable subgroup is also sofic");
* generalized wreath products of sofic groups whose underlying group action
  on a set is sofic — Gao, Kunnawalkam Elayavalli and Patchell, *Soficity
  for group actions on sets and applications*, arXiv:2401.04945, which also
  recovers Hayes--Sale for the regular action.

Each entry is a permanence theorem whose conclusion is soficity, so applying
it to sofic inputs can only ever certify a sofic group.  Since no group is
currently known to be hyperlinear and not sofic, a certificate of this shape
cannot have a hyperlinear-but-not-sofic input either: the whole family is
closed off, not merely unavailable today.

**4.**  Let `(M,tau)` be a von Neumann algebra with faithful normal tracial
state, `Phi:H->U(M)` a homomorphism with `Phi(x)!=1`, and suppose
`N=W*(Phi(H))` is Connes embeddable, i.e. there is a trace-preserving
embedding `N -> R^U`.  Then `Phi(H) <= U(N) <= U(R^U)` and `Phi(H)` is
countable, so it is hyperlinear by definition; `Phi(x)!=1` in it.  This is
the hypothesis of 2.

For the finite-coordinate form, `M_{d_n}` embeds trace preservingly into `R`,
hence `prod_U M_{d_n} <= R^U`, and the unitary group of the left side is the
normalized-Hilbert--Schmidt metric ultraproduct `prod_U U(d_n)`.  Asymptotic
representations `rho_n` therefore define a homomorphism `H -> U(R^U)`, and
`liminf ||rho_n(x)-1||_2 > 0` says exactly that `x` is not killed.  No
amplification or trace-normalization step is needed for this direction; the
tensor-power device is only required if one additionally wants the canonical
trace, i.e. `L(Phi(H))` Connes embeddable.

**5.**  A union of a chain of normal subgroups avoiding `x` avoids `x`, so
Zorn gives maximal elements `N`; in `H/N` every nontrivial normal subgroup
contains the image of `x`, so the normal closure of that image is the
monolith.  If `H` is just infinite and `N!=1`, then `H/N` is finite, hence
sofic, hence `Rad_sof(H) <= N` and `x in N`; so `N=1` is the only member and
the criterion asks for a faithful hyperlinear model.  If `H` is torsion-free
hyperbolic and nonsofic then `H` is nonelementary (elementary hyperbolic
groups are virtually cyclic, hence amenable, hence sofic).  A nontrivial
normal subgroup of a torsion-free group is infinite, and an infinite normal
subgroup of a nonelementary hyperbolic group is nonelementary — otherwise its
two-point limit set would be an invariant boundary pair, making `H`
elementary — and a nonelementary subgroup of a hyperbolic group contains a
free subgroup of rank two.

This settles the *leverage* question only.  It does not say whether a
hyperbolic nonsofic group would be hyperlinear: the mechanism behind
`nonsofic-hyperbolic-group` is local testability of expander codes in the
permutation metric, and whether it has a normalized-Hilbert--Schmidt
analogue is untouched by this argument.

## Scope

The claim measures the criterion; it does not weaken it.  What survives is
the freedom in 4 to use a *non-faithful* `Phi`: the model has to see one
word, not the whole group.  That is the only asymmetry between the collision
route and the direct problem, and it is why a partial model — for instance
one supported on a single central sign — is still worth chasing.
