---
rg: 2
id: amenable-traces-on-exact-cstar-algebras-are-quasidiagonal
kind: claim
title: Amenable traces on exact C*-algebras are quasidiagonal (the exact residual of STW Problem X(1))
root: true
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: that is the universal statement over all C*-algebras, refuted by the literal group's full group algebra; this is the exact-algebra case that STW single out as the substantive residual and that the group-algebra refutation provably cannot reach.
  stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal: that assumes nuclearity and a faithful trace and concludes quasidiagonality of the algebra; this assumes only exactness, allows every amenable trace, and concludes quasidiagonality of the trace.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks whether the unique trace of the nonexact algebra R is quasidiagonal; this asks about exact algebras, and it implies only the exact-subalgebra part of X(2).
  tww-gabe-schafhauser-af-embedding-theorem: that is the established UCT theorem; this is the trace statement that its UCT-free form would settle, and it is open exactly where the UCT is absent.
  stw10-homotopy-domination-preserves-amenable-qd: that is a permanence theorem transporting the property between homotopy-dominated exact algebras; this is the universal question over the whole exact class.
artifacts:
  - research/artifacts/stw10-x1-exact-residual-2026-09-05.md
---

Let `A` be an exact C\*-algebra and `tau` an amenable tracial state on `A`
(Brown: there are u.c.p. maps `phi_n : A -> M_(k_n)` with
`||phi_n(ab)-phi_n(a)phi_n(b)||_2 -> 0` and `tr o phi_n -> tau`).  Then
`tau` is quasidiagonal: the maps can be chosen asymptotically multiplicative
in operator norm.

**OPEN.**  This is the case of STW Problem X(1) that survives the refutation
`stw99-problem-x1-fails-on-full-group-algebras`.  The verbatim problem, its
surrounding discussion and footnotes 25 and 26 are pinned in the artifact.
STW: "for exact C\*-algebras, Problem X(1) can be reduced to the case of
faithful traces ... It follows that if Theorem 11 holds without the UCT, then
Problem X holds for exact C\*-algebras."

## Reductions in hand

- **Separable.** An amenable non-QD trace restricts to an amenable non-QD
  trace on a separable unital subalgebra
  (`directed-unions-preserve-trace-approximations`), and subalgebras of exact
  algebras are exact.
- **Faithful.** For exact `A` the GNS quotient `A -> pi_tau(A)` is locally
  liftable (Effros--Haagerup), so amenability descends
  (`amenable-trace-descends-through-locally-liftable-quotient`), and
  quasidiagonality of the induced faithful trace pulls back by composition
  with the quotient map.  So it suffices to treat faithful amenable traces
  on separable exact algebras.
- **Injective GNS closure.** For exact `A` a trace is amenable if and only if
  `pi_tau(A)''` is injective (Brown, Corollary 4.3.4, via Connes and
  Kirchberg's local reflexivity of exact algebras; STW footnote 25).  So the
  question is exactly: is every faithful trace with hyperfinite GNS closure
  on a separable exact C\*-algebra quasidiagonal?
- **AF-embedding form.** Route `exact-x1-via-uct-free-trace-extending-af-embedding`:
  the UCT-free, trace-extending form of Theorem 11
  (`exact-faithful-amenable-trace-extends-to-af-embedding`) implies this
  claim, because every trace on an AF algebra is quasidiagonal and
  quasidiagonality of traces passes to subalgebras and pulls back along
  quotients.  This is STW's footnote 26 made into a route.

## Why the group-algebra refutation stops here

The refutation of the universal X(1) uses the full group algebra `C*(E)` of
the literal group, which is not exact (`E` is not amenable).  No exact
algebra can be reached from it: if `A` is any exact quotient of `C*(E)`
through which `tau_E` factors, then `pi_tau(A) = pi_(tau_E)(C*(E))` is the
reduced algebra `C*_r(E)`, whose GNS closure is `L(E)`, which is not
injective.  By the injective-GNS characterisation the induced trace is not
amenable on `A`.  More generally a full group algebra `C*(G)` is exact only
when `G` is amenable, and then it is nuclear and satisfies the UCT (Tu), so
all its amenable traces are quasidiagonal (Tikuisis--White--Winter, Gabe).
Hence every candidate counterexample to this claim must be built away from
group C\*-algebras and away from the UCT class.

## Relation to X(2)

If this claim holds, then for every separable exact `S` inside the
hyperfinite II1 factor `R` the restriction of `tau_R` is quasidiagonal,
because that restriction is faithful with injective GNS closure.  This is the
exact-subalgebra half of X(2); the converse is not automatic, since
quasidiagonality of the algebra `pi_tau(A)` does not by itself make the trace
quasidiagonal.

## Attempts

- Known positive classes: separable exact UCT algebras with a faithful
  amenable trace (`tww-gabe-schafhauser-af-embedding-theorem`); cones and
  contractible algebras (`stw10-contractible-algebras-have-qd-amenable-traces`);
  algebras homotopy dominated by a positive case
  (`stw10-homotopy-domination-preserves-amenable-qd`); full group algebras of
  Kazhdan groups (`stw10-kazhdan-full-group-traces-are-qd`).
- Nothing else is recorded.  A counterexample needs a separable exact,
  non-UCT (or at least not known-UCT) algebra with a faithful trace whose GNS
  closure is hyperfinite but which admits no operator-norm multiplicative
  matrix models; equivalently, by the route above, a failure of UCT-free
  trace-extending AF-embeddability.
