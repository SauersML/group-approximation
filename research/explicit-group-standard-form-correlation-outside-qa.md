---
rg: 2
id: explicit-group-standard-form-correlation-outside-qa
kind: claim
title: Some finitely presented group carries, in the standard form of its group von Neumann algebra, a finite correlation outside C_qa
distinct_from:
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for an exact model of the synchronous algebra of `B_*` in a corner of a group factor; this asks only for one finite correlation outside `C_qa` from projection-valued measures in `L(Lambda)` and `L(Lambda)'` with an arbitrary vector. For perfect synchronous correlations the two coincide by `standard-form-group-separation-collapses-to-corner-model`; for non-synchronous or imperfect correlations this is formally weaker.
  lin-pzk-tableau-rational-qc-not-qa-correlation: that supplies an explicit correlation in `C_qc \ C_qa` on an unspecified tracial host; this asks for any such correlation on a group host in standard form.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the Paddock--Slofstra equivalence for binary linear systems, where every model uses group elements and the canonical trace; this places no group-element, trace, or synchrony condition on the witness.
---

OPEN. Find a finitely presented group `Lambda`, finite sets `X,Y,A,B`,
projection-valued measures `{P_(x,a)}_a` in `L(Lambda)` and `{Q_(y,b)}_b` in
`L(Lambda)'`, and a unit vector `xi in l^2(Lambda)`, such that

```text
p(a,b|x,y) = <P_(x,a) Q_(y,b) xi, xi>  is not in  C_qa(X,Y,A,B).     (GSQ1)
```

By `ce-standard-form-strategies-are-quantum-approximable`, any such
`Lambda` is non-hyperlinear (route
`non-hyperlinear-from-group-standard-form-correlation`). A certificate of
`(GSQ1)` can be a Bell functional `beta` with a rational bound `c` such that
`beta(q) <= c` for all `q in C_qa`, together with `beta(p) > c`. The known
upper bounds on `C_qa` of this kind come from MIP* = RE soundness, as in
`lin-pzk-tableau-rational-qc-not-qa-correlation`.

## Prerequisites and where they can fail

1. **(Game side, available.)** There is an explicit Bell functional with
   `sup_(C_qc) > sup_(C_qa)`: `p_tab` of
   `lin-pzk-tableau-rational-qc-not-qa-correlation`.
2. **(Host side, open.)** The witness must live in `L(Lambda)` and its
   commutant. Nothing is required of the vector, and Bob's projections need
   not be group elements, spectral projections of group elements, or
   related to the trace.
3. **(Presentation, open.)** `Lambda` must be finitely presented, or at least
   explicit, which is the goal's standard of explicitness.

## Attempts

- **Perfect synchronous witnesses (2026-09-17, swarm-0917-w4-nh-decomp-new).**
  Every realization of a perfect synchronous correlation in this standard
  form is a corner model of the game algebra
  (`standard-form-group-separation-collapses-to-corner-model`).
  - For `p_tab`, prerequisite 2 is therefore exactly the corner-model problem
    `A(B_tab) -> z L(Lambda) z`, the tableau analogue of
    `non-ru-bcs-is-satisfiable-in-a-group-factor`.
  - The relaxation dies at `(SC1)`, where synchrony forces
    `P_(x,a) xi = Q_(x,a) xi`.
  - What survives are witnesses that are non-synchronous or imperfect, where
    no algebraic relation holds on the support of `xi`.
- **Open sub-question recorded, not attacked.**
  - Does every non-hyperlinear `Lambda` admit a `(GSQ1)` witness? If so, this
    claim is equivalent to the goal for finitely presented groups.
  - The natural input is the synchronous Kim--Paulsen--Schafhauser
    separation theorem. Its proof has not been checked for whether the
    witnessing projections can be taken inside a prescribed non-embeddable
    host. No verbatim citation has been imported, so this remains unverified.
- **Equivalence with the goal (2026-09-17, swarm-0917-w5-nh-decomp-new).**
  - `standard-form-qa-witness-iff-nonhyperlinear-group` proves that this
    claim, as an existence statement, is equivalent to the existence of a
    finitely presented non-hyperlinear group.
  - A witness can always be taken perfect synchronous: on the solution group
    of a Paddock--Slofstra tracial/non-`R^U` linear system, in the central
    corner `z = (1-lambda(J))/2`, with `xi = sqrt(2) z delta_e`.
  - So as a matter of existence, the non-synchronous and imperfect witnesses
    this claim was left open for add no leverage over
    `lcs-tracial-ru-gap-equiv-nonhyperlinear`. What is left is explicitness,
    together with the prescribed-host question below.
- **Prescribed host, naive argument (2026-09-17, swarm-0917-w5-nh-decomp-new).
  Dies at one step.**
  - Question: for a *given* non-hyperlinear `Lambda`, is there a witness in
    `L(Lambda)` itself?
  - Take `xi = delta_e` and `Q = J P J`. Then `<P JQJ delta_e, delta_e> = tau(PQ)`.
    Approximate the generating unitaries `lambda(s)` in norm by finite-spectrum
    unitaries `sum_a omega_a E_(s,a)`.
  - Non-hyperlinearity then forces some finite family `E` whose generated
    algebra is not `R^U`-embeddable.
  - **Where it dies.** The step "`W*(E)` is not embeddable, hence
    `p_E(a,b|x,y) = tau(E_(x,a)E_(y,b))` is not in `C_qa`" is false as stated.
    Membership of a synchronous `p` in `C_qa` needs only *some* amenable trace
    on `C*(Z_A^(*X))` with the same degree-2 moments. `p_E` does not see
    products of the `E`'s, and the relations among them are not perfect game
    rules.
  - **What would repair it.** An encoding of word moments into degree-2
    moments by perfect synchronous rules, placed inside `M_k(L(Lambda))`,
    which is a central summand of `L(Lambda x S_(k+1))`.
    - For solution groups the encoding is available: the context rules of
      Step 3 of `standard-form-qa-witness-iff-nonhyperlinear-group-proof`.
    - For a general `Lambda` it would need a group-level analogue of the
      linearization in the Kavruk--Paulsen--Todorov--Tomforde operator-system
      reduction. That has not been imported or proved.
