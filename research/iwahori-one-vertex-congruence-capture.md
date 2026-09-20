---
rg: 2
id: iwahori-one-vertex-congruence-capture
kind: claim
title: A vertex of an almost compatible Iwahori pair is close to a congruence representation
distinct_from:
  iwahori-local-global-defect-question: that asks for a compatible pair near every almost compatible pair; this asks only that the first vertex, a single exact SL_2(Z) representation, be near some congruence representation of any level. By iwahori-congruence-capture-transfers-across-one-edge the two are equivalent, but this names the one object a proof must control.
  dv-distance-is-defect-plus-congruence-capture: that reduces the question to capture of the whole pair by congruence pairs (DCC3); this is capture of one vertex, which transfers to the pair.
  regular-iwahori-relative-congruence-exactification: that asks to move a regular pair into the congruence locus on the regular branch; this asks, on every branch, only about one vertex.
  modular-vertex-extension-does-not-force-congruence: that shows one-sided extendibility through a vertex does not force congruence; this asks whether two-sided commensurated extendibility does.
---

**OPEN.** Notation is as in `iwahori-congruence-capture-transfers-across-one-edge`.

> For every sequence of exact pairs `pi_n = (pi_(n,+), pi_(n,-))` in
> `X_FD(SL_2(Z) * SL_2(Z))` with `def(pi_n) -> 0`, we have `A_+(pi_n) -> 0`.
> That is, `pi_(n,+)` is at generalized HS distance `o(1)` from exact
> representations of `SL_2(Z)` that factor through congruence quotients of
> any level, with any dimensions.

**Intrinsic form.** Let `alpha` be an exact representation of `SL_2(Z)`.
Suppose the transported restriction `alpha o sigma^(-1)` on `Gamma^0(2)` is
`epsilon`-close, on generators, to the restriction of some exact
representation of `SL_2(Z)`. Must `alpha` then be `f(epsilon)`-close to
congruence? This is "almost extendibility through the commensurator element
`t` forces congruence". One-sided extendibility through a vertex does not
force it (`modular-vertex-extension-does-not-force-congruence`).

**Status in the graph.**

- By `iwahori-congruence-capture-transfers-across-one-edge` this claim is
  equivalent to Dogon--Vigdorovich Question 1.4
  (`iwahori-local-global-defect-question`), and the route
  `iwahori-question-from-one-vertex-congruence-capture` records the forward
  direction.
- A refutation needs almost compatible pairs whose first vertex stays
  uniformly far from all congruence representations. By the same transfer, the
  second vertex must then also stay far.

## Attempts

- **2026-09-17 (swarm-0917, stability-approximation).** Isolating one vertex
  from the pair. The transfer theorem shows that the pair repair and the
  second-vertex capture add no difficulty once one vertex is captured. The
  whole content of Question 1.4 is therefore this single-vertex statement.

  The natural next attack is Selberg `(tau)` applied to `pi_+` itself. It fails
  as stated, because `pi_+` need not factor through any finite quotient, and
  `(tau)` gives no gap for representations of `SL_2(Z)` with infinite image.
  So the missing input is genuinely non-congruence: some mechanism must show
  that almost `t`-transportability excludes positive-mass infinite-image
  constituents.

  The known infinite-image examples of
  `modular-vertex-extension-does-not-force-congruence` do not decide this. Their
  vertex representation is only extended on one side, and no bound on its
  `t`-transported defect is recorded. Open.

- **2026-09-19 (swarm-0917, operator-algebras).** Decomposition and a class
  kill.
  * **Decomposition.** The route
    `iwahori-capture-from-finite-image-and-finite-image-congruence` splits
    this claim into (FI) `iwahori-vertex-finite-image-capture`, which removes
    infinite-image mass, and (NC)
    `iwahori-finite-image-vertex-congruence-capture`, which handles
    non-congruence finite quotients. The two halves are equivalent to this
    claim together, by the Step 6 replacement argument.
  * **Class kill.** `iwahori-bounded-dimensional-vertex-constituents-are-congruence`
    (proof through the new import `peterson-thom-sl2-s-integer-character-rigidity`)
    shows that constituents of bounded dimension are asymptotically
    congruence. So every countersequence to this claim, to (FI) or to (NC)
    carries its gap on irreducible constituents of dimension tending to
    infinity. This kills fixed small non-congruence representations, their
    amplifications and mixtures, and bounded-degree non-congruence
    quotients. The invariant is the mass of the Peterson--Thom restricted
    character on the type-I non-congruence part, which is zero. Bounded
    dimension enters through the weight `1/D` and a polynomial identity.
  * **Dead: NC implies a nonsofic vertex action.** Trying to feed an (NC)
    countersequence into the codense-`(tau)` coset argument fails. That
    argument needs Hamming correction of the chart labels. HS-closeness does
    not see the chart-label block vectors: `||XL||_HS <= ||X||_HS ||L||_op`
    with `||L||_op^2` of order `|V|/|B|`, so an `o(1)` HS error can move
    every label.
  * **Dead: uniform `(tau)` for (NC).** Recorded in the Attempts of (NC).
