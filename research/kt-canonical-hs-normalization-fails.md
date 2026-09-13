---
rg: 2
id: kt-canonical-hs-normalization-fails
kind: claim
title: Some Connes-embeddable model of the Kun--Thom actor, with any trace, has a non-normalized Gamma-commutant
invalidates: [kt-pair-non-hyperlinear-commutant]
distinct_from:
  kt-centralizer-normalization-hs: that is the universal normalization statement over all trace-preserving representations; this is the negation of its Connes-embeddable instance, with no trace condition, and any such counterexample answers Question 3.4.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**OPEN.**  For the Kun--Thom Theorem E pair `Gamma < G`, there exist a
Connes-embeddable finite tracial algebra `M` and a homomorphism
`sigma: G -> U(M)`, with no condition on `tau o sigma` and `sigma` not necessarily injective, such that

```text
R = sigma(Gamma)' cap M   is not normalized by sigma(G).
```

**Stakes: this is a fork between the two program goals.**
- If established, `hyperlinear-nonsofic-from-canonical-hs-normalization-failure`
  produces a hyperlinear nonsofic binary coset wreath and answers Pestov 3.4.
  It also refutes `kt-centralizer-normalization-hs`, killing
  `kt-pair-non-hyperlinear-commutant`.
- Its negation, the canonical instance of `kt-centralizer-normalization-hs`,
  already proves the Kun--Thom wreath non-hyperlinear.

The claim is equivalent to hyperlinearity of `W_K` for some `K` with
`Gamma <= K <= G`, `N = <<Gamma>>_G` not in `K`.
- Forward direction: the route below.
- Converse: a hyperlinear `W_K` gives, through relative embeddability, a
  canonical model whose `K`-lamp lies in `R` and whose commutation stabilizer
  is `K`.  Normalization would force `N <= K`.

It is strictly weaker than hyperlinearity of `W = W_Gamma`, since any
intermediate `K` suffices.

## Attempts

- **Finite and profinite models.** Dead.  A profinitely closed `K >= Gamma`
  contains `N` (`infranormal-compact-closure-normal`), so separable
  intermediate subgroups never qualify.
- **Sofic-action permanence for `G action G/K`.** Dead for every qualifying
  `K`.  Kun--Thom Theorem C applies to `Gamma <= G` regardless of `K`, and the
  coordinate at the coset `K` is `Gamma`-invariant but not `G`-invariant, so
  the Bernoulli action over `G/K` is never sofic.
- **One-compressor subgroups `K = <Gamma,t>`.** Qualify (`N` is not in
  `<Gamma,t>`) and are not Kazhdan, but the action is still nonsofic by the
  previous item.  A model must be native, e.g. extend the one-compressor
  permutation model of `<Gamma,t>` to all of `G` inside a II_1 envelope.
- **Atomic commutants.** Dead.  Any compressor acts as an automorphism on the
  discrete type I summand of `R`
  (`trace-preserving-endomorphism-fixes-discrete-type-i-summand`), and on the
  finite-dimensional isotypic part of `sigma|Gamma`
  (`fd-isotypic-part-of-a-kazhdan-image-carries-no-wall`).  A witness needs a
  diffuse summand of `R` on which `Ad sigma(t)^*` is a proper trace-preserving
  endomorphism.  The model shape is the one-sided Bernoulli shift: in the lamp
  model of `W`, the lamps at the cosets `t^(-k) Gamma`, `k >= 0`, span such a
  summand, and `Ad sigma(t)^*` shifts `k -> k+1`.
- **Fell models and Haagerup coefficients.** Dead as a source of walls.
  `fell-models-inherit-walls-from-coefficients` (q34-free) shows a canonical
  Fell model `lambda (tensor) pi` has a wall exactly when its coefficient `pi`
  does, because `Gamma` is icc.  `kt-fell-models-over-haagerup-coefficients-are-wall-free`
  and `haagerup-targets-carry-no-relative-wall` exclude coefficients with
  Haagerup `pi(Gamma)''`.  A witness therefore needs a coefficient with
  non-Haagerup `pi(Gamma)''`, or a canonical model that is not of Fell type.
- **Genuine vertex coordinates.** Dead, conditional only on the recorded
  premises (lane `ex-q34-kt-double`, 2026-09-12). By
  `kt-regular-congruence-mask-removes-trace-faithfulness-from-the-commutant-wall`,
  a witness may be taken trace-preserving. For a trace-preserving `sigma` whose
  restriction to `Gamma` flexibly rounds (hypothesis (H1) of
  `hs-stable-vertex-rounding-for-every-model`, at this one `sigma`), four
  established per-model claims give normalization of `R`:
  `nonunit-projection-bounded-by-root-spectral-mass`,
  `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`,
  `vertex-rounding-deep-nonunit-root-mass-vanishes` (these three make the
  rounding unit-type) and `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`.
  Each has a review record among the 2026-09-12 review artifacts. So every
  witness is a trace-preserving model of `G` whose restriction to
  `Gamma = EL_r(F_q[x_1..x_d])` is a `G`-extendable asymptotic representation
  that is **not** flexibly Hilbert--Schmidt close to genuine representations.
  Such representations are not known to exist for any infinite higher-rank
  Kazhdan group (compare Dogon arXiv:2211.10492), so the positive branch of this
  claim contains a flexible-instability theorem for `Gamma` at `G`-extendable
  models. Aspect-ratio cascades over genuine vertex coordinates, the natural
  Hilbert-hotel witness, are excluded by the same chain.
- **Popa's second independence case.** Popa, arXiv:1308.3982 (abstract, read on
  MSI 2026-09-12), proves relative free independence in two cases. The first is
  the amenable-centralizer case recorded in
  `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`. The second is
  `Q = prod_omega Q_n` with `Q_n <= M_n` and `Q_n` not intertwining into
  `Q_n' cap M_n` for every `n`: then for every separable
  `X <= M (-) (Q' cap M)` some diffuse abelian subalgebra of `Q` is free from `X`
  relative to `Q' cap M`.
  - For matrix coordinates the non-intertwining hypothesis never holds, since
    finite-dimensional subalgebras always intertwine through minimal
    projections.
  - With II_1 coordinates `M_n = R` it holds for genuine vertex coordinates:
    `sigma_n(Gamma)''` is atomic in the Haagerup algebra `R`, and its diffuse
    commutant does not intertwine into it.
  - The relative freeness is over `P = Q' cap M`, not over `L(Gamma)`. It gives the
    amalgamated-free Haar letter of the centralizer HNN group only if
    `E_P = E_(L(Gamma))` on `L(G)`, a commuting square that already forces
    commutation stabilizer exactly `Gamma`.
  - Any model meeting it has genuine vertex coordinates. The rounding chain of the
    previous item is established for matrix ultraproducts. Whether its per-model
    claims transfer to II_1-coordinate ultraproducts, where multiplicities are
    continuous, was not checked. If they transfer, this lever is dead for the
    Theorem E pair.
