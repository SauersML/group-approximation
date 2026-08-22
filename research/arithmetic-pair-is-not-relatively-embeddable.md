---
rg: 2
id: arithmetic-pair-is-not-relatively-embeddable
kind: claim
title: The lattice factor inclusions L(SL2(Z)) in L(SL2(Z[1/2])) and L(SL3(Z)) in L(SL3(Z[1/2])) are not relatively embeddable with respect to any Connes-embeddable algebra
distinct_from:
  relatively-embeddable-pair-makes-the-hnn-group-hyperlinear: that is the established implication from relative embeddability to hyperlinearity of the HNN group; this is the OPEN negative statement for the two arithmetic pairs that the lane needs, a necessary condition for both weakest holes.
  non-ce-twisted-group-factor-exists: that asks for a non-Connes-embeddable twisted group factor; this asserts a non-embeddability property of an inclusion of two Connes-embeddable group factors, Gao's relative embeddability, and produces no new factor.
  sl2-hnn-admits-no-amalgamated-free-haar-unitary: that is equivalent to non-hyperlinearity of the SL2 HNN group; this is a consequence of it, phrased purely in terms of microstates of the host with no stable letter, and is what a refuter would attack first.
---

OPEN.  For `(A, C) = (SL_2(Z[1/2]), SL_2(Z))` and `(SL_3(Z[1/2]), SL_3(Z))`,
the inclusion `L(C) subset L(A)` is not `RE/C` (Gao, arXiv:2012.07940,
Def. 1.1 with `N_1 = C`).  Three equivalent forms:

1. (matrix form) there is no regular-trace microstate sequence
   `pi_k : A -> U(d_k)` with subalgebras `B_k subset M_(d_k)` satisfying
   `(CF1)` of `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`:
   every sequence keeps, for some `a notin C`, a uniformly positive
   component of `pi_k(a)` inside any subalgebra nearly containing
   `pi_k(C)`;
2. (group form, Gao Theorem 7.1) the explicit finitely presented group
   `D^+ = (A x Z) *_C A` is not hyperlinear;
3. (factor form) `(L(A) (x) L(Z)) *_(L(C)) L(A)` is not Connes embeddable.

This is the WEAKEST statement in the HNN lane and it closes the goal
directly with witness `D^+` (`non-hyperlinear-from-non-relative-embeddability`):
non-hyperlinearity of the HNN group `G_2` (resp. `G_3`) implies it, since
`G subset D^+`, through `non-relative-embeddability-from-sl2-exclusion`
(resp. `-sl3-`), while nothing weaker than it makes `D^+` a witness.  Its
other value is as the lane's cheapest falsification target: a
`C`-faithful microstate sequence of the host is a construction on the
host alone, with no stable letter, and would make `D^+`, hence every
group in this lane, hyperlinear.

## Attempts

- **Congruence models fail `(CF1)` maximally.**  Co-density puts
  `pi_k(a)` inside `W^*(pi_k(C))` for every `a`, so `||E(pi_k(a))||_2 = 1`.
  Any faithful sequence is exotic, i.e. far from every congruence
  representation, which is the same sector the stability and Iwahori lanes
  cannot control (`sl2-half-stability-excludes-hnn-hyperlinearity`).
- **Amplification does not help.**  Tensoring `pi_k` with `1_m` leaves
  `E_(W^*(pi_k(C)) (x) 1)(pi_k(a) (x) 1) = E(pi_k(a)) (x) 1` unchanged, and
  tensoring with a finite-quotient representation keeps co-density.  A
  faithful sequence needs genuinely new microstates of the host.
- **Gao's converse.**  The appendix of arXiv:2012.07940 proves, under extra
  assumptions or after enlarging the amalgam, that embeddability of the
  star amalgam implies relative embeddability; if that converse applies to
  `L(C) subset L(A)`, this claim is EQUIVALENT to the weakest holes rather
  than merely implied by them, and the whole lane becomes a statement
  about microstates of the host.  Not yet checked against the appendix's
  exact hypotheses.
- **Amalgam picture for `n = 2` (Serre): three exclusions.**  Since
  `A = C *_(C_0) C'` with `C' = hCh^-1`, `C_0 = C cap C'` of index three,
  a microstate of `A` is a pair of representations `sigma` (of `C`) and
  `rho` (of `C`, transported to `C'` by `Ad h`) with
  `rho|_(C_(-1)) ~ (sigma o Ad h)|_(C_(-1))` on generators of
  `C_(-1) = h^-1 C_0 h`, and `C`-faithfulness asks `rho(c)` to be nearly
  orthogonal to `W^*(sigma(C))` for `c notin C_(-1)`.
  (i) *Exact edge agreement is congruence.*  If the two restrictions agree
  exactly, `(sigma, rho)` is an exact finite-dimensional representation of
  `A`, hence of finite image and congruence (Margulis superrigidity for
  the rank-two S-arithmetic lattice plus Serre's congruence subgroup
  property), so `rho(C) subset W^*(sigma(C))` by co-density: maximally
  unfaithful.  (ii) *Finite-quotient restrictions glue only exactly.*  If
  both restrictions to `C_(-1)` are regular representations of finite
  quotients `C_(-1)/K`, `C_(-1)/K'` (with multiplicity), approximate
  unitary equivalence forces the shared irreducible content, of weight
  `1/[KK':K]`, to tend to full weight, hence `K = K'` for large index —
  exact agreement, and (i) applies.  (iii) *Irreducible restrictions are
  useless.*  If `sigma` is irreducible, or more generally
  `W^*(sigma(C))` has dimension comparable to `d^2`, no unitary is nearly
  orthogonal to it.  So a faithful sequence needs `sigma` highly reducible
  with large multiplicities and non-congruence irreducible constituents,
  and `rho` an approximate extension of `(sigma o Ad h)|_(C_(-1))` whose
  `C`-part escapes the algebra generated by `sigma(C)`: an "approximate
  congruence subgroup property" would exclude it, and that is the
  flexible-stability content of `iwahori-local-global-defect-question`
  in different clothes.
- **What property (T) buys for `n = 3`.**  `W^*(pi_k(C))'` is the exact
  coordinate commutant of the microstate image, and by Peterson's
  interchange formula the ultraproduct of these commutants is
  `L(C)' cap M`; faithfulness `(CF1)` with `B_k = W^*(pi_k(C))` says the
  coset images are orthogonal to the bicommutant of the `C`-image in each
  coordinate.  No mechanism is known that forces a positive overlap.
