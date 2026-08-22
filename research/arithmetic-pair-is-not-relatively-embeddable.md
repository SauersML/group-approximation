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

- **Exact-face confinement at `n = 3` (from the lifting lane,
  2026-08-21).**  `kazhdan-subgroup-weak-ucp-exactifies-microstates`
  applies to candidate refuters of this claim, not only to HNN
  microstates: given `(pi_k, B_k)` witnessing `RE/C`, the corner
  transport `W_k` of that theorem carries `B_k` to the subalgebra
  `W_k B_k W_k^* + C(1 - W_k W_k^*)`, preserves near-containment of the
  now GENUINE congruence representation `rho_k = pi'_k|_(SL_3(Z))`, and
  preserves `E_(B_k)(pi_k(a)) -> 0` (conditional expectations transport
  along the algebra identification, and all changes are pointwise
  HS-small).  So under `sl3-z-weakly-ucp-stable` this claim need only be
  refuted on the `Lambda`-exact face, where
  `at-op62-holds-for-representation-lifts` gives the commutant of
  `rho_k(SL_3(Z))` levelwise and the double-coset orthogonality form of
  faithfulness becomes a statement about finite-level isotypic blocks.
  (For `n = 2` the subgroup lacks full (T) and this confinement is not
  available.)

- **Congruence models fail `(CF1)` maximally.**  Co-density puts
  `pi_k(a)` inside `W^*(pi_k(C))` for every `a`, so `||E(pi_k(a))||_2 = 1`.
  Any faithful sequence is exotic, i.e. far from every congruence
  representation, which is the same sector the stability and Iwahori lanes
  cannot control (`sl2-half-stability-excludes-hnn-hyperlinearity`).
- **Amplification does not help.**  Tensoring `pi_k` with `1_m` leaves
  `E_(W^*(pi_k(C)) (x) 1)(pi_k(a) (x) 1) = E(pi_k(a)) (x) 1` unchanged, and
  tensoring with a finite-quotient representation keeps co-density.  A
  faithful sequence needs genuinely new microstates of the host.
- **Gao's converse is now checked for the rank-three plain double.**
  Appendix Theorem 7.1 requires the coefficient `N_1` to be a finite factor
  and, for the plain double, a unitary `u in L(A)` with
  `E_(L(C))(u^n)=0` for all `n!=0`.  For `SL_3`, `L(C)` is a CE II_1 factor
  and `u=lambda(diag(2,1,1/2))` satisfies the power condition.  Therefore
  `sl3-arithmetic-double-hyperlinear-iff-relative-embeddable` proves that
  CE of `L(A)*_(L(C))L(A)` is EQUIVALENT to `RE/L(C)`.  The exact weakest
  rank-three hole is now split out as
  `sl3-arithmetic-inclusion-is-not-re-over-lattice`.  The same literal
  specialization with `N_1=L(SL_2(Z))` is unavailable because that group
  factor is not a factor (the center contains `+-I`); no rank-two conclusion
  is asserted here.
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
- **Bimodule form of faithfulness (both pairs).**  Write `B = prod_omega B_k`
  and `K = L^2(B) (-) L^2(L(C))`, a nonzero left `L(C)`-module (`B` is
  non-separable while `L(C)` is separable, so `B != L(C)`).  The commuting
  square makes `u_a (x) b -> u_a b` an isometry
  `L^2(L(A)) (x)_(L(C)) K -> L^2(M)`, so the left `A`-module `L^2(M)`
  contains the induced representation `Ind_C^A(kappa)`, `kappa` the left
  `C`-action on `K`; by Mackey its restriction to `C` is
  `kappa (+) (+)_(CaC != C) Ind_(C cap aCa^-1)^C(kappa^a)` with all
  inducing subgroups of finite index (`A` commensurates `C`).  In the
  basic construction `<M, e_B>` the projections `u_a e_B u_a^*`, `aC in A/C`,
  are orthogonal with `Tr = 1` and are permuted by `Ad u_A`, an exact copy
  of `l^2(A/C)` inside the conjugation representation of `A` on
  `L^2(<M, e_B>, Tr)` with base vector `e_B` commuting with `L(C)`.
  Property (T) of `A` or `C` yields no contradiction here by itself: the
  left action of `A` on `L^2(M)` has no invariant vectors (regular trace)
  hence a spectral gap, and `l^2(A/C)` has the `C`-fixed vector `delta_C`
  but no `A`-fixed vector, exactly as these copies do.  What must be used
  is that `B` is an ultraproduct of coordinate subalgebras: the copies of
  `K` and of `l^2(A/C)` are coordinatewise objects, and the double-coset
  translates `pi_k(a) B_k` must be asymptotically orthogonal subspaces of
  `L^2(M_(d_k))` of dimension `dim B_k`, so `dim B_k / d_k^2 -> 0`.
- **What property (T) buys for `n = 3`.**  `W^*(pi_k(C))'` is the exact
  coordinate commutant of the microstate image, and by Peterson's
  interchange formula the ultraproduct of these commutants is
  `L(C)' cap M`; faithfulness `(CF1)` with `B_k = W^*(pi_k(C))` says the
  coset images are orthogonal to the bicommutant of the `C`-image in each
  coordinate.  No mechanism is known that forces a positive overlap.
