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
- **On the `Lambda`-exact face the one-unitary system is explicit, and
  perfectness kills its scalar part (`n = 3`).**  Take `pi_k|_C = rho_k`
  exact, factoring through `Q = SL_3(Z/m_k)`, and `H = pi_k(h)`.  The
  element `h-bar = diag(2, 1, 1/2) mod m_k` lies in `Q`, so
  `H_0 = rho_k(h-bar) in rho_k(C) subset B_k` intertwines
  `rho_k(C_0) -> rho_k(C_1)` exactly; `X = H_0^* H` almost commutes with the
  genuine finite image `rho_k(C_0)`, and property (T) of `C_0` (finite
  index in `SL_3(Z)`) puts `X` within `O(defect)` of a unitary
  `X' in rho_k(C_0)' = (lambda(Q_0) (x) 1)'`.  Since `B_k` is a
  `B_k`-bimodule and `H_0 in B_k`, `E_(B_k)(H) = H_0 E_(B_k)(X')`, so
  faithfulness at `h` is exactly `E_(B_k)(X') -> 0` with `X'` in the
  `C_0`-isotypic commutant.  If `X' = 1 (x) Y` (scalar on each isotypic
  block, `Y` in the multiplicity algebra), every relator `r` of a finite
  presentation of `A` evaluates to `lambda(r-bar) (x) Y^(e(r)) = 1 (x) Y^(e(r))`,
  `e(r)` the `h`-exponent sum; `SL_3(Z[1/2])` is perfect, so the `e(r)`
  have gcd `1`, and approximate satisfaction of finitely many relators
  forces `Y ~ 1` (Bezout), hence `H ~ H_0 in B_k`: unfaithful.  (Exactly:
  no homomorphism `A -> Q x Z/e` has nontrivial second factor.)  What
  survives is the non-scalar part `X' = (+)_sigma X'_sigma` over the
  `Q_0`-isotypic blocks, nearly orthogonal to `lambda(Q) (x) 1`, with the
  relators of `A` approximately satisfied while the `C`-part is frozen at
  `rho_k`; conjugation by `lambda(q)`, `q notin Q_0`, moves the blocks
  between the `Q_0`- and `qQ_0q^-1`-isotypic decompositions.  Exact
  solutions of this system are unfaithful (they are congruence
  representations of `A` by the congruence subgroup property), so the
  `n = 3` hole on the exact face is the STABILITY of this one-unitary
  system: approximate solutions near exact ones.  This is the finite-level
  bookkeeping the previous bullet names, stated as a single equation.
- **Cocycle form of the exact-face system (`n = 3`).**  Let
  `rho-tilde : A -> U(d)` be the congruence representation extending
  `rho` (`rho-tilde(g) = rho(g-bar)`, `g-bar in Q`), and put
  `c(g) = pi(g) rho-tilde(g)^(-1)`.  Then `c|_C = 1` and `c` is an
  approximate 1-cocycle for the action `Ad rho-tilde` of `A` on `U(d)`,
  which factors through the finite group `Q`:
  `c(g g') ~ c(g) rho-tilde(g) c(g') rho-tilde(g)^(-1)`, with defect the
  presentation defect of `pi`.  An exact cocycle with `c|_C = 1` gives an
  exact representation `c . rho-tilde` of `A` extending `rho`, which is
  congruence, so `c = 1` when `rho = lambda_Q (x) 1_m` (co-density pins
  the quotient).  Hence on the exact face, faithfulness fails as soon as
  approximate `U(d)`-valued 1-cocycles of `A` for finite-quotient actions,
  trivial on `C`, are uniformly (in `d`) close to exact ones.  The
  linearisation is the additive cocycle problem for the conjugation
  representation `Ad rho-tilde` on `M_d`, where property (T) of `A` gives
  a uniform spectral gap; the nonlinear remainder is the same obstacle the
  Newton iteration of `iwahori-newton-closes-near-sector` controls only
  inside fixed torsion-multiplicity strata.  So the exact-face hole is a
  relative (to `C`) normalized-HS cocycle-stability statement for
  `SL_3(Z[1/2])`, with the action through a finite quotient — narrower
  than `sl3-z-weakly-ucp-stable` in two ways (the subgroup is exact, the
  action is finite) and the precise remaining content of this claim at
  `n = 3` under that stability hypothesis.

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
- **Ruled out: "regular trace forces regular type" (do not retry).**  It is
  tempting to close the whole `Lambda`-exact face at `n = 3` at once: an
  `RE/C` witness has the regular trace of `A` (Gao's embedding is
  trace-preserving on the group factor), hence the regular trace `delta_e`
  on `C`, and on a genuine congruence tower `sigma_m = (+)_rho rho^(m_rho)`
  the normalized trace is `sum_rho (m_rho dim rho / d)(chi_rho/dim rho)`; if
  this forced the Plancherel weights `m_rho propto dim rho` (regular type),
  `lambda-exact-face-of-the-collapse-closes` would finish both the coprime
  and `p`-power faces and, with the confinement, close the claim under
  `sl3-z-weakly-ucp-stable`.  It does NOT: pointwise convergence of the
  weighted character sum to `delta_e` does not force the weights to
  Plancherel (many non-Plancherel weight sequences have weighted character
  sums tending to `delta_e`), exactly the scope limitation recorded in
  `lambda-exact-face-of-the-collapse-closes` (Step 2) and the failure of
  `fixed-shift-invariance-does-not-force-flat-profile`.  So the residual
  after the coprime closure `sl3-re-lambda-exact-coprime-face-is-unfaithful`
  and the regular-type `p`-power closure is genuinely the NON-regular-type
  `p`-primary `Lambda`-exact towers (plus the weak-ucp outliers), the same
  live enemy as `(RC3)`; regular trace does not shortcut it.
- **What property (T) buys for `n = 3`.**  `W^*(pi_k(C))'` is the exact
  coordinate commutant of the microstate image, and by Peterson's
  interchange formula the ultraproduct of these commutants is
  `L(C)' cap M`; faithfulness `(CF1)` with `B_k = W^*(pi_k(C))` says the
  coset images are orthogonal to the bicommutant of the `C`-image in each
  coordinate.  No mechanism is known that forces a positive overlap.
- **Correction (2026-08-21 audit): the coprime closure is CONDITIONAL.**
  `sl3-re-lambda-exact-coprime-face-is-unfaithful` has been demoted to
  OPEN: its step `pi(h) = V' in pi(Lambda)''` is false
  (`congruence-slot-escapes-ultraproduct-lambda-algebra` -- regular
  representations of `SL_3(Z/n_m)` at coprime levels have `W = 1` on the
  nose and `E_(pi(Lambda)'')(pi(h)) = 0`).  What is proved is the
  logarithmic-rate form: no matrix-form `RE/C` witness is `Lambda`-exact of
  coprime type with `eps_k log n_k -> 0` (`eps_k` the generator
  near-containment defect, `n_k` the level; subadditivity of
  `dist_2(. , B_k)` plus `(tau)`-expander diameter).  So the residual
  enemy sector on this face ALSO contains coprime-level `Lambda`-exact
  witnesses whose near-containment decays slower than `1 / log n_k`, in
  addition to the non-regular-type `p`-primary towers and the outliers
  described above; the sentence "after the coprime closure" above should
  be read with that hypothesis.  Separately, the title of this claim
  ("with respect to ANY Connes-embeddable algebra") is stronger than the
  three `N_1 = C` forms in the body: `RE/C` implies `RE/N_1` for every
  `N_1`, not conversely.
- **Correction (2026-08-21 audit): the exactification transport of `B_k` is
  not an algebra as written.**  The bullet above transports `B_k` to
  `W_k B_k W_k^* + C(1 - W_k W_k^*)`; with `q_k = W_k^* W_k` only
  `||.||_2`-close to `1`, products `W_k b W_k^* . W_k b' W_k^* = W_k b q_k b' W_k^*`
  leave that set unless `q_k` commutes with `B_k`, so the "transported
  conditional expectation" is undefined and the preservation of `(CF1)`
  under `kazhdan-subgroup-weak-ucp-exactifies-microstates` is UNPROVED (the
  theorem itself and its route never mention `B_k`; it also confines only to
  the `Lambda`-exact face, not to the coprime face, and is conditional on
  the OPEN `sl3-z-weakly-ucp-stable`).  A repaired transport must replace
  the set by an honest von Neumann algebra (e.g. the algebra generated by
  `W_k B_k W_k^*`, or the corner `q_k B_k q_k` on `ran q_k`) and prove the
  `o(1)` defect of its expectation against `pi_k(a)`; until then the
  "confinement to the `Lambda`-exact face" of `RE/C` witnesses is a
  conjecture, and the residual description above should be read as
  conditional on it.
