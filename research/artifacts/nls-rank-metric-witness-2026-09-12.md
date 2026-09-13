# The Kun--Thom 4.1 proof in normalized rank, for the Bowen--Chapman witness

Lane `nls-rank-metric-witness`, 2026-09-12. Root `non-linear-sofic-group`. Read at main
`7e05aa771`.

## 0. Question and answer

**Setting.**
* `F` is a field. `GL_n(F)` carries the normalized rank distance `rk(A - B)/n`, and
  "F-linear sofic" is in the sense of Arzhantseva--Paunescu, arXiv:1212.6780.
* The witness is `D = G *_Gamma G`, with `G = EL_3(F_2[Z^3]) semidirect EL_3(Z)` acting
  by monomial substitution and `Gamma = EL_3(F_2[N^3])`. In Lean these are
  `SymmetricDouble Ambient Peripheral` (`GroupApproximation/BowenChapman/LaurentPair.lean`).
* `D` is finitely generated, surjunctive and nonsofic
  (`bowen-chapman-witness-is-kt-double-at-q2-r3-d3`: it is the Kun--Thom double at
  `(2, 3, 3)`).
* The Lean endpoint `symmetricDouble_fg_surjunctive_not_isSofic_of_normalization`
  (`BowenChapman/EndpointOfNormalization.lean`) derives nonsoficity from
  `HasSequentialCentralizerNormalization Peripheral`. That is Kun--Thom Theorem 4.1 in
  sequential form.

**Answer.**
1. **The consumer transfers** (Section 2.1). Suppose `Gamma <= G` normalizes sequential
   rank almost-centralizers over `F`. Call this `NORM_F`. Then `D` is not `F`-linear
   sofic. So the transfer question is exactly `NORM_F` for this pair. That is one pair
   of the open rank row of `rigid-compression-defect-normalization-dichotomy`.
2. **The proof does not transfer.** (M), (C) and the metric bookkeeping transfer. The
   steps that use permutations fail for this pair:
   * **(K), in the rounding form and for linear-size pieces, and the rounding form of
     `hrep`.** These fail over every field of characteristic two, for honest
     representations of the ambient group `G` itself (Theorem B, new here). Main's
     Theorem 2.1 and 3.1 models are models of `Gamma` alone.
   * **(T1), one-piece transport.** This fails over every field for multiplicity
     decompositions (Section 2.3). The non-monomial factor comes from the actor
     `EL_3(Z)` of `G`.
   * **Other characteristics.** Over fields of odd or zero characteristic, (K) for this
     pair is open. Theorem B needs an `F`-algebra quotient of `F_2[Z^3]`.
3. **Nothing here decides `NORM_F` or the linear soficity of `D`.** `non-linear-sofic-group`
   stays OPEN.
4. **Premise corrections** (Section 3).
   * Over `C`, a rank result does not give non-hyperlinearity.
   * Exact models with exact centralizers always normalize.
5. **`D` decides a strict link** (Section 4). `D` is weakly sofic, which is already on main
   (`residually-finite-doubles-are-weakly-sofic`). Like the Kun--Thom wreath, it decides a
   strict link of `sofic <= F-linear sofic <= weakly sofic`.

**New here:**
* Theorem B;
* the far almost-centralizer;
* the binder map and the distributivity principle (Section 1);
* the Bowen--Chapman specialization of (T1).

**Not new:**
* rounding failures for models of `Gamma` alone
  (`kazhdan-rank-rounding-fails-over-every-field` and its artifacts);
* the generic (T1) failure (audit Section 3);
* the weak soficity of `D`.

## 1. Where the Lean proof uses permutations

The skeleton is `seqNormalizes_of_compressor_of_steps`
(`GroupApproximation/KunThom/CompressorNormalizationAssembly.lean`). The consumer is
`not_isSofic_symmetricDouble_of_sequentialNormalization`
(`KunThom/NormalizationFromCriterionConsumer.lean`).

| binder | step | what the permutation model supplies | rank verdict, this pair |
|---|---|---|---|
| `hdecomp`, `hdefect` | (K) | spectral gap on `l^2(Y_n)` splits the set `Y_n` into expanding `Gamma`-components with `o(N)` leakage | char 2: fails in the rounding form and for linear-size pieces (Theorem B.4); sublinear pieces open; odd and zero char open |
| `hframe` | scales | real sequences only | transfers |
| `hrep` | Kun--Thom Lemma 4.2(4) | an almost-commuting permutation almost permutes components | char 2: the rounding form fails (Theorem B.4, third item); the piecewise form needs pieces from (K) |
| `hconv` | patches almost commute | bi-invariance of the metric | transfers |
| `hmatching`, `hfunctor` | relative functor, (T1) | a permutation carries a partition to a partition | fails, every field (Section 2.3) |
| `honesided`, `hmedian`, `hcounting` | (M), (C), Lemma 4.4 | bijections preserve total size; counting vertex masses | transfer, given (K) and (T1) (audit Section 3) |
| `hhamming` | step 9 | triangle inequality and conjugation invariance | transfers |
| `hwrapper` | contradiction | metric only | transfers |

**The one permutation-specific property.** Take a partition `Y = P_1 sqcup ... sqcup P_r`.
* Every subset `S` is the disjoint union of its traces `S cap P_j`.
* A permutation carries partitions to partitions.

The subspace lattice is not distributive. A subspace `W` need not equal
`sum_j (W cap P_j)`, and an invertible matrix can carry a decomposition to pieces that
meet the old pieces diagonally. Every failing row uses this property, and no
transferring row does.

## 2. The steps in rank for the Bowen--Chapman pair

### 2.1 The consumer transfers

* **The metric.** Normalized rank is a bi-invariant length on `GL_n(F)`:
  `rk(AB - 1) <= rk(A - 1) + rk(B - 1)` and `rk(CAC^-1 - 1) = rk(A - 1)`.
  * `not_isSofic_freeLamp_of_sequentialNormalization` uses two facts:
    `hamming_conj_commute_vanishing` and `not_hamming_vanishing_of_ne`. Both hold with
    rank in place of Hamming distance.
  * The second needs `rk(sigma_n(g) - 1)/n` bounded below for `g != 1`. That is part of
    the definition of an `F`-linear sofic approximation.
* **The lamp group.** `D' = G *_Gamma (Gamma x C_2)` contains `D` as the index-two kernel
  of its retraction onto `C_2` (`not_isSofic_symmetricDouble_of_not_isSofic_freeLamp_flip`).
  * `F`-linear soficity passes from `D` to `D'` by induction along a transversal
    `{1, s}`.
  * `Ind phi(x)` is block-monomial with two nonzero blocks, so its multiplicative
    defect is at most the sum of two block defects.
  * `rk(Ind phi(x) - 1)` is at least `rk(phi(x) - 1)` for `x` in `D`, and at least `n`
    for `x` outside `D`.
* **The defect.** The flip `k` commutes with `Gamma`. If `gamma in Gamma` and
  `t^-1 gamma t notin Gamma`, then `[t k t^-1, gamma] != 1` (`lampWitness_ne_one`).
* **Conclusion.** `NORM_F` for `Gamma <= G` makes `D'`, and hence `D`, not `F`-linear
  sofic. Here `NORM_F` quantifies over `F`-linear sofic approximations of `G`, which is
  what restricting an approximation of `D'` gives.
* **The other branch.** By the rank row of the dichotomy, a failure of `NORM_F` gives an
  `F`-linear sofic group with a nontrivial rigid defect on the image pair. That group is
  nonsofic by `sofic-groups-kill-rigid-compression-defects`. So `NORM_F` for this pair is
  a win--win: this root at `F`, or Question 8.5 at `F`.

### 2.2 (M) and (C)

Section 3 of `research/artifacts/rank-row-compression-audit-2026-09-12.md` proves both in
rank. Dimension counting replaces vertex counting, and two independent transported pieces
cannot both fill more than half of one target. Nothing here is specific to the pair.

### 2.3 (T1) fails for the Bowen--Chapman compressors, over every field

* **The actor representation.** Let `B : G -> EL_3(Z) -> GL_3(F)` be the natural
  representation of the actor, reduced to the prime field. Then
  `Gamma <= EL_3(F_2[Z^3]) <= ker B`.
* **Elementary actor matrices are compressors.**
  * A nonnegative integer matrix maps `N^3` into `N^3`, so each `e_ij(1)` in `EL_3(Z)`
    maps `F_2[N^3]` into itself.
  * `e_12(1)` is strict: its inverse sends `x_2` to `x_1^-1 x_2`.
* **The model.** Take any honest `F`-representation `U` of `G` and put `V = U (x) F^3`,
  with `g` acting as `rho_U(g) (x) B(g)`. `Gamma` acts as `rho_U (x) 1`, so every
  `U (x) L` with `L <= F^3` is `Gamma`-invariant. When `rho_U|Gamma` is absolutely
  irreducible, these are all the invariant subspaces.

**Claim.** Let `F^3 = L_1 (+) ... (+) L_r` with `r >= 2` and every `L_k != 0`. Some
`t = e_ij(1)` and some `k` have `B(t) L_k` inside no `L_j`.

*Proof.*
* **Pieces into pieces forces a permutation.** Suppose each `B(t)` maps every `L_k` into
  some `L_j`. The images are independent, so the dimensions sent into `L_j` total at most
  `dim L_j`. Both totals are `3`, so equality holds everywhere, no `L_j` is missed, and
  `B(t)` permutes `{L_k}`.
* **The permutation is trivial.** `H = <B(e_ij(1))>` is perfect, since
  `e_ij(1) = [e_ik(1), e_kj(1)]`. Its image in `Sym(r)` with `r <= 3` is perfect and
  solvable, hence trivial. So every `L_k` is `H`-invariant.
* **Contradiction.** `H` acts irreducibly on `F^3`. If `v` is in `L` with `v_j != 0`, then
  `(B(e_ij(1)) - 1) v = v_j e_i`, so `L` contains every `e_i` with `i != j`, and then
  `e_j = (B(e_ji(1)) - 1) e_i`. So `L_k = F^3`, contradicting `r >= 2`. QED

**Effect.** The transported piece `U (x) B(t) L_k` has at least `dim U = n/3` dimensions
outside every piece `U (x) L_j`, so it lies almost inside no piece at linear scale. This
is the audit's diagonal-transport example, with the non-monomial factor supplied by the
actor of `G`.

### 2.4 Theorem B: (K) and `hrep` fail for honest ambient models in characteristic two

**Setting.**
* `F` has characteristic two, `N >= 7` is odd, `m = (N-1)/2`, `A = F[(Z/N)^3]` and
  `n = 3N^3`.
* `rho_N : G -> GL(A^3)` is given by `(a, M) . u = abar sigmabar_M(u)`: reduce exponents
  modulo `N`, then substitute by `M mod N`. This is the action of
  `residuallyFinite_semidirectProduct_of_expSubst`
  (`BowenChapman/ResiduallyFiniteSubstitution.lean`), extended from `F_2` to `F`. It is a
  homomorphism.
* `S = { e_ij(1), e_ij(x_l) : i != j, l = 1, 2, 3 }` generates `Gamma`, because
  `e_ij(f + g) = e_ij(f) e_ij(g)` and `e_ij(fg) = [e_ik(f), e_kj(g)]` for distinct
  `i, j, k`.
* `B_m = span{ x^v : v in [0,m)^3 } <= A` and `W = B_m^3`. Let `pi_B` be the coordinate
  projection onto `B_m` along the other monomials, and `p = 1_3 (x) pi_B`.
* `b_S(X) = sum_(s in S) (dim(X + sX) - dim X)`, and
  `d(X, Y) = dim X + dim Y - 2 dim(X cap Y)`.

**Theorem B.**
1. `b_S(W) <= 18 m^2 <= 1.5 n/N`, and `rk[p, rho_N(s)] <= 2 m^2` for `s` in `S`.
2. Every `rho_N(Gamma)`-invariant subspace `U` has `d(W, U) > n/64 - 3`.
3. `rk(p - z) > n/64 - 3` for every `z` in the commutant of `rho_N(Gamma)`.
4. Consequences.
   * **No rounding modulus.** Restrictions to `Gamma` of honest `F`-representations of
     `G` have `(1.5/N) n`-almost-invariant subspaces at distance more than `n/64 - 3`
     from every invariant subspace.
   * **Linear-size pieces do not expand.** Fix `c, kappa > 0`. For large `N`, no subspace
     `P` with `dim P >= c n` and `b_S(P) = o(n)` is internally `kappa`-expanding for
     `rho_N|Gamma`, in the sense of the counterexample artifact, Section 3.
   * **Centralizers do not round.** In the rank ultraproduct, `[p_N]` is a sequential
     almost-centralizer of `sigma(Gamma)` at normalized rank distance at least `1/64`
     from the exact commutants `rho_N(Gamma)'`.
     * Unit form: `1 + (lambda - 1) p` for `|F| > 2`, at distance at least `1/64`.
     * Over `F_2`, use `[[1, p], [0, 1]]` on `rho_N (+) rho_N`, at distance at least
       `1/128`.
   * **Faithful approximations.** Let `L_N` be the regular representation of a finite
     quotient of `G`, amplified to dimension in `(n/2, n]`. Then `rho_N (+) L_N` is an
     `F`-linear sofic approximation of `G` by honest representations. In it, `W (+) 0`
     has boundary at most `1.5 n/N` and normalized distance at least `1/128 - o(1)` from
     every invariant subspace.

**Lemma B1 (invariant subspaces and commutant).**
* The `F`-span of `rho_N(Gamma)` is `M_3(A)`.
  * `rho_N(e_ij(f)) - 1 = E_ij (x) fbar`, and `F_2[N^3] -> A` is onto since
    `x_l^-1 = x_l^(N-1)`.
  * The products `E_ij E_ji` give the diagonal units.
* So the invariant subspaces are the `M_3(A)`-submodules of `A^3`. These are `I^3` for the
  ideal `I = { a : a e_1 in U }`, by Morita.
* The commutant is `End_(M_3(A))(A^3) = 1_3 (x) A`, the multiplication operators.

**Lemma B2 (uncertainty).** Let `I` be an ideal of `A` with
`dim(B_m cap I) >= m^3 - c` and `c + 1 <= N^3/64`. Then `dim I > N^3/4`.

*Proof.*
* **A small support.** Put `s = ceil((c+1)^(1/3))`, so `s - 1 < N/4` and `s <= m`.
  A cube `Q` in `[0,m)^3` of side `s` has at least `c + 1` points. So `B_m cap I` meets
  `F^Q` nontrivially, and there is `f != 0` in `I` supported on `Q`.
* **Characters.** `N` is odd, so `Fbar[(Z/N)^3]` is `Fbar^(N^3)` through the `N^3`
  characters `chi`, and `dim fA = #{ chi : chi(f) != 0 }`.
* **Counting zeros.** After translating `Q` to `[0,s)^3`, `chi(f) = zeta^(v_0) P(zeta)`,
  with `P != 0` of degree `< s` in each variable and `zeta` in `mu_N^3`.
  * A nonzero polynomial in `d` variables with degree at most `s - 1` in each vanishes
    at no more than `d (s-1) N^(d-1)` points of `mu_N^d`.
  * Proof by induction on `d`: pick a nonzero coefficient `Q_j` of a power of `y_1` and
    split on whether `Q_j` vanishes.
* **Conclusion.** `dim I >= dim fA >= N^3 - 3(s-1) N^2 > N^3/4`. QED

**Proof of Theorem B.**
1. **Boundary and commutator.**
   * `e_ij(1)` preserves `W` and commutes with `p`.
   * For `s = e_ij(x_l)`, `sW` lies in `W` plus `x_l B_m`, which adds the `m^2` monomials
     of one face.
   * `[p, s] = E_ij (x) [pi_B, x_l]`, which is supported on the `2m^2` monomials `x^v`
     with exactly one of `v` and `v + e_l` in `[0,m)^3`.
   * There are 18 such `s`, and `18 m^2 <= 4.5 N^2 = 1.5 n/N`.
2. **Distance.** Write `U = I^3` (Lemma B1), so `d(W, U) = 3 d(B_m, I)`. Put
   `c = m^3 - dim(B_m cap I)`.
   * If `c + 1 > N^3/64`, then `d(B_m, I) >= c > N^3/64 - 1`.
   * Otherwise Lemma B2 gives `d(B_m, I) >= dim I - dim B_m > N^3/4 - N^3/8`.
3. **Commutant.** Write `z = 1_3 (x) a`, so `rk(p - z) = 3 rk(pi_B - a)`.
   * `B_m` lies in `aA + im(pi_B - a)`, so `dim(B_m cap aA) >= m^3 - rk(pi_B - a)`.
   * If `rk(pi_B - a) <= N^3/64 - 1`, Lemma B2 gives `rk a > N^3/4`.
   * But `rk a <= m^3 + rk(pi_B - a) < N^3/8 + N^3/64`, a contradiction.
4. **Consequences.**
   * **No rounding modulus.** This is items 1 and 2.
   * **Linear-size pieces.** Use the chain `W_j = B_j^3`, `0 <= j <= N`.
     * Steps have dimension at most `9 N^2`, and `b_S(W_j) <= 18 N^2`.
     * Boundaries are subadditive on intersections:
       `(X cap Y) + s(X cap Y) <= (X + sX) cap (Y + sY)`, so
       `b_S(X cap Y) <= b_S(X) + b_S(Y)`.
     * Choose `j` with `dim(P cap W_j)` in `(p/2 - 9N^2, p/2]`.
     * Internal expansion then gives `kappa (p/2 - 9N^2) <= b_S(P) + 18 N^2 = o(n)`,
       which is false for large `N`.
   * **Centralizers.** The commutator rank is subadditive along words, so item 1 gives
     vanishing for every `gamma`. Item 3 gives the distance.
     * The unit forms reduce to item 3: an exact commutant element close to them puts
       `p` close to `1_3 (x) A`, or to an off-diagonal entry of `M_2(1_3 (x) A)`.
   * **Faithful approximations.** `G` is residually finite (`ambient_residuallyFinite`),
     so it has finite quotients with injectivity radius tending to infinity.
     * A regular representation has `rk(g - 1) >= |Q|/2` for `g != 1` in `Q`.
     * Amplify to dimension in `(n/2, n]`. The sum has dimension at most `2n` and
       `rk(g - 1) > n/4` eventually for each `g != 1`.
     * For an invariant `U`, let `U_0 = U cap (A^3 (+) 0)` and let `U_1` be the
       projection of `U` to `A^3`. Both are `rho_N(Gamma)`-invariant, `U_0 <= U_1` and
       `(W (+) 0) cap U = (W cap U_0) (+) 0`.
     * So `d(W (+) 0, U) >= dim W + dim U_1 - 2 dim(W cap U_0) >= d(W, U_0) > n/64 - 3`.
       QED

**Remarks.**
* **Mechanism.** `B_m` is a Folner box for the translation action of `Z^3` on
  monomials, so almost invariance costs only its boundary. Invariant subspaces are
  ideals, that is sums of character eigenspaces, and a Folner box is far from every such
  sum: that is the uncertainty principle on `(Z/N)^3`. In the Hamming row, a set is the
  union of its traces on the pieces, so this cannot happen there.
* **Relation to main.** `kazhdan-group-rank-models-admit-no-expander-decomposition` gives
  models of `EL_3(F_2[t])` and, through `x_l -> alpha`, of the Theorem E subgroup. A
  transcribed `hdecomp` consumes approximations of the ambient `G`, and nobody has shown
  those models extend. Theorem B uses the congruence quotients that the Lean
  residual-finiteness proof already uses.
* **No defect here.** `rho_N(t) p rho_N(t)^-1 = 1_3 (x) pi_(M B_m)`. The parallelepiped
  `M B_m` is again Folner, and `e_12(1)` does not wrap it modulo `N`, so the conjugate
  still almost commutes with `rho_N(Gamma)`. These models are consistent with `NORM_F`.
* **Scope.**
  * Theorem B covers linear-size pieces only.
  * `rho_N|Gamma` is reducible, with one exactly invariant summand per Galois orbit of
    characters. So the irreducibility bound behind part 1 of main's Theorem 3.1 is
    unavailable, and sublinear expander decompositions are not excluded.
* **Odd and zero characteristic.** `F_2[Z^3]` has no ring map to an `F`-algebra, and the
  unipotents `e_ij(1)` become semisimple involutions. Theorem B has nothing to act on.

## 3. Premise corrections

* **Over `C`.** `linear-sofic-nonsofic-group` records that "no implication between
  hyperlinear and linear sofic is known in either direction". The metric-scope artifact
  finds none stated by Arzhantseva--Paunescu.
  * So "`D` not `C`-linear sofic" would not make `D` non-hyperlinear, and it does not
    overlap the `non-hyperlinear-group` chain.
  * Conversely, hyperlinearity of `D` (lane `q34-bc-witness-hyperlinear`) says nothing
    about `C`-linear soficity.
  * The rank row and the Hilbert--Schmidt row are separate rows of the dichotomy.
* **Exact models normalize.** Let `rho : G -> GL_n(F)` be honest with `n` fixed, and let
  `z` commute exactly with `rho(Gamma)`.
  * `H = <rho(G), z>` is a finitely generated linear group, so it is residually finite
    by Malcev, hence sofic.
  * `rho(Gamma) <= rho(G)` is an infranormal Kazhdan pair: quotients of Kazhdan groups
    are Kazhdan, and images of compressors are compressors.
  * `sofic-groups-kill-rigid-compression-defects` gives
    `[rho(g) z rho(g)^-1, rho(gamma)] = 1`.
  * So `NORM_F` can fail only through centralizers that are approximate in rank with
    `n -> infinity`, like `p_N` in Theorem B.

## 4. Where `D` sits

* **Weak soficity is on main.** `residually-finite-doubles-are-weakly-sofic` proves every
  double of a residually finite group weakly sofic.
  * The fold kernel is free.
  * Glebsky's permanence theorem (Rev. Mat. Iberoam. 39 (2023), Theorem 1.1) applies.
  * `G` is residually finite (`ambient_residuallyFinite`).
* **The strict link.** `D` is weakly sofic and nonsofic. So, as for the wreath in
  `sofic-linear-weakly-sofic-chain-has-a-strict-link`, `D` decides the strict link at
  every `F`:
  * if `D` is `F`-linear sofic, it answers Question 8.5 at `F`;
  * if not, it gives this root at `F`.

  No new node: this is the chain node's argument with `D` in place of `W`.
* **Method consequence.** No argument through non-weak-soficity can close this root with
  `D`.

## 5. What stays open

* `NORM_F` for the Bowen--Chapman pair, over any field. This is a win--win (Section 2.1).
* Step (K) for this pair in odd and zero characteristic.
* Expander decompositions of `rho_N|Gamma` with pieces of sublinear dimension.
* Whether `D` is `F`-linear sofic, for any `F`.

## 6. Graph

* **Obstruction.** `bowen-chapman-ambient-rank-models-do-not-round-peripheral` is
  ESTABLISHED, through `bowen-chapman-ambient-rank-models-do-not-round-peripheral-proof`.
* **Dead route.** It invalidates `non-linear-sofic-via-bowen-chapman-rank-transcription`:
  the step-by-step transcription into `F`-rank in characteristic two, with its rounding
  steps.
* **Root.** `non-linear-sofic-group` gets one Attempts bullet.
