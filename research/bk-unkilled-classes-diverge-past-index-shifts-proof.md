---
rg: 2
id: bk-unkilled-classes-diverge-past-index-shifts-proof
kind: route
title: Split exhaustion values additively into almost-invariant blocks, compare Cuntz pairs by the index of a pair, and make case-2 positivity uniform on a finite window
target: bk-unkilled-classes-diverge-past-index-shifts
requires:
  - stw07-unkilled-classes-are-model-one-signed
  - stw07-trace-invisible-classes-carry-hahn-banach
---

# Proof: unkilled classes diverge along exhaustions and strongly convergent sequences; Cuntz-pair twists shift by constants

Lane `stw99-problem-vii-blackadar-kirchberg`, obstruction-miner sw-045, 2026-09-17.

## 0. Setting and conventions

`A` is separable, unital and quasidiagonal. `pi: A -> B(H)` is a unital
representation that is *faithful and essential*: `pi` is injective and
`pi(A) cap K(H) = 0`. Then the composite `A -> B(H) -> Q(H)` is injective, hence
isometric:

(0.1) `||pi(a) + K|| = ||a||` for all `a in A`.

A *model* is a sequence of u.c.p. maps `phi_n: A -> M_(k_n)` (`k_n >= 1`) with
`||phi_n(ab) - phi_n(a)phi_n(b)|| -> 0`. It is *faithful* if
`liminf ||phi_n(a)|| = ||a||` for all `a`. For a projection `p in M_m(A)`, put
`T_n = (phi_n tensor id_m)(p)`. The *defect* is `||T_n^2 - T_n|| -> 0`. Once
the defect is `delta < 1/8`, the spectrum of `T_n` lies in
`[-2delta, 2delta] cup [1-2delta, 1+2delta]`. Put
`r_n(p) = rank chi_[1/2, inf)(T_n)`, and for `x = [p]-[q]` put
`v_n(x) = r_n(p) - r_n(q)`. The eventual value is independent of the
representatives. This is the convention of
`stw07-unkilled-classes-are-model-one-signed`: equivalent projections have
approximately equivalent compressions, and adding `1_j` to both `p` and `q`
adds the same rank to both. We use that trichotomy.

- (Case 1) some faithful model has value `0` infinitely often ("`x` is killed");
- (Case 2) every model is eventually `>= 0`, and every faithful model is eventually `> 0`;
- (Case 3) the mirror image of Case 2.

A *QD exhaustion* of `pi` is a sequence of finite-rank projections
`P_1 <= P_2 <= ...` with `P_n -> 1` strongly and `||[P_n, pi(a)]|| -> 0` for all
`a`. The compressions `phi_n = P_n pi(.) P_n : A -> B(P_n H)` form a model, since
`P_n pi(a) P_n pi(b) P_n - P_n pi(ab) P_n = -P_n pi(a)(1-P_n) pi(b) P_n` has norm
at most `||a|| ||[P_n, pi(b)]||`. The model is faithful, because
`||P_n pi(a) P_n|| -> ||pi(a)||` as `P_n -> 1` strongly. Its values are denoted
`v_n(x)`, with `k_n = rank P_n`. Amplifications `pi tensor id_m` and
`P_n tensor 1_m` are used silently.

**Rank lemma (R).** Let `S, S'` be self-adjoint operators on a finite-dimensional
space with defects `<= delta` and `||S - S'|| <= eta`, where `2delta + eta < 1/4`.
Then `rank chi_[1/2,inf)(S) = rank chi_[1/2,inf)(S')`.

*Proof.* By Weyl's inequality, `|lambda_j(S) - lambda_j(S')| <= eta` for the
ordered eigenvalues. Every eigenvalue of `S` is within `2delta` of `{0, 1}`, so
the eigenvalues of `S'` with the same index lie within `2delta + eta < 1/4` of
the same point of `{0,1}`. Hence the number of eigenvalues `>= 1/2` agrees. ∎

## 1. Additivity along an exhaustion

Fix `p in M_m(A)` and write `R = (pi tensor id_m)(p)` and
`eps_n = ||[P_n, R]||`, which tends to `0`. Since `P_n` is monotone, for `N < n`
put `E = P_n - P_N`. It is a projection, and `||[E, R]|| <= eps_n + eps_N`.

**Lemma 1.** For `N < n`, with `T_n = P_n R P_n` on `P_nH`, `T_N = P_N R P_N` on
`P_NH` and `U = E R E` on `EH`, we have `||T_n - (T_N ⊕ U)|| <= 2 eps_N`. So if
`2(eps_n + eps_N) + 2 eps_N < 1/4`, then
`r_n(p) = r_N(p) + rank chi_[1/2,inf)(U)`.

*Proof.* `P_n = P_N + E`, so `T_n = T_N + U + P_N R E + E R P_N`. Also
`P_N R E = P_N R (1 - P_N) P_n`, whose norm is at most
`||P_N R (1-P_N)|| <= eps_N`, and similarly for the adjoint term. The defects of
`T_n`, `T_N ⊕ U` are at most `eps_n + eps_N`, since the defect of `P R P` is
`||P R (1-P) R P|| <= ||[P,R]||`. Apply (R). ∎

Write `w_(N,n)(x)` for the value of the compression `E pi(.) E` on `x`. There is
`N_0` (depending on `p, q`) such that for all `N_0 <= N < n`:

(1.1) `v_n(x) = v_N(x) + w_(N,n)(x)`.

**Lemma 2 (tails are faithful models).** Let `N_j -> infinity`. Choose `n_j > N_j`
large enough that `||(P_(n_j) - P_(N_j)) pi(a_i) (P_(n_j) - P_(N_j))|| >= ||a_i|| - 1/j`
for `i <= j`, where `(a_i)` is dense in `A`. Put `E_j = P_(n_j) - P_(N_j)`. Then
`E_j pi(.) E_j` is a faithful model.

*Proof.* Asymptotic multiplicativity: the error is at most
`||a|| ||[E_j, pi(b)]|| <= ||a|| (||[P_(n_j),pi(b)]|| + ||[P_(N_j),pi(b)]||) -> 0`.
Choice of `n_j`: as `n -> infinity`,
`||(P_n - P_N) X (P_n - P_N)|| -> ||(1-P_N) X (1-P_N)||`. Because `P_N` has
finite rank, `(1-P_N) pi(a)(1-P_N) - pi(a)` is compact, so the limit is
`>= ||pi(a) + K|| = ||a||` by (0.1). Faithfulness then follows for the dense
sequence, and so for all `a`, by the triangle inequality. ∎

## 2. Theorem 1 (monotone divergence)

**Theorem 1.** Let `x in K_0(A)` be in Case 2. Then for every faithful essential `pi` and
every QD exhaustion of `pi`, `v_n(x)` is eventually nondecreasing and tends to
`+infinity`. The same holds in Case 3 with `-infinity`.

*Proof.* *Monotonicity.* By (1.1), `v_(n+1)(x) - v_n(x) = w_(n,n+1)(x)` for large
`n`. Suppose `w_(n,n+1)(x) < 0` for infinitely many `n`. Along those `n` the
blocks `E_n = P_(n+1) - P_n` are nonzero, and `E_n pi(.) E_n` is a model by the
estimate in Lemma 2, needing no faithfulness. That model has infinitely many
negative values, contradicting Case 2.

*Divergence.* If `v_n(x)` does not tend to `+infinity`, it is a bounded,
eventually nondecreasing integer sequence, so it equals a constant `c` for
`n >= N_1`. By (1.1), `w_(N,n)(x) = 0` for all `N_1 <= N < n`. Lemma 2 then
gives a faithful model `E_j pi E_j` with value `0` for all `j`. This
contradicts Case 2, whose faithful models are eventually `> 0`. ∎

**Corollary 1 (criterion).** If some QD exhaustion of some faithful essential
representation has `liminf |v_n(x)| < infinity`, then `x` is killed. The
trichotomy is exhaustive, and Cases 2 and 3 force `|v_n(x)| -> infinity`.

The converse is not claimed. In Case 1, an exhaustion may still have divergent
values, as in the unbalanced exhaustion of Section 6(b). Absorbing arbitrary
vectors into an exhaustion costs blocks of uncontrolled value.

## 3. Theorem 2 (index twists are constants)

**Index of a pair.** For projections `P, Q` with `P - Q` compact,
`ind(P,Q) := index(QP: PH -> QH)`. By Avron--Seiler--Simon, *The index of a
pair of projections*, JFA 120 (1994), together with the Brown--Douglas--Fillmore
essential codimension, it satisfies:

- (I1) `ind(P,Q) = 0` if `||P - Q|| < 1`;
- (I2) `ind(P,Q) + ind(Q,S) = ind(P,S)` when all differences are compact;
- (I3) if `P = P_1 ⊕ Z` and `Q = Q_1 ⊕ Z` on `V ⊕ V^perp` with `dim V < infinity`,
  then `ind(P,Q) = rank P_1 - rank Q_1`.

(I1) holds because `QP: PH -> QH` is invertible when `||P-Q|| < 1`. (I3) holds
because `QP = Q_1 P_1 ⊕ id_(ZH)` and the index of a map between
finite-dimensional spaces is the difference of their dimensions.

**Theorem 2.** Let `pi'` be a unital representation with `pi'(a) - pi(a) in K(H)`
for all `a`. Then:

- (a) `pi'` is faithful and essential;
- (b) every QD exhaustion `(P_n)` of `pi` is a QD exhaustion of `pi'`;
- (c) for `x = [p] - [q]`, with `c(x) := ind(pi(p), pi'(p)) - ind(pi(q), pi'(q))`
  (amplified), we have `v'_n(x) = v_n(x) - c(x)` for all large `n`.

*Proof.* (a) `||pi'(a) + K|| = ||pi(a) + K|| = ||a||`. So `pi'` is injective, and
`pi'(a) in K` forces `a = 0`.

(b) For compact `K_a = pi'(a) - pi(a)`,
`[P_n, K_a] = (P_n - 1)K_a - K_a(P_n - 1)`. Its norm tends to `0` because
`P_n -> 1` strongly and `K_a` is compact.

(c) Fix `p`, and put `R = pi(p)`, `R' = pi'(p)` (amplified), so `R - R'` is
compact. Let `T = (1-P_n) R (1-P_n)` and `Y_n = chi_[1/2,inf)(T)`.

- *Y_n is a compact perturbation of T.* `T - T^2 = (1-P_n) R P_n R (1-P_n)` has
  finite rank and norm at most `eps_n`. For small `eps_n`, the spectrum of `T`
  lies near `{0,1}`. On it, `f(t) = chi(t) - t` factors as `f(t) = h(t)(t - t^2)`
  with `h` continuous: near `0`, `h = -1/(1-t)`; near `1`, `h = 1/t`. So
  `Y_n - T = h(T)(T - T^2)` has finite rank, with norm at most
  `||h|| eps_n -> 0`.
- *The comparison projections.* Put
  `X_n = chi(P_n R P_n) ⊕ Y_n` and `X'_n = chi(P_n R' P_n) ⊕ Y_n`
  on `P_nH ⊕ (1-P_n)H`. Both are projections.
- *X_n against R.* `R - (P_nRP_n + T)` is the finite-rank cross term, of norm
  at most `2eps_n`, and `chi(S) - S` has norm at most `2 * defect`. Hence
  `||X_n - R|| -> 0` and `X_n - R` is compact.
- *X'_n against R'.*
  `||Y_n - (1-P_n)R'(1-P_n)|| <= ||Y_n - T|| + ||(1-P_n)(R-R')||`, and this tends
  to `0` because `R - R'` is compact and `P_n -> 1` strongly. The cross terms of
  `R'` have norm at most `2||[P_n,R']|| -> 0`. So `||X'_n - R'|| -> 0`, and
  `X'_n - R'` is compact, being a sum of finite-rank terms and the compact
  operator `T - (1-P_n)R'(1-P_n)`.
- *Index computation.* For large `n`, by (I1)--(I3),
  `r_n(p) - r'_n(p) = ind(X_n, X'_n) = ind(X_n, R) + ind(R, R') + ind(R', X'_n) = ind(R, R')`.

Subtracting the same identity for `q` gives (c). ∎

`c` is a homomorphism `K_0(A) -> Z`. It is the pairing of `K_0(A)` with the
Cuntz pair `(pi, pi')` in `KK(A, C) = K^0(A)`. This identification is not used.

**Corollary 2.** Under a Cuntz-pair twist, the germ `v_n(x)` changes by a
constant integer. In Case 2 it still tends to `+infinity` by Theorem 1, applied
to `pi'` or directly.

## 4. Theorem 3 (trace wall)

**Theorem 3.** Let `(P_n)` be a QD exhaustion of `pi`. If every weak* limit point
`tau` of `tr_(k_n) o P_n pi(.) P_n` satisfies `tau(x) = 0`, then `v_n(x)/k_n -> 0`.

*Proof.* Limit points are tracial states. Asymptotic multiplicativity gives
`tr(phi(ab)) ≈ tr(phi(a)phi(b)) = tr(phi(b)phi(a)) ≈ tr(phi(ba))`. For
`T_n = P_n R P_n` with defect `delta_n -> 0`,
`|r_n(p) - Tr(T_n)| <= m k_n ||chi(T_n) - T_n|| <= 2 m k_n delta_n`.
Also `Tr(T_n)/k_n = (tr_(k_n) tensor Tr_m)((phi_n tensor id)(p))`, and every
subsequence has a further subsequence along which this converges to
`(tau tensor Tr)(p)`. Subtract the same for `q`. ∎

## 5. Moves that keep the sign (Case 2)

- *Enlargement.* Let `(P'_n)` be a QD exhaustion with `P'_n >= P_n`. Then
  `E_n = P'_n - P_n` asymptotically commutes with `pi`, and by Lemma 1 (same
  proof) `v'_n(x) = v_n(x) + (value of E_n pi E_n)`. The block sequence, along
  indices with `E_n != 0`, is a model, so it is eventually `>= 0`.
- *Direct sum.* For `pi ⊕ sigma` with exhaustion `P_n ⊕ S_n`, the value is
  `v_n(x) + s_n(x)`, and `s_n(x)` is eventually `>= 0` as the value of a model.
- *Subsequences and unitary conjugation.* Both preserve the germ exactly.

## 6. Calibration

(a) `A = C`, `pi = infinity * id` on `l^2`, `P_n` = projection onto the first
`n` basis vectors, `x = [1]`. Then `v_n = n -> infinity`. Indeed `[1]` is not
killed: every model has value `k_n > 0`. This is Case 2, matching Theorem 1.
The class `x = 0` has `v_n = 0` and is killed, matching Corollary 1.

(b) `A = C ⊕ C`, `pi = infinity*ev_1 ⊕ infinity*ev_2` on `l^2 ⊕ l^2`,
`x = [e_1] - [e_2]` (singular in `K_0 = Z^2` with the positive cone `N^2`).

- A balanced exhaustion `P_n = P^(1)_n ⊕ P^(2)_n` has `v_n = 0`; by
  Corollary 1, `x` is killed, which is correct.
- The unbalanced exhaustion `P^(1)_(2n) ⊕ P^(2)_n` has `v_n = n -> infinity`.
  So in Case 1 divergence along one exhaustion is possible, and the converse of
  Corollary 1 needs the choice of exhaustion.

(c) In (b), let `pi'` replace one copy of `ev_1` by a copy of `ev_2`. On one
basis vector `e`, `pi'(e_1) = pi(e_1) - (e ⊗ e)`. This is a Cuntz pair with
`ind(pi(e_1), pi'(e_1)) = +1`, so Theorem 2 predicts `v'_n([e_1]) = v_n([e_1]) - 1`
once `e in P_nH`. Direct count: the rank of `pi'(e_1)` on `P_nH` is one less.
This matches.

## 7. What is obstructed, and where it fails

Let `x` be singular, trace-invisible (Theorem 3 applies to every exhaustion) and
not killed; this is a failure of the K_0-Hahn--Banach property of Brown--Dadarlat
Definition 4.8. By `stw07-trace-invisible-classes-carry-hahn-banach`, universal
K_0-Hahn--Banach lives entirely in such classes. By Theorems 1--3 and Section 5,
for every faithful essential representation and every exhaustion,

  `v_n(x) -> +infinity` (eventually nondecreasing) and `v_n(x) = o(k_n)`,

and the germ is stable under all bounded moves up to a constant. Hence:

1. **Exhaustion constructions** fail at the step "compress along `P_n` and read
   off `v_n = 0` infinitely often". This covers the Voiculescu or Arveson
   characterisation of quasidiagonality, quasicentral approximate units, and
   filtrations of `pi ⊕ sigma`. By Corollary 1, the step already requires a
   bounded subsequence, which Theorem 1 excludes.
2. **Index-theoretic twists** fail at the step "choose a class in `KK(A,C)`
   whose pairing cancels `v_n(x)`". This covers a Cuntz pair, an
   essential-codimension correction, or a Fredholm-module twist of a QD
   representation. Theorem 2 shows the correction is one integer `c(x)`, while
   `v_n(x)` is unbounded and not eventually constant.
3. **Tracial realisation** fails at the step "a model with prescribed limit
   trace has prescribed values". This covers full-map existence and uniqueness
   (CGSTW-type classification of embeddings, which also needs faithful traces
   and so is absent in the normal form of
   `stw07-counterexample-has-singular-trace-normal-form`) and trace pushouts.
   Theorem 3 shows the trace data of `x` coincide with those of `0` at scale
   `k_n`, while the obstruction lives at scale strictly between `1` and `k_n`.

**Gate.** By Voiculescu's theorem (Brown--Ozawa, *C\*-algebras and
finite-dimensional approximations*, Section 1.7), every faithful model `phi_n` is
close to `V_n^* pi(.) V_n` for isometries `V_n: C^(k_n) -> H`. The projections
`Q_n = V_nV_n^*` asymptotically commute with `pi`, because
`||(1-Q_n)pi(b)Q_n||^2 ≈ ||phi_n(b^*b) - phi_n(b)^* phi_n(b)|| -> 0`. So killing
is equivalent to a faithful sequence of almost-commuting finite-rank
projections `Q_n` with value `0` infinitely often. By Theorem 1, such `Q_n`
cannot be nested exhaustions, nor enlargements or bounded modifications of
them. By Theorem 4 (Section 8) they cannot converge strongly to `1` either, and
for every large `N` they must stay a fixed distance `delta_0` away from
containing `P_NH`. A positive answer to Problem VII must construct *moving, non-exhausting*
almost-invariant subspaces whose rank value on `x` cancels at intermediate
scale. A counterexample must make the germ `v_n(x) mod O(1)` a genuine
invariant at scale between `1` and `k_n`.

## 8. Uniform local positivity and the strong-convergence wall

Fix `x = [p] - [q]` with `p, q in M_m(A)` projections, and let `G` be the finite
set of matrix entries of `p` and `q`. For a u.c.p. map `phi: A -> M_k` and a
finite set `F`, write `mult_F(phi) = max_(a,b in F) ||phi(ab) - phi(a)phi(b)||`.
The *value* `val(phi)(x)` is `r(p) - r(q)` computed from
`(phi tensor id_m)(p), (phi tensor id_m)(q)`, whenever both defects are `< 1/8`
(and `val = 0` if `k = 0`).

**Lemma U (uniform positivity).** Let `x` be in Case 2. Then there are a finite
set `F supseteq G` and `epsilon > 0` such that every u.c.p. map
`phi: A -> M_k` with `mult_F(phi) < epsilon` has both defects `< 1/8` and
`val(phi)(x) >= 0`. If moreover `||phi(a)|| > ||a|| - epsilon` for all
`a in F`, then `val(phi)(x) > 0`.

*Proof.* Defects: `(phi tensor id)(p)^2 - (phi tensor id)(p)` has entries
`sum_j phi(p_ij)phi(p_jk) - phi(p_ik) = sum_j [phi(p_ij)phi(p_jk) - phi(p_ij p_jk)]`,
so its norm is at most `m^3 mult_G(phi)`. Take `epsilon <= 1/(100 m^3)`; shrinking
`epsilon` or enlarging `F` preserves both assertions.
Suppose the first assertion fails for every pair `(F, epsilon)`. Fix a dense
sequence `(a_i)` in `A` and put `F_n = G cup {a_1, ..., a_n}`, `epsilon_n = 1/n`.
Pick `phi_n` with `mult_(F_n)(phi_n) < 1/n` and `val(phi_n)(x) < 0`. Since
u.c.p. maps are contractive,
`||phi(ab) - phi(a)phi(b)|| <= ||phi(a'b') - phi(a')phi(b')|| + 2||a - a'|| ||b|| + 2||a'|| ||b - b'||`,
so `(phi_n)` is asymptotically multiplicative on all of `A`: it is a model
with negative values for all `n`, contradicting Case 2. For the second
assertion, choose `phi_n` with in addition `||phi_n(a_i)|| > ||a_i|| - 1/n`
for `i <= n` and `val(phi_n)(x) <= 0`. By density and contractivity
`lim ||phi_n(a)|| = ||a||` for all `a`, so this is a faithful model. It is
eventually `>= 0` by Case 2, hence eventually `= 0`, which is Case 1; contradiction.
Take the smaller `epsilon` and the union of the two finite sets. ∎

For a finite-rank projection `Q` on `H`, write `phi_Q = Q pi(.) Q` on `QH` and
`c_F(Q) = max_(a in F) ||[Q, pi(a)]||`. As in Section 0,
`mult_F(phi_Q) <= M c_F(Q)` with `M = max_(a in F) ||a||`, and the defects of
`phi_Q` on `p, q` are at most `m^2 c_G(Q)`.

**Lemma P (perturbing a projection into a subprojection).** Let `Q` be a
projection, `P` a finite-rank projection, and `delta = ||(1 - Q)P|| <= 1/4`.
Let `P'` be the range projection of `QP`. Then `P' <= Q`, `rank P' = rank P`,
and `d := ||P' - P|| <= 2 delta`. There is a unitary `u` with `u P u^* = P'` and
`||u - 1|| <= 8 d` when `d <= 1/16`.

*Proof.* For `xi in PH`, `||QP xi|| >= (1 - delta^2)^(1/2) ||xi||`, so `QP` is
injective on `PH` and `rank P' = rank P`; clearly `P' <= Q`. For `xi in PH`,
`dist(xi, P'H) <= ||xi - Q xi|| <= delta ||xi||`, so `||(1 - P')P|| <= delta`.
A unit vector `eta in P'H` is `eta = QP zeta` with
`||zeta|| <= (1 - delta^2)^(-1/2)`, and
`(1 - P)eta = (1 - P)(Q - 1)P zeta`, so `||(1 - P)P'|| <= delta (1 - delta^2)^(-1/2)`.
Since `P' - P = P'(1 - P) - (1 - P')P`, and the two terms have orthogonal ranges
and orthogonal supports,
`||P' - P|| = max(||(1-P)P'||, ||(1-P')P||) <= 2 delta`. For the unitary, put
`z = P'P + (1 - P')(1 - P)`. Then `z - 1 = (P' - P)(2P - 1)`, so `||z - 1|| <= d`;
`zP = P'P = P'z`; and `z` is invertible. Let `u = z|z|^(-1)`. Since `z*z` commutes
with `P` (both `z*z = P P' P + (1-P)(1-P')(1-P)` terms are diagonal in `P`),
`u P u^* = z P z^(-1) = P'`. Finally `||z*z - 1|| <= 3d`, so
`|| |z|^(-1) - 1 || <= (1 - 3d)^(-1/2) - 1 <= 3d`, and
`||u - 1|| <= ||z|| || |z|^(-1) - 1|| + ||z - 1|| <= (1 + d) 3d + d <= 8d`. ∎

**Theorem 4 (strong-convergence wall).** Let `x` be in Case 2, let `(F, epsilon)`
be as in Lemma U with `M = max(1, max_F ||a||)`, and let `(P_N)` be a QD
exhaustion of `pi` with values `v_N`. Put `eta = epsilon/(3M)`, and
`delta_0 = min(1/1000, eta/(32M))`. There is `N_*` such that for every
`N >= N_*` and every finite-rank projection `Q` with `c_F(Q) < eta` and
`||(1 - Q)P_N|| < delta_0`,

  `val(phi_Q)(x) >= v_N`.

*Proof.* Choose `N_*` so that `c_F(P_N) < eta/3` for `N >= N_*` (possible
since `F` is finite), and so that `v_N` is the value read at stage `N`
(defects `<= m^2 c_G(P_N) < 1/300`). Let `P'` be the subprojection of `Q` from Lemma P for
`P = P_N`, with `d = ||P' - P_N|| <= 2 delta_0` and unitary `u`,
`||u - 1|| <= 16 delta_0`.

- *`P'` has the value `v_N`.* For `R = pi(p)` (amplified, norm `<= 1`),
  `||P' R P' - u P_N R P_N u^*|| = ||P' (R - u R u^*) P'|| <= 2 ||u - 1|| <= 32 delta_0`.
  Conjugation by `u` does not change ranks. The defect of a compression
  `P R P` is `||P R (1-P) R P|| <= ||[P, R]|| <= m^2 c_G(P)`, and `G subseteq F`.
  So both defects are at most `m^2 eta <= m^2 epsilon/3 <= 1/300` (using
  `c_F(P') < eta` from the next bullet). The margin in (R) is
  `2/300 + 32 delta_0 < 1/4`, so the ranks agree. The same holds for `q`.
- *Commutators.* `c_F(P') <= c_F(P_N) + 2dM <= eta/3 + 4 delta_0 M <= eta/3 + eta/8 < eta`.
  Put `E = Q - P'`, a projection because `P' <= Q`. Then
  `c_F(E) <= c_F(Q) + c_F(P') < 2 eta`, so `mult_F(phi_E) < 2M eta < epsilon`.
- *Additivity.* As in Lemma 1,
  `||Q R Q - (P' R P' ⊕ E R E)|| <= 2||P' R (1 - P')|| <= 2 m^2 c_G(P')`, and the
  defects are at most `m^2 max(c_G(Q), c_G(P'), c_G(E)) <= 2 m^2 eta`. The
  margin in (R) is `2 * 2m^2 eta + 2 m^2 eta = 6 m^2 eta <= 1/50 < 1/4`. By (R),
  `val(phi_Q)(x) = val(phi_(P'))(x) + val(phi_E)(x) = v_N + val(phi_E)(x)`.
- *Sign.* By Lemma U, `val(phi_E)(x) >= 0` (trivially if `E = 0`). ∎

The constants only need to make the rank-lemma margins `< 1/4`, and the
choices above do so because `epsilon <= 1/(100 m^3)` in Lemma U.

**Corollary 4.** Let `x` be in Case 2, and let `(Q_n)` be finite-rank
projections with `||[Q_n, pi(a)]|| -> 0` for every `a in A`.

1. If `Q_n -> 1` strongly, then `val(phi_(Q_n))(x) -> +infinity`.
2. If `val(phi_(Q_n))(x) <= B` along a subsequence, then for every `N >= N_*`
   with `v_N > B`, eventually along that subsequence `||(1 - Q_n)P_N|| >= delta_0`.
   Here `delta_0` depends only on `(F, epsilon)`, not on `N`.

*Proof.* (2) is the contrapositive of Theorem 4, since `c_F(Q_n) < eta`
eventually. For (1), `P_N` has finite rank, so `Q_n -> 1` strongly gives
`||(1 - Q_n)P_N|| -> 0`. Hence for each `N >= N_*`, eventually
`val(phi_(Q_n))(x) >= v_N`, and `v_N -> infinity` by Theorem 1. ∎

Contrapositive, as a killing criterion: if some almost-commuting finite-rank
`Q_n -> 1` strongly has bounded values on `x` along a subsequence, then `x` is
killed. Sequences with `Q_n -> 1` strongly and `||[Q_n, pi(a)]|| -> 0` are
automatically faithful models (Section 0), so this is also the non-nested form
of Corollary 1.

**Calibration.** In 6(b) (`A = C ⊕ C`, `x = [e_1] - [e_2]`, killed) the balanced
exhaustion converges strongly and has value `0`; this is Case 1, and Theorem 4
does not apply. In 6(a) (`x = [1]`, Case 2), any `Q_n -> 1` strongly has value
`rank Q_n -> infinity`, as Corollary 4(1) predicts.

**Scope of the wall.** Killing sequences in Case 1 do exist and can be taken
with `Q_n -> 0` weakly: Voiculescu's theorem lets the isometries `V_n` have
ranges almost orthogonal to any prescribed finite-rank subspace. Corollary 4
says that in Case 2 no bounded-value almost-invariant sequence may
`delta_0`-contain any exhaustion stage of large value. So a proof of
K_0-Hahn--Banach must produce killing subspaces that *escape* every exhaustion
at a uniform angle. Lemma U is the finite form of Case 2: `x` is not killed iff
for some finite `F` and `epsilon > 0`, every `(F, epsilon)`-multiplicative
u.c.p. map is `>= 0` on `x`, and every `(F, epsilon)`-isometric one is `> 0`.
So non-killing is witnessed on a finite window, and killing is a statement
about all windows.
