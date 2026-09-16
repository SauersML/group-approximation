# STW Problem I frontier: a real-rank-zero normal form and a faithful-state criterion

Swarm artifact, 2026-09-16. Target: `stw99-problem-i-quasitraces-are-traces`.
Angle: frontier. Hole attacked:
`stw01-monotone-complete-ii1-awstar-factors-are-w-star` (hole 4 below). Its
Attempts section ends with "Faithful-state route ... Dies at existence". The new
result for the graph is Theorem 3.1, a normal form for counterexamples.

## 0. Summary

**Proved (internal, same trust boundary as `stw01-separable-simple-reduction-proof`).**

- **Theorem 3.1.** If Problem I fails, there is a separable, unital, simple,
  non-elementary, stably finite, nonexact C\*-algebra `A` with the following
  properties:
  - real rank zero and stable rank one;
  - a unital copy of the CAR algebra `M_{2^infty}`;
  - **exactly one** normalized 2-quasitrace `q`, which is faithful and not additive;
  - no tracial state;
  - comparison of projections by `q`: `q(e) < q(f)` implies `e <~ f` in `A`.

  So Problem I is equivalent to the claim that every separable unital simple
  C\*-algebra of real rank zero and stable rank one with a unique normalized
  2-quasitrace has a tracial state.
- **Proposition 4.1 (weighted norm inequality).** A normalized 2-quasitrace `tau` on
  a unital real rank zero C\*-algebra is a trace iff
  `||sum_j t_j p_j|| >= sum_j t_j tau(p_j)` for all finite convex combinations of
  projections.
- **Proposition 4.2 (noncommutative Kelley criterion).** A unital C\*-algebra has a
  faithful state iff `A_+ \ {0}` is a countable union of sets with positive
  intersection number.
- **Proposition 4.3 (dimension intersection numbers).** Let `M` be a type `II_1`
  AW\*-factor. Put `iota_n(M) = inf ||sum_j t_j p_j||`, over convex combinations of
  projections `p_j` with dimension `D(p_j) >= 1/n`. Then:
  - `iota_n(M) <= 1/n` always;
  - `iota_n(M) = 1/n` for all `n` if the dimension quasitrace is a trace;
  - if `iota_n(M) > 0` for all `n`, then `M` has a faithful state.

**Conditional (Wright 1975, as quoted in the Saito-Wright survey; primary not
fetched).** Corollary 4.4: for a monotone complete type `II_1` factor the
following are equivalent:

- being W\*;
- having a faithful state;
- `iota_n > 0` for all `n`;
- `iota_n = 1/n` for all `n`;
- the weighted norm inequality.

This replaces "dies at existence" in hole 4 by an explicit norm inequality. It is an
equivalent reformulation, not a strictly easier claim, so no graph node is created
for it.

**Conditional and marginal.** Proposition 5.1 is a monotone-hull additivity lemma
under an unproved normality hypothesis. It lives only here.

**Not achieved.** Hole 4 remains open. No strictly weaker sub-claim was found
whose conjunction with known results closes it; see Section 6.

## 1. Frontier map (from `bin/cairn why`, 2026-09-16)

Open leaves under the root, and their classification:

| leaf | relation to Problem I |
|---|---|
| `stw01-full-free-group-algebra-quasitraces-are-traces` | equivalent (universal host) |
| `stw01-three-projection-algebra-quasitraces-are-traces` | equivalent (universal host) |
| `stw01-three-projection-corner-pair-quasitrace-additivity` | equivalent via route |
| `stw01-modular-single-pair-quasitrace-additivity` | equivalent via route |
| `stw01-universal-order-pair-quasitrace-additivity` | equivalent (locked by another agent) |
| `stw01-ii1-awstar-factors-are-monotone-complete` (hole 3) | a priori weaker |
| `stw01-monotone-complete-ii1-awstar-factors-are-w-star` (hole 4) | a priori weaker |

Holes 3 and 4 are the only leaves not already equivalent to the root. Their
conjunction is equivalent to the root. Hole 3 is Gow's Question 6.4 and the
type `II_1` factor case of the Arulseelan-Hanson monotone completeness conjecture.
Hole 4 is the type `II_1` factor case of Gow's Question 6.3. Hole 4 was chosen
because it has a concrete known mechanism (Wright's theorem on factors with a
strictly positive functional) that turns it into a functional-existence problem.

## 2. Literature gate (2023-2026 plus the classical sources actually used)

Web search budget was exhausted in this session, so the gate used direct fetches of
arXiv abstract and HTML pages, plus text extracted from arXiv PDFs.

**Recent (2023-2026).**

- A. Gow, *On the Quasitrace Problem and a Characterization of W\*-algebras*,
  arXiv:2601.04431v2 (v2 dated 14 July 2026). The following were checked in the HTML:
  - Theorem 4.11 (four-way equivalence);
  - Corollary 4.10 (a `II_1` AW\*-factor is W\* iff it is a retract of its bidual);
  - Corollary 3.10 (an AW\*-algebra with a separating family of states that are
    completely additive on projections is W\*);
  - Questions 6.3 and 6.4.

  The introduction attributes to Wright (J. London Math. Soc. (2) 12, 1975/76) the
  statement that a type II AW\*-factor with a faithful state is W\*. The
  bibliography entry and the primary paper were **not** obtained, so this is
  **unverified**. Gow gives no construction of a state on a monotone complete
  `II_1` factor.
- A. Arulseelan and D. Hanson, arXiv:2609.10218v1 (dated 9 September 2026).
  Checked:
  - Theorem A (every AW\*-algebra is normal);
  - Corollary 1.5 (W\* iff there is a large W\*-corner);
  - Conjecture 1.3 (monotone completeness);
  - Theorem B (an equiconsistency statement).

  Nothing in it produces states on `II_1` AW\*-factors. Its content is already
  recorded in `stw01-quasitrace-crux-is-awstar-factor-w-star`.
- M. Milhoj and M. Rordam, *Around traces and quasitraces*, arXiv:2309.17412v2
  (dated 30 November 2023). This is a survey. It discusses traceless simple
  C\*-algebras whose ultrapowers carry quasitraces, and characterizations of algebras
  with faithful traces. It contains no real-rank-zero normal form of the kind in
  Theorem 3.1, and no progress on Kaplansky's problem.

No 2023-2026 source found in this gate claims progress on either hole 3 or hole 4.

**Classical, quoted through a fetched secondary source.**

- K. Saito and J. D. M. Wright, *Monotone complete C\*-algebras and generic
  dynamics*, arXiv:1212.6503v1 (28 December 2012). The PDF text was extracted. Near
  its bibliography item [52] the survey says, verbatim up to line breaks:
  "If a monotone complete factor M possesses a strictly positive functional and is
  not a von Neumann algebra then, as an application of a more general result in
  [52] M must be of Type III, see also [30]. Whenever an algebra is almost separably
  representable then it possesses a strictly positive functional. (See Corollary
  3.2)." The survey's references are:
  - [52] J. D. M. Wright, *On semifinite AW\*-algebras*, Math. Proc. Camb. Phil. Soc.
    79 (1975) 443-445;
  - [30] K. Saito, Lecture Notes in Math. 650 (1978) 131-134;
  - [46] J. D. M. Wright, *Regular sigma-completions of C\*-algebras*, J. London
    Math. Soc. 12 (1976) 299-309;
  - [48] J. D. M. Wright, Math. Z. 172 (1980) 131-141.

  **The primary papers [52], [30], [46] and [48] were not fetched.** Every use of
  them below is marked conditional.

**Classical inputs used as standard background (not re-fetched).**

- Kaplansky (Ann. of Math. 1951) and Berberian (*Baer \*-rings*, 1972):
  - comparability of projections in AW\*-factors;
  - halving in type II AW\*-algebras;
  - the dimension function of a finite AW\*-factor, which is faithful, additive on
    orthogonal projections, invariant under equivalence, and completely additive;
  - polar decomposition;
  - spectral projections in maximal abelian AW\*-subalgebras.
- Blackadar-Handelman (J. Funct. Anal. 1982): every bounded 2-quasitrace is monotone
  on self-adjoint elements. Proposition numbers were not rechecked.
- Brown-Pedersen (J. Funct. Anal. 1991): a unital C\*-algebra has real rank zero iff
  its finite-spectrum self-adjoint elements are dense. The theorem number was not
  rechecked.
- The classical equivalence between failure of Problem I and a finite AW\*-factor
  with a nonadditive dimension quasitrace. This is the trust boundary of
  `stw01-separable-simple-reduction-proof`; Gow Theorem 4.11 is a checked modern form.
- Haagerup: 2-quasitraces on exact C\*-algebras are traces. This is already used in
  the graph.

## 3. Theorem 3.1: the real-rank-zero unique-quasitrace witness

### 3.0 Conventions

A *normalized 2-quasitrace* on a unital C\*-algebra `A` is a map `tau: A -> C` with
`tau(1) = 1`. It satisfies `tau(x*x) = tau(xx*) >= 0` and `tau(a+ib) = tau(a)+i tau(b)`
for `a,b` in `A_sa`. It is linear on every commutative C\*-subalgebra, and it extends
to `M_2(A)` with the same properties. We use three standard consequences.

- (Q1) If `v*v = e` and `vv* = f` are projections, then `tau(e) = tau(f)`.
- (Q2) `tau` is linear on `C*(1,h)` for self-adjoint `h`. If `e_1,...,e_k` are
  mutually orthogonal projections, then `tau(sum lambda_i e_i) = sum lambda_i tau(e_i)`.
  In particular `f <= e` implies `tau(e) = tau(f) + tau(e-f) >= tau(f)`.
- (Q3) (Blackadar-Handelman) `a <= b` in `A_sa` implies `tau(a) <= tau(b)`. Hence
  `|tau(a) - tau(b)| <= ||a-b||` on `A_sa`, using `b - ||a-b|| <= a <= b + ||a-b||` and
  (Q2) on `C*(1,b)`.

Also `tau(h) <= ||h||` by (Q3). A C\*-subalgebra containing `1` inherits (Q1)-(Q3)
by restriction.

### 3.1 Statement

**Theorem 3.1.** Suppose STW Problem I fails. Then there is a separable unital
C\*-algebra `A` with the following properties:

- (a) `A` is simple, non-elementary and stably finite;
- (b) `A` has real rank zero and stable rank one;
- (c) `A` contains a unital copy of the CAR algebra `M_{2^infty}`;
- (d) `A` has exactly one normalized 2-quasitrace `q_A`, which is faithful and
  not additive;
- (e) `A` has no tracial state and is not exact;
- (f) for projections `e,f` in `A`, `q_A(e) < q_A(f)` implies `e <~ f` in `A`.

Consequently, Problem I is equivalent to the claim that every separable unital simple
C\*-algebra of real rank zero and stable rank one, with a unique normalized
2-quasitrace, has a tracial state. The easy direction holds because tracial states
are 2-quasitraces.

### 3.2 Inputs from the AW\*-factor

By the classical reduction, there is a finite AW\*-factor `M` whose dimension
quasitrace `q` is a nonadditive normalized 2-quasitrace. A finite type `I` AW\*-factor
is a matrix algebra, on which quasitraces are traces. So `M` is of type `II_1`. We use
the following standard facts about `M`, with `D = q` restricted to projections.

- (M1) `D` is faithful, additive on orthogonal projections, and invariant under
  Murray-von Neumann equivalence. For `t = sum_i lambda_i e_i` with orthogonal
  spectral projections, `q(t) = sum_i lambda_i D(e_i)`.
- (M2) (Comparability.) For projections `e,f`: if `D(e) > D(f)`, then `f <~ e`.
  Indeed either `e <~ f` or `f <~ e`, and `e <~ f` would give `D(e) <= D(f)`.
- (M3) (Halving.) There is a unital embedding `M_{2^infty} -> M`. Halve `1` into
  equivalent orthogonal projections, then halve again and transport with the
  partial isometries, building compatible matrix units for `M_{2^k}` for every `k`.
  For a diagonal dyadic projection `p_r` of normalized rank `r = j/2^k`, (Q1) and
  (Q2) give `D(p_r) = r`.
- (M4) (Real rank zero.) Every self-adjoint `h` in `M` lies in a maximal abelian
  \*-subalgebra. That subalgebra is an AW\*-subalgebra `C(X)` with `X` Stonean, so
  `h` is a norm limit of finite-spectrum self-adjoint elements of `M`.
- (M5) (Stable rank one.) Write `x = v|x|` (polar decomposition in `M`).
  - Compute `D(1 - v*v) = 1 - D(v*v) = 1 - D(vv*) = D(1 - vv*)`.
  - By (M2) and faithfulness of `D`, `1 - v*v ~ 1 - vv*`. So `v` extends to a
    unitary `u` with `u|x| = x`.
  - Then `u(|x| + epsilon)` is invertible and within `epsilon` of `x`.
- (M6) (Simplicity.) `M` is simple as a C\*-algebra. This is proved in
  `stw01-separable-simple-reduction-proof`.

Fix self-adjoint `x,y` in `M` with `q(x+y) != q(x) + q(y)`, and a unital copy
`B` of `M_{2^infty}` from (M3) with its dyadic projections `p_r`.

### 3.3 Construction

Let `A_0 = C*(1, x, y, B)`, which is separable. Given a separable unital
`A_k`, fix a countable dense subset `Q_k` of `A_k`. Let `A_{k+1}` be the
C\*-subalgebra of `M` generated by `A_k` together with the following countably many
elements. For each `h` in `Q_k` and each `m >= 1`:

- (i) a finite-spectrum self-adjoint `t_{h,m}` in `M` with
  `||t_{h,m} - Re h|| < 1/m`, which exists by (M4);
- (ii) an invertible `g_{h,m}` in `M` with `||g_{h,m} - h|| < 1/m`, together with
  `g_{h,m}^{-1}`, which exist by (M5);
- (iii) the fullness coefficients of the separable-simple lemma of
  `stw01-separable-simple-reduction-proof` for the positive element `h*h` and its
  rational cutdowns. These are finitely many `b_i` with
  `sum_i b_i* (h*h - epsilon)_+ b_i` invertible whenever the cutdown is nonzero, plus
  the inverse square root of that sum. They exist by (M6).
- (iv) for every projection `e` in `C*(1, t_{h,m})` and every dyadic `r` in `(0,1)`,
  one partial isometry. There are finitely many such `e`, namely the sums of
  eigenprojections of `t_{h,m}`.
  - if `D(e) > r`, some `v` in `M` with `v*v = p_r` and `vv* <= e`;
  - if `D(e) < r`, some `w` in `M` with `w*w = e` and `ww* <= p_r`.

  These exist by (M2) and (M3). Nothing is adjoined when `D(e) = r`.

The projections in `C*(1, t_{h,m})` are polynomials in `t_{h,m}`, so they lie in
`A_{k+1}`. Let `A` be the norm closure of `union_k A_k`. Call a projection
*scheduled* if it lies in `C*(1, t_{h,m})` for some `h` and `m`. Call an element
*scheduled* if it is some `t_{h,m}`. Since `union_k Q_k` is dense in `A`:

- (D1) the scheduled `t_{h,m}` are dense in `A_sa`, because `||Re h - a|| <= ||h - a||`
  for `a` in `A_sa`;
- (D2) the adjoined invertibles `g_{h,m}`, which are invertible in `A`, are dense
  in `A`.

### 3.4 Proof of (a)-(c)

- **(c)** `B` is contained in `A_0`.
- **(b)** By (D1), the finite-spectrum self-adjoint elements are dense in `A_sa`, so
  `A` has real rank zero (Brown-Pedersen). By (D2), `A` has stable rank one.
- **(a)** Simplicity follows from (iii) exactly as in
  `stw01-separable-simple-reduction-proof`. A nonzero positive element of `A` is
  approximated by some `h*h` with `h` in `union_k Q_k`, and Cuntz-dominates a
  nonzero rational cutdown of it. By (iii) that cutdown is full in `A`.
  - Stable finiteness follows from faithfulness of `q_A = q|A` as in that route.
  - `A` is non-elementary because it is infinite-dimensional and simple, and contains
    `B`.

### 3.5 Proof of (d)-(e)

Let `sigma` be any normalized 2-quasitrace on `A`.

*Step 1: `sigma(p_r) = r`.* `sigma|B` is a normalized quasitrace on `M_{2^infty}`.
On each `M_{2^k}`, diagonal minimal projections are equivalent (Q1) and orthogonal
with sum `1` (Q2). So `sigma(p_r) = r`.

*Step 2: `sigma(e) = D(e)` for scheduled projections `e`.*
- If `D(e) = 0`, then `e = 0` by (M1).
- If `D(e) = 1`, then `D(1-e) = 0`, so `e = 1`.
- Otherwise let `r` be dyadic in `(0,1)`.
  - If `r < D(e)`, (iv) gives `v` in `A` with `v*v = p_r` and `vv* <= e`. By (Q1),
    (Q2) and Step 1, `sigma(e) >= sigma(vv*) = sigma(p_r) = r`.
  - If `r > D(e)`, (iv) gives `w` in `A` with `w*w = e` and `ww* <= p_r`. So
    `sigma(e) = sigma(ww*) <= sigma(p_r) = r`.
  - Dyadics are dense in `(0,1)`, so `sigma(e) = D(e)`.

*Step 3: `sigma(t) = q(t)` for every scheduled `t = t_{h,m}`.* Apply (Q2) on `C*(1,t)`
to both `sigma` and `q`, then use Step 2 and (M1).

*Step 4: `sigma = q|A`.* For `a` in `A_sa` and `epsilon > 0`, (D1) gives a scheduled
`t` with `||t - a|| < epsilon`. By (Q3) for both `sigma` and `q`,
`|sigma(a) - q(a)| <= |sigma(a) - sigma(t)| + |q(t) - q(a)| < 2 epsilon`. So `sigma`
and `q` agree on `A_sa`, and hence on `A`.

Thus `q_A := q|A` is the unique normalized 2-quasitrace on `A`. It is faithful
because `q` is faithful on `M` (`q(a) >= epsilon D(1_[epsilon,infinity)(a))` for
`a >= 0`). It is not additive because `x,y` lie in `A`.

- **(e)** A tracial state on `A` extends to matrices as a trace, so it is a
  normalized 2-quasitrace. It would then equal `q_A`, which is not additive; this is
  impossible. By Haagerup's theorem, an exact `A` would have `q_A` linear, so `A` is
  not exact.

### 3.6 Proof of (f)

Let `e,f` be projections in `A` with `q_A(e) < q_A(f)`.

- By (D1) choose a scheduled `t` with `||t - e|| < 1/4`. Then
  `spec(t)` is contained in `[-1/4,1/4] union [3/4,5/4]`, so
  `e' = 1_(1/2,infinity)(t)` is a scheduled spectral projection with
  `||e' - e|| <= ||e' - t|| + ||t - e|| < 1/2`.
- Projections at distance `< 1` are unitarily equivalent in `A`. Put
  `z = e'e + (1-e')(1-e)`, which is invertible, and let `u` be the unitary part of `z`.
  Then `ueu* = e'`. Likewise `f` is unitarily equivalent to a scheduled `f'`.
- By (Q1), `D(e') = q_A(e) < q_A(f) = D(f')`.
  - If `D(e') = 0`, then `e' = 0` and there is nothing to prove.
  - Otherwise pick a dyadic `r` with `D(e') < r < D(f')`. Then (iv) supplies `w,v` in
    `A` with `w*w = e'`, `ww* <= p_r`, `v*v = p_r` and `vv* <= f'`.
  - Since `p_r w = w`, we get `(vw)*(vw) = w* p_r w = e'` and
    `(vw)(vw)* <= v p_r v* = vv* <= f'`.

So `e' <~ f'`, and hence `e <~ f`. This proves Theorem 3.1.

### 3.7 Remarks

- The difference from the committed reductions is (b), (c), (d) and (f). The
  committed `stw01-traceless-separable-simple-reduction` gives `T(A) = empty` with
  some nonadditive faithful quasitrace. Here the quasitrace simplex is a single point,
  the algebra has real rank zero and stable rank one, and projections are compared
  by the quasitrace.
- In such `A` every state `phi` differs from `q_A` on some projection. Otherwise the
  argument of Step 4 makes `q_A = phi` linear. So Proposition 4.1 applies to `A`
  directly: some convex combination of projections violates the weighted norm
  inequality.
- Stable rank one and comparison of projections are consistent with the open
  graph question `finite-simple-rr0-algebras-have-stable-rank-one`. That question is
  about arbitrary finite simple real rank zero algebras; here stable rank one is
  built in by construction.

## 4. Faithful states and norm inequalities

### 4.1 A weighted norm inequality characterizes linearity

**Proposition 4.1.** Let `A` be a unital C\*-algebra of real rank zero and `tau` a
normalized 2-quasitrace on `A`. The following are equivalent.

1. `tau` is a trace, i.e. linear.
2. Some state `phi` agrees with `tau` on all projections.
3. Some state `phi` satisfies `phi(p) >= tau(p)` for all projections `p`.
4. For all projections `p_1,...,p_N` and convex weights `t_j`,
   `||sum_j t_j p_j|| >= sum_j t_j tau(p_j)`.

*Proof.*

- **(1 => 4).** A linear `tau` is a state, so `tau(x) <= ||x||` for `x >= 0`.
- **(4 => 3).** Let `C` be the convex hull of `{p - tau(p)1}` in `A_sa`, and
  `N = {y in A_sa : max spec(y) < 0}`. The set `N` is open and convex, because
  `max spec` is convex and 1-Lipschitz. For `c = sum_j t_j (p_j - tau(p_j)1)` in `C`,
  `max spec(c) = ||sum_j t_j p_j|| - sum_j t_j tau(p_j) >= 0` by (4). So `C` and `N`
  are disjoint.
  - By Hahn-Banach there is a nonzero real functional `psi` on `A_sa` and a real `s`
    with `psi(y) <= s <= psi(c)` for all `y` in `N` and `c` in `C`.
  - `N` contains `-epsilon 1 - a` for every `a >= 0` and `epsilon > 0`. Scaling `a`
    gives `psi >= 0` on `A_+`, so `psi(1) = ||psi|| > 0`, and `phi = psi/psi(1)` is a state.
  - Letting `epsilon -> 0` gives `s >= 0`, so `phi(p) - tau(p) >= 0` for every
    projection `p`.
- **(3 => 2).** Apply (3) to `1-p`: `1 - phi(p) >= 1 - tau(p)`.
- **(2 => 1).**
  - For a finite-spectrum self-adjoint `t = sum_i lambda_i e_i`, (Q2) and linearity of
    `phi` give `phi(t) = tau(t)`.
  - By real rank zero these elements are dense in `A_sa`. Both `phi` and `tau` are
    1-Lipschitz there by (Q3). So `phi = tau` on `A_sa`, hence on `A`, and `tau` is
    linear. QED

*Remarks.*

- For `N <= 2`, inequality (4) holds for every 2-quasitrace. `C*(1,p_1,p_2)` is
  2-subhomogeneous, hence exact, so Haagerup's theorem makes `tau` linear on it. The
  first possible failure is at three projections, which matches the committed
  three-projection host.
- Applied to the dimension quasitrace of every `II_1` AW\*-factor, Proposition 4.1
  gives: **Problem I holds iff in every type `II_1` AW\*-factor,
  `||sum_j t_j p_j|| >= sum_j t_j D(p_j)` for all convex combinations of
  projections.** By Theorem 3.1, it is equally enough to test the unique quasitrace
  of every separable simple real rank zero, stable rank one algebra. This is an
  equivalent reformulation that involves no functional at all.

### 4.2 Faithful states: a noncommutative Kelley criterion

For `S` contained in `A_+`, put `kappa(S) = inf{ ||x|| : x in conv S }`.

**Proposition 4.2.** A unital C\*-algebra `A` has a faithful state iff
`A_+ \ {0} = union_{n>=1} S_n` with `kappa(S_n) > 0` for every `n`.

*Proof.*

- **(<=).** Put `c_n = kappa(S_n)`. The convex hull of `S_n` is disjoint from the open
  convex set `N_n = {y in A_sa : max spec(y) < c_n}`, since `||x|| = max spec(x)` for
  `x >= 0`.
  - Hahn-Banach gives `psi_n`, nonzero, with `psi_n(y) <= s_n <= psi_n(x)`.
  - As in 4.1, `N_n` contains `c' 1 - a` for `c' < c_n` and `a >= 0`, so `psi_n` is
    positive. Its normalization `phi_n` is a state with `phi_n(x) >= c'` for all
    `c' < c_n`, i.e. `phi_n >= c_n` on `S_n`.
  - Then `phi = sum_n 2^{-n} phi_n` is a state, and for `0 != a in S_n`,
    `phi(a) >= 2^{-n} c_n > 0`.
- **(=>).** Given a faithful state `phi`, take `S_n = {a in A_+ : phi(a) >= 1/n}`. This
  set is convex, and `||x|| >= phi(x) >= 1/n` on it. QED

This is the C\*-analogue of Kelley's intersection-number criterion for strictly
positive measures on Boolean algebras (Kelley 1959; not re-fetched). The proof above
is self-contained.

### 4.3 Dimension intersection numbers

Let `M` be a type `II_1` AW\*-factor with dimension function `D`. For `n >= 1` put

```text
iota_n(M) = inf { ||sum_j t_j p_j|| : N >= 1, t convex, p_j projections, D(p_j) >= 1/n }.
```

**Proposition 4.3.**

- (a) `iota_n(M) <= 1/n`, and `iota_{n+1}(M) <= iota_n(M)`.
- (b) If the dimension quasitrace `q` is a trace, then `iota_n(M) = 1/n` for all `n`.
- (c) `iota_n(M) = 0` iff for every `delta > 0` there are projections `f_j` with
  `D(f_j) <= 1 - 1/n` and convex weights with `sum_j t_j f_j >= (1-delta) 1`. For
  such families, `q(sum_j t_j f_j) - sum_j t_j q(f_j) >= 1/n - delta`.
- (d) If `iota_n(M) > 0` for every `n`, then `M` has a faithful state.
- (e) A convex combination of `N` projections has norm `>= max_j t_j >= 1/N`. So
  witnesses for `iota_n(M) < epsilon` need more than `1/epsilon` terms. With `N <= 2`
  terms the norm is at least `1/n`, by the first remark in 4.1.

*Proof.*

- **(a)** Use a unital `M_{2^K}` inside `M` (M3). Let `s = ceil(2^K/n)`. Let `p_j`,
  for `j` in `Z/2^K`, be the sum of the diagonal matrix units `e_{ii}` with `i` in
  `{j, ..., j+s-1}`. Then `D(p_j) = s/2^K >= 1/n` and
  `2^{-K} sum_j p_j = (s/2^K) 1`, whose norm is `<= 1/n + 2^{-K}`. Monotonicity in
  `n` is clear.
- **(b)** `||x|| >= q(x) = sum_j t_j D(p_j) >= 1/n`.
- **(c)** Put `f_j = 1 - p_j`. Then `sum_j t_j f_j = 1 - x >= (1 - ||x||) 1`. The
  converse is the same computation. The defect bound follows from (Q3):
  `q(sum_j t_j f_j) >= 1 - delta`, while `sum_j t_j D(f_j) <= 1 - 1/n`.
- **(d)** Let `S_n` be the set of `a >= 0` with `a >= (1/n) p` for some projection `p`
  with `D(p) >= 1/n`.
  - These sets cover `M_+ \ {0}`. For `a != 0` and `0 < epsilon < ||a||`, the AW\*
    spectral projection `p = 1_[epsilon,infinity)(a)` is nonzero, `a >= epsilon p`,
    and `D(p) > 0` by faithfulness. Take `n >= max(1/epsilon, 1/D(p))`.
  - If `a_j >= (1/n) p_j`, then `sum_j t_j a_j >= (1/n) sum_j t_j p_j >= 0`. So
    `kappa(S_n) >= iota_n(M)/n > 0`.
  - Apply Proposition 4.2.
- **(e)** `x >= t_j p_j` for every `j`. QED

*Remark (Dixmier hull form; relies on Haagerup-Zsido 1984, not re-fetched).*

- A tracial state on `M` agrees with `D` on projections, by uniqueness of the
  normalized dimension function (dyadic values plus comparability). By real rank
  zero it then equals `q`, so `M` has at most one tracial state. Being simple, `M`
  has the Dixmier property by Haagerup-Zsido.
- Take `n = 2^k`. Projections with equal `D` are unitarily equivalent in a finite
  AW\*-factor: comparability and faithfulness of `D` give `e ~ f` and
  `1-e ~ 1-f`. Replacing each `p_j` by a subprojection of dimension exactly `2^{-k}`
  only lowers the norm; such a subprojection exists by halving and comparability.
- Now apply the Dixmier property to an almost-minimizing convex combination.
  Unitary conjugation preserves the norm, so its hull contains a scalar at most its
  norm. Hence `iota_{2^k}(M)` is the least scalar in the closed convex hull of the
  unitary orbit of a projection with `D = 2^{-k}`.
- So (d) asks that these least Dixmier scalars stay positive. This is an honest
  restatement, not a proof strategy.

### 4.4 Consequences for hole 4 (conditional)

**Corollary 4.4 (conditional on Wright [52] as quoted in arXiv:1212.6503; primary
not fetched).** For a monotone complete type `II_1` AW\*-factor `M`, the following
are equivalent:

- (i) `M` is W\*;
- (ii) `q` is a trace;
- (iii) the weighted norm inequality of Proposition 4.1 holds for `D`;
- (iv) `iota_n(M) = 1/n` for all `n`;
- (v) `iota_n(M) > 0` for all `n`;
- (vi) `M` has a faithful state.

*Proof.*

- **(i => ii).** A `II_1` W\*-factor has a faithful normal tracial state. On
  projections it equals `D` by uniqueness of the dimension function, so by real rank
  zero and (Q3) it equals `q`.
- **(ii <=> iii).** Proposition 4.1.
- **(ii => iv => v => vi).** Proposition 4.3 (b) and (d).
- **(vi => i).** This is the quoted theorem: a monotone complete factor with a
  strictly positive functional that is not a von Neumann algebra is of type III.
  `M` is finite, hence not of type III. QED

So, conditionally, hole 4 is equivalent to: every monotone complete type `II_1`
AW\*-factor satisfies `iota_n > 0` for all `n`.

Using Gow's quotation of Wright (J. London Math. Soc. 1975/76, unverified) for
general type II factors instead, Problem I is equivalent to `iota_n(M) > 0` for all
`n` and all type `II_1` AW\*-factors. Both are reformulations of "dies at existence"
in the committed Attempts, turned into a norm inequality about finitely many
projections. Neither is strictly easier, so no graph node is created for them. The
unconditional part (Propositions 4.1-4.3) is recorded here so that a later agent
can build on it.

## 5. A conditional monotone-hull additivity lemma

Let `M` be monotone complete: every norm-bounded increasing net in `M_sa` has a
least upper bound in `M_sa`. For bounded increasing nets `h_alpha` and `k_beta` in a
monotone complete C\*-algebra, `sup (h_alpha + k_beta) = sup h_alpha + sup k_beta`
over the product directed set. Translation and positive scaling are order
automorphisms, so this follows by taking suprema one variable at a time.

Call a normalized 2-quasitrace `sigma` on `M` *order-normal* if `h_alpha` increasing
to `h` implies `sigma(h_alpha) -> sigma(h)`.

**Proposition 5.1 (conditional).** Let `sigma` be order-normal, and let `V` be a real
subspace of `M_sa` containing `1` on which `sigma` is additive. Let `U(V)` be the set
of suprema of bounded increasing nets in `V`, and put `L(V) = -U(V)`. Then `U(V)` is a
convex cone containing `V`, `U(V) - U(V)` is a real subspace, and `sigma` is additive
on its norm closure.

*Proof.* Throughout, `a_alpha` increasing to `a` and `b_beta` increasing to `b` are
nets in `V`.

1. *`U(V)` and `V`.* For `a` in `U(V)` and `b` in `V`, `a_alpha + b` increases to
   `a + b`. So `sigma(a+b) = lim sigma(a_alpha) + sigma(b) = sigma(a) + sigma(b)`.
2. *`U(V)` and `U(V)`.* By 1, `sigma(a_alpha + b) = sigma(a_alpha) + sigma(b)`, and
   `a_alpha + b` increases to `a + b`. Take limits.
3. *`L(V)` and `L(V)`.* Use `sigma(-x) = -sigma(x)` from (Q2), then apply 2.
4. *`U(V)` and `L(V)`.* For `a` in `U(V)` and `b'` in `U(V)`, `a_alpha - b'` lies in
   `L(V)`, because `V` is contained in `L(V)` and `L(V)` is closed under sums. So by 3,
   `sigma(a_alpha - b') = sigma(a_alpha) - sigma(b')`. Since `a_alpha - b'` increases
   to `a - b'`, take limits.
5. *General elements.* Let `x = a_1 - b_1` and `y = a_2 - b_2` with all four in
   `U(V)`. Then
   `sigma(x+y) = sigma((a_1+a_2) - (b_1+b_2)) = sigma(a_1) + sigma(a_2) - sigma(b_1) - sigma(b_2) = sigma(x) + sigma(y)`,
   by 4, then 2, then 4 again.
6. *Closure.* `sigma` is 1-Lipschitz on `M_sa` by (Q3). QED

Iterating transfinitely makes `sigma` additive on the smallest norm-closed subspace
that contains `V` and is closed under suprema and infima of bounded monotone nets.
Starting from `V = S_sa` for an exact unital C\*-subalgebra `S`, where Haagerup's
theorem makes `sigma` linear, we get the following. **If `q` is order-normal and
`M_sa` is the monotone closure of `S_sa` for some exact `S`, then `q` is a trace.**

*Where it dies.*

- Order-normality of the dimension quasitrace on general increasing nets of
  self-adjoint elements is not known for non-W\* factors. Additivity of `D` on
  families of orthogonal projections does not control `q(h_alpha)` for noncommuting
  `h_alpha`.
- Monotone generation by an exact subalgebra is not implied by hole 4.
- By the survey's account of Wright [46] and [52] (item 5 of Section 6), regular
  sigma-completions of infinite-dimensional simple separable unital algebras are wild
  factors of type III, not `II_1`. So the obvious candidate `S` (the CAR algebra)
  cannot generate a `II_1` factor through its regular completion.

This lemma is recorded for reuse only.

## 6. Dead ends, with the exact failure point

1. **Uniform superadditivity to get `iota_n > 0`.** A lower bound
   `q(sum_j t_j p_j) >= c sum_j t_j D(p_j)`, with `c` independent of the number of
   terms, gives `iota_n >= c/n`, so (conditionally) hole 4. But:
   - monotonicity gives only `q(sum_{j<=N} a_j) >= max_j q(a_j) >= (1/N) sum_j q(a_j)`;
   - the `2 x 2` pinching trick gives the opposite bound
     `q(a+b) <= 2(q(a)+q(b))`, whose `N`-term iterate carries a factor `N`.

   **Dies** at dimension-free constants. No superadditivity estimate for 2-quasitraces
   was found in the sources checked. Any subadditivity-type estimate bounds the wrong
   direction.
2. **Dixmier property (Haagerup-Zsido).** By the remark in 4.3, `iota_{2^k}` is the
   least Dixmier scalar of a projection of dimension `2^{-k}`, and existence of a trace
   is equivalent to all Dixmier scalar sets being singletons. **Dies** as a pure
   restatement: no estimate on the scalar interval is available.
3. **Normality of `q` from monotone completeness** (feeding Proposition 5.1, or Gow's
   Corollary 3.10 through completely additive states). **Dies**: monotone completeness
   controls suprema but gives no continuity of a nonlinear `q` along noncommuting nets.
4. **Maharam/Gaifman-type commutative obstruction.** Countable decomposability plus
   monotone completeness does not give a strictly positive functional even for
   commutative Stonean algebras (Gaifman-type ccc examples; not re-fetched). **This
   obstruction does not bite in the `II_1` factor**: on every maximal abelian
   AW\*-subalgebra `C(X)`, `q` restricts to a faithful *state*. The obstacle is purely
   the gluing across noncommuting MASAs, which is Problem I itself.
5. **Regular sigma-completion of the CAR algebra.** The survey (arXiv:1212.6503,
   Section 1) says of Wright [46]: when `A` is separably representable, its regular
   sigma-completion is monotone complete and almost separably representable, and when
   `A` is also infinite-dimensional, unital and simple, it is a wild factor. With
   item 8 below, such factors are of type III. **Dies**: it produces type III, not
   `II_1`.
6. **Transfer of type III wild constructions** (already in the hole's Attempts).
   Their mechanism is the absence of normal states, which the `II_1` dimension function
   contradicts on projections. **Dies.**
7. **Splitting hole 4 as "`q` order-normal" plus "monotone generation by an exact
   subalgebra".** The conjunction implies hole 4 for the factors it covers, but hole
   4 implies neither, so it is not a decomposition into weaker claims. **Not
   recorded as a route.**
8. **Small factors.** If a wild factor is almost separably representable, it is of
   type III (survey, Corollary 3.2 with [52]). So hole 4 is already settled, modulo
   the unverified primary, for almost separably representable monotone complete
   `II_1` factors. What remains is the non-small case, which has no known examples in
   either direction.
9. **K-theory of the Theorem 3.1 witness.** `q_A` restricted to projections gives a
   state on `K_0(A)`. A Blackadar-Handelman type theorem (every state on `K_0` of a
   unital algebra comes from a quasitrace; not re-fetched) would make it the unique
   `K_0`-state. Deciding whether that state lifts to a tracial state is exactly the
   question for real rank zero algebras. **Dies** as a restatement.

## 7. Next steps

1. **Primary check of Wright.** Fetch J. D. M. Wright, *On semifinite
   AW\*-algebras*, Math. Proc. Camb. Phil. Soc. 79 (1975) 443-445, and the J. London
   Math. Soc. paper quoted by Gow. If the statements are confirmed:
   - add a citation route;
   - add a route into hole 4 through a new claim "every monotone complete `II_1` factor
     has `iota_n > 0` for all `n`".

   That claim would be equivalent to hole 4, so it helps only as a normal form.
2. **Attack `iota_2 > 0` combinatorially inside the CAR subalgebra.** A violating
   convex combination needs more than `1/epsilon` terms (4.3 e) and at least three
   noncommuting projections (4.1, first remark). A structural lower bound on the number
   of terms or the noncommutativity pattern, in terms of `epsilon`, would be a first
   quantitative foothold.
3. **Use the Theorem 3.1 normal form in the host leaves.** A counterexample can be taken
   with real rank zero, stable rank one, a unique quasitrace and projection comparison.
   The three-projection and order-pair leaves could restrict their search to algebras
   where the violating projections compare by `q`.
4. **Hole 3 (monotone completeness).** Nothing here addresses it. Proposition 4.3 is
   insensitive to monotone completeness, so the conditional equivalences in Section 4
   do not reduce hole 3.
