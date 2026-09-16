# The trace-positive singular class is a K_0-state separation problem (2026-09-16)

Swarm lane on `qd-nuclear-algebra-with-qd-trace-positive-singular-class`.  This
artifact builds on `research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md`,
cited as **[HB]**.  From it we use Lemma 1, the estimate (V1), Theorem C (node
`stw07-singular-classes-change-sign-or-sit-on-boundary`) and Theorem E.

It contains:

- Theorem 1: the hole is equivalent, algebra by algebra, to a gap between the
  K_0-states of all traces and those of quasidiagonal traces.
- Theorem 2: tensoring with a bootstrap-class factor can neither create nor
  destroy such a class.
- Proposition 3: when `K_0` separates traces, for example in real rank zero,
  a nonquasidiagonal trace is enough.
- Proposition 4: an extreme normal form, and a dichotomy with STW IX(1).

## 0. Conventions

`A` is separable and unital.  `T(A)` is its tracial state space with the weak*
topology.

- **Quasidiagonal traces.**  A tracial state `tau` is *quasidiagonal* (Brown)
  if there are c.c.p. maps `phi_n: A -> M_(k_n)` with
  `||phi_n(ab)-phi_n(a)phi_n(b)|| -> 0` and `tr o phi_n -> tau` weak*.
  `T_qd(A)` is the set of quasidiagonal tracial states.  A unital
  quasidiagonal algebra has `T_qd(A) != {}` ([HB] Lemma 1 applied to a
  faithful model).
- **K_0-states.**  For `tau in T(A)` put
  `tau_*([p]-[q]) = (Tr (x) tau)(p) - (Tr (x) tau)(q)`, a state on
  `(K_0(A), K_0^+(A), [1])`, and write `x^(tau) = tau_*(x)`.
- **The map r_A.**  Let `r_A: T(A) -> R^(K_0(A))` send `tau` to `tau_*`.  The
  target carries the product topology.
- **Singular classes.**  `x in K_0(A)` is *singular* if
  `Zx cap K_0^+(A) = {0}`.
- **Witnesses.**  A *witness* is a separable unital nuclear quasidiagonal `A`
  with a singular `x` such that `x^ > 0` on `T_qd(A)`.  These are exactly the
  objects the hole asks for.

## 1. Lemmas

**Lemma 1.1.**  `T_qd(A)` is weak* closed and convex, hence compact.

*Proof.*
- *Closed.*  Let `tau_i -> tau` with `tau_i` quasidiagonal, and fix a dense
  sequence `(a_j)` in `A`.
  - For each `m`, choose `i` with `|tau_i(a_j)-tau(a_j)| < 1/m` for `j <= m`.
  - Then choose one c.c.p. `phi: A -> M_k` from a model of `tau_i` with
    `|tr phi(a_j) - tau_i(a_j)| < 1/m` and
    `||phi(a_j a_l) - phi(a_j)phi(a_l)|| < 1/m` for `j,l <= m`.
  - The resulting diagonal sequence `phi_m` is c.c.p.
  - Its multiplicativity defect `D(a,b) = phi(ab)-phi(a)phi(b)` satisfies
    `||D(a,b)-D(a',b')|| <= 2(||a-a'|| ||b|| + ||a'|| ||b-b'||)`.  So the defect
    tends to `0` on all of `A`, not only on the dense sequence.
  - Likewise `tr o phi_m -> tau` weak*.
- *Convex.*  Take models `phi_n -> tau_1` into `M_(k_n)` and `psi_n -> tau_2`
  into `M_(l_n)`.  For `t = p/q` rational, use `p l_n` copies of `phi_n` and
  `(q-p) k_n` copies of `psi_n`.
  - Direct sums keep the multiplicativity defect.
  - The normalised trace is `t tr phi_n + (1-t) tr psi_n`.
  - Closedness then gives real `t`. QED

**Lemma 1.2.**  `r_A` is affine and continuous.  If `g = [p]-[q]` with
`p,q in M_n(A)`, then `|tau_*(g)| <= n` for every `tau in T(A)`.

*Proof.*  Each coordinate `tau -> (Tr (x) tau)(p) - (Tr (x) tau)(q)` is affine
and weak* continuous, and `0 <= (Tr (x) tau)(p) <= n`. QED

**Lemma 1.3 (functoriality).**  Let `theta: A -> B` be a unital *-homomorphism
and `tau in T(B)`.  Then `(tau o theta)_* = tau_* o theta_*`.  If `tau` is
quasidiagonal, so is `tau o theta`.

*Proof.*  The first statement follows from the definitions.  For the second,
compose a model of `tau` with `theta`: this keeps complete positivity,
contractivity and asymptotic multiplicativity. QED

**Lemma 1.4 (tensor products).**  Let `A, D` be separable and unital, and
`B = A (x)_min D`.

1. If `tau_1 in T_qd(A)` and `tau_2 in T_qd(D)`, then `tau_1 (x) tau_2` lies
   in `T_qd(B)`.
2. If `A` and `D` are quasidiagonal, so is `B`.

*Proof.*
1. Let `phi_n`, `psi_n` be models for `tau_1`, `tau_2`.
   - `Phi_n = phi_n (x) psi_n : B -> M_(k_n) (x) M_(l_n)` is c.c.p.
   - On elementary tensors the multiplicativity defect is at most
     `||D_phi(a,a')|| ||dd'|| + ||a|| ||a'|| ||D_psi(d,d')||`, which tends to
     `0`.  (Write `Phi(aa' (x) dd') - Phi(a (x) d)Phi(a' (x) d')` as
     `D_phi(a,a') (x) psi(dd') + phi(a)phi(a') (x) D_psi(d,d')`.)
     So it tends to `0` on the algebraic tensor product, and on all of `B`
     by the Lipschitz bound of Lemma 1.1.
   - `tr Phi_n(a (x) d) = tr phi_n(a) tr psi_n(d) -> tau_1(a) tau_2(d)`.  The
     functionals `tr o Phi_n` have norm at most `1`, so this gives weak*
     convergence.
2. Take faithful quasidiagonal representations of `A` on `H` and `D` on `K`,
   with finite-rank projections `P_n` and `Q_n` increasing to `1`.
   - `P_n (x) Q_n` increases to `1` on `H (x) K`.
   - `||[P_n (x) Q_n, a (x) d]|| <= ||[P_n,a]|| ||d|| + ||a|| ||[Q_n,d]||`,
     which tends to `0`.  By density this holds on the faithful representation
     of `B` on `H (x) K`. QED

**Lemma 1.5 (extreme traces of tensor products).**  Let `omega` be an extreme
point of `T(A (x)_min D)`.  Then `omega = rho_1 (x) rho_2` with
`rho_1 = omega( . (x) 1)` and `rho_2 = omega(1 (x) . )`.

*Proof.*  Let `(pi, H, xi)` be the GNS triple, `M = pi(B)''`, and `w` the
vector trace `<. xi, xi>` on `M`.  It is a faithful normal tracial state.

- **`M` is a factor.**  Suppose `z` is a central projection with
  `0 < w(z) < 1`.  Then `omega = w(z) omega_z + w(1-z) omega_(1-z)`, where
  `omega_z(b) = w(pi(b) z)/w(z)` is tracial.  Extremality forces
  `omega_z = omega`.  By normality this gives `w(xz) = w(z) w(x)` for all
  `x in M`, and `x = z` gives `w(z) in {0,1}`.
- **`M_1` is a finite factor.**  Let `M_1 = pi(A (x) 1)''` and
  `M_2 = pi(1 (x) D)''`.  They commute and generate `M`.  A central projection
  of `M_1` commutes with `M_1` and with `M_2`, which lies in `M_1'`.  So it is
  central in `M` and hence scalar.  Thus `M_1` is a factor, and it is finite
  since `w` restricts to a faithful normal trace on it.
- **The trace factorises.**  Fix `d >= 0` in `D` and put `h = pi(1 (x) d)`,
  which lies in `M_1'`.  Define `psi(x) = w(xh)` on `M_1`.
  - `psi` is normal.
  - It is positive, since `xh = x^(1/2) h x^(1/2) >= 0` when `x >= 0`
    commutes with `h`.
  - It is tracial: `w(xyh) = w(yhx) = w(yxh)`.
  - A normal positive tracial functional on a finite factor is a multiple of
    the trace, so `psi = w(h) w|_(M_1)`.

  Hence `omega(a (x) d) = rho_1(a) rho_2(d)`.  Linearity and continuity finish
  the proof. QED

**Lemma 1.6 (Krein--Milman transfer).**  Let `K` be compact convex, `r` an
affine continuous map into a locally convex space, and `C` a closed convex set.
If `r(ext K) ⊆ C`, then `r(K) ⊆ C`.

*Proof.*  `r(conv ext K) = conv r(ext K) ⊆ C`.  By Krein--Milman, `K` is the
closure of `conv ext K`.  Continuity of `r` and closedness of `C` give the
result. QED

## 2. Theorem 1: the K_0-state form of the hole

**Theorem 1.**  Let `A` be separable, unital, exact and quasidiagonal.  The
following are equivalent.

- (a) Some singular `x in K_0(A)` has `x^ > 0` on `T_qd(A)`.
- (b) There are `y in K_0(A)` and `sigma in T(A)` with `y^ > 0` on `T_qd(A)`
  and `y^(sigma) < 0`.
- (c) `r_A(T(A)) != r_A(T_qd(A))`.  That is, some tracial state induces a
  K_0-state which no quasidiagonal tracial state induces.

Moreover, `sigma` in (b) can be taken extreme in `T(A)` with
`pi_sigma(A)''` a II_1 factor, isomorphic to `R` when `A` is nuclear.

*Proof.*

**(a) => (b).**  `A` is stably finite, being quasidiagonal.  Theorem C of [HB]
gives `sigma` with `x^(sigma) <= 0`.  `T_qd(A)` is compact (Lemma 1.1) and
`x^` is continuous, so `x^ >= delta > 0` on `T_qd(A)`.  Take an integer
`N > 1/delta` and `y = Nx - [1]`.  Then `y^ >= N delta - 1 > 0` on
`T_qd(A)`, and `y^(sigma) <= -1`.

**(b) => (c).**  `r_A(sigma)(y) < 0`, while `r_A(tau)(y) > 0` for every
quasidiagonal `tau`.

**(c) => (b).**
1. *Separate.*  Let `sigma` satisfy `s_0 = r_A(sigma) notin C = r_A(T_qd(A))`.
   `C` is compact and convex in the locally convex space `R^(K_0(A))`, by
   Lemmas 1.1 and 1.2.  By Hahn--Banach there is a continuous linear
   functional `f` with `f(s_0) + delta <= inf_C f` for some `delta > 0`.
   Continuous functionals on a product of lines are finite combinations of
   coordinates, so `f(s) = sum_(i<=k) c_i s(g_i)` with real `c_i`.
2. *Make the coefficients rational.*  By Lemma 1.2, `|s(g_i)| <= n_i` on
   `r_A(T(A))`.  Choose rationals `q_i` with `sum |c_i - q_i| n_i < delta/3`,
   and put `f_q = sum q_i s(g_i)`.  Then `|f_q - f| < delta/3` on `r_A(T(A))`,
   so `min_C f_q - f_q(s_0) >= delta/3`.
3. *Clear denominators.*  Pick a rational `c` strictly between these two
   numbers.  Let `L >= 1` be an integer clearing all denominators of the `q_i`
   and of `c`.  Put `y = L(sum q_i g_i - c[1])`, which lies in `K_0(A)`.
   Then `y^ = L(f_q o r_A - c)` is `> 0` on `T_qd(A)` and `< 0` at `sigma`.

**(b) => (a).**  Suppose `my in K_0^+(A)` for an integer `m`.
- If `m >= 1`, then `sigma_*(my) = m y^(sigma) < 0`, which is impossible for a
  positive class.
- If `m <= -1`, then `tau_*(my) < 0` for any `tau in T_qd(A)`, which is
  nonempty.  Impossible again.

So `m = 0`, and `y` is singular.

**Extreme normal form.**  Suppose `r_A(ext T(A)) ⊆ C`.  Since `C` is closed
and convex, Lemma 1.6 gives `r_A(T(A)) ⊆ C`, contradicting (c).  So some
extreme `sigma` has `r_A(sigma) notin C`, and the proof of (c) => (b) applies
to it.

For extreme `sigma`, `pi_sigma(A)''` is a finite factor (Lemma 1.5, first
step).  If it were `M_k`, then `pi_sigma: A -> M_k` would be a
*-homomorphism with `sigma = tr o pi_sigma`, so `sigma` would be
quasidiagonal and `r_A(sigma) in C`.  Hence it is II_1.  When `A` is nuclear
the factor is injective with separable predual, hence `R` by Connes. QED

**Remark 2.1 (state space).**  By `blackadar-rordam-haagerup-k0-states-are-traces`,
`r_A(T(A))` is the whole state space `S(K_0(A), K_0^+, [1])` when `A` is exact
and stably finite.  So the hole asks for a separable unital nuclear
quasidiagonal algebra in which the K_0-states induced by quasidiagonal traces
form a **proper** closed convex subset of the K_0-state space.

**Remark 2.2 (finite-dimensional form).**  `r_A(T_qd(A))` is the set of
pointwise limits `s(g) = lim (phi_n)_*(g)/k_n` along unital models
`phi_n: A -> M_(k_n)`.

- *Limits lie in `C`.*  Given such a limit, pass to a subsequence with
  `tr o phi_n -> tau`.  Then `tau` is quasidiagonal, and (V1) of [HB] gives
  `s = tau_*`.
- *Every point of `C` is a limit.*  A model of `tau in T_qd(A)` can be made
  unital without changing limits, by compressing as in [HB] Lemma 1 and
  conjugating by `(e phi(1) e)^(-1/2)`.  Then (V1) gives
  `(phi_n)_*/k_n -> tau_*`.

So a witness is exactly an algebra with a K_0-state that no normalised
K_0-map of a matrix model approximates.  This is the K_0-analogue of a
nonquasidiagonal trace.

**Remark 2.3 (the witness itself fails the UCT).**  If `A` is a witness, (c)
gives a tracial state outside `T_qd(A)`.  It is amenable because `A` is
nuclear.  By Gabe's theorem (arXiv:1511.02760v1, abstract: any amenable trace
on a separable exact quasidiagonal UCT algebra is quasidiagonal), `A` does not
satisfy the UCT.  Theorem E of [HB] gives the same conclusion for the quotient
`A/J_sigma`.  Neither statement implies the other, because the UCT is not
known to pass to quotients or to ideals.

## 3. Theorem 2: bootstrap tensor factors neither create nor destroy the class

**Theorem 2.**  Let `A` and `D` be separable, unital, nuclear and
quasidiagonal, with `D` in the bootstrap class.  Then `A (x) D` (nuclear and
quasidiagonal by Lemma 1.4) is a witness if and only if `A` or `D` is.

*Proof.*

**If.**  Let `y`, `sigma` witness (b) for `A`, and let `iota: A -> A (x) D`
send `a` to `a (x) 1`.
- For `omega in T_qd(A (x) D)`, `omega o iota` is quasidiagonal
  (Lemma 1.3).  So `omega_*(iota_* y) = (omega o iota)_*(y) > 0`.
- For any `tau_D in T(D)`,
  `(sigma (x) tau_D)_*(iota_* y) = sigma_*(y) < 0`.

Theorem 1, (b) => (a), applies.  The case where `D` is a witness is
symmetric.

**Only if.**  Suppose neither `A` nor `D` is a witness.  By Theorem 1,
`r_A(T(A)) = r_A(T_qd(A))` and `r_D(T(D)) = r_D(T_qd(D))`.

*Step 1 (Künneth).*  `D` is in the bootstrap class, so the Künneth theorem
(Schochet 1982; Rosenberg--Schochet, Duke Math. J. 55 (1987); Blackadar,
*K-theory for operator algebras*, §23) gives an exact sequence

```text
0 -> (K_0(A) (x) K_0(D)) (+) (K_1(A) (x) K_1(D)) --alpha--> K_0(A (x) D) -> Tor-terms -> 0
```

where `alpha` is the external product.  Tor groups are torsion.  So for each
`z in K_0(A (x) D)` we fix `m_z >= 1` and a decomposition

```text
m_z z = sum_i x_i × y_i + sum_j u_j × v_j,
```

with `x_i in K_0(A)`, `y_i in K_0(D)`, `u_j in K_1(A)`, `v_j in K_1(D)`.

*Step 2 (trace values).*
- **Even products.**  For projections `p in M_n(A)` and `q in M_k(D)`,
  `[p] × [q] = [p (x) q]`.  So `(rho_1 (x) rho_2)_*(x × y) = rho_1*(x) rho_2*(y)`.
- **Odd products vanish on every trace.**  Let `omega in T(A (x) D)`, and let
  `u in M_n(A)`, `v in M_k(D)` be unitaries.
  - Write `phi_u: C(T) -> M_n(A)` for the map `z -> u`, and `phi_v` similarly.
  - Naturality of `alpha` gives `[u] × [v] = (phi_u (x) phi_v)_*(c)`, where
    `c = [z] × [z] in K_0(C(T^2))`.
  - Naturality under evaluation at a point sends `c` to `0 × 0 = 0` in
    `K_0(C)`.  Since `T^2` is connected, `c = [P]-[Q]` with
    `rank P(t) = rank Q(t)` for all `t`.
  - Put `mu = (Tr (x) omega) o (phi_u (x) phi_v)`, a positive functional on
    `C(T^2)`.  Then
    `omega_*([u] × [v]) = int (rank P(t) - rank Q(t)) d mu(t) = 0`.
- **Consequence.**  For product traces,

  ```text
  (rho_1 (x) rho_2)_*(z) = m_z^(-1) sum_i rho_1*(x_i) rho_2*(y_i),
  ```

  which depends only on the pair `(rho_1*, rho_2*)`.

*Step 3 (replace by quasidiagonal traces).*  Let `omega` be extreme in
`T(A (x) D)`.
- By Lemma 1.5, `omega = rho_1 (x) rho_2`.
- By hypothesis there are `tau_1 in T_qd(A)` and `tau_2 in T_qd(D)` with
  `tau_i* = rho_i*`.
- By Step 2, `(tau_1 (x) tau_2)_* = omega_*`.
- By Lemma 1.4, `tau_1 (x) tau_2` is quasidiagonal.

Hence `r(ext T(A (x) D)) ⊆ r(T_qd(A (x) D))`.  The right-hand side is compact
and convex, so Lemma 1.6 gives `r(T(A (x) D)) = r(T_qd(A (x) D))`.  By
Theorem 1, `A (x) D` is not a witness. QED

Only the torsion-ness of `coker alpha` in degree `0` was used.  So `D` may be
any algebra for which the Künneth map against `A` has torsion cokernel.

**Corollary 3.1.**  Let `D` be separable, unital, nuclear and quasidiagonal in
the bootstrap class.  Then every tracial state of `D` is quasidiagonal.  This
is the second theorem in the abstract of J. Gabe, *Quasidiagonal traces on
exact C\*-algebras*, arXiv:1511.02760v1 (J. Funct. Anal. 272 (2017)): any
amenable trace on a separable exact quasidiagonal UCT algebra is quasidiagonal.
Traces on nuclear algebras are amenable.  Examples are `C(X)`, AF and UHF
algebras, the Jiang--Su algebra `Z`, and irrational rotation algebras.

- `D` is not a witness (Theorem 1 (c)), so `A (x) D` is a witness iff `A` is.
- In particular a witness may be assumed `Z`-stable and `Q`-stable.
- For an inner automorphism `Ad w`, `A x|_(Ad w) Z` is isomorphic to
  `A (x) C(T)`, via `a -> a (x) 1` and `U -> w (x) z`, the gauge-invariant
  uniqueness for `Z` giving injectivity.  So this crossed product is a witness
  iff `A` is.
- The claim node's remark that "enlarging `K_0` by tensoring changes the trace
  space" is thus a theorem: tensor enlargements by such `D` never manufacture
  the separating class.

## 4. Proposition 3: algebras whose K_0 separates traces

**Proposition 3.**  Let `A` be separable, unital, exact and quasidiagonal, and
suppose `K_0(A)` separates tracial states (`r_A` is injective).  Then `A`
carries a singular class positive on `T_qd(A)` if and only if
`T(A) != T_qd(A)`.

- If `A` has real rank zero, `r_A` is injective.
- Injectivity of `r` passes to quotients.

*Proof.*
- **Equivalence.**  If `sigma notin T_qd(A)`, injectivity gives
  `r_A(sigma) != r_A(tau)` for all `tau in T_qd(A)`.  So (c) of Theorem 1
  holds.  Conversely, (c) produces `sigma` with `r_A(sigma) notin
  r_A(T_qd(A))`, so `sigma` is not quasidiagonal.  This direction needs no
  injectivity.
- **Real rank zero.**  Let `a in A_sa` and `eps > 0`.  There is `b in A_sa`
  with finite spectrum and `||a-b|| < eps`.  Then `b = sum lambda_j p_j` with
  spectral projections `p_j in A`, so `tau(b) = sum lambda_j tau_*([p_j])`.
  Two traces with the same K_0-state therefore agree on `a` up to `2 eps`.
- **Quotients.**  Let `q: A -> A/J`, and let `tau, tau'` be traces of `A/J`
  with equal K_0-states.  By Lemma 1.3, `tau o q` and `tau' o q` have equal
  K_0-states, so they are equal, and `q` is onto. QED

So among K_0-trace-separating algebras (for instance real rank zero), a witness
is the same thing as a separable unital nuclear quasidiagonal algebra with a
nonquasidiagonal tracial state.  The forward direction is Theorem E of [HB].

## 5. Proposition 4: extreme normal form and the IX(1) dichotomy

**Proposition 4.**  Let `A` be a witness.  Theorem 1 gives an extreme,
nonquasidiagonal `sigma` and `y` with `y^ > 0` on `T_qd(A)` and
`y^(sigma) < 0`, with `pi_sigma(A)''` isomorphic to `R`.  Put
`B = A/J_sigma`, the image `pi_sigma(A)`, with quotient map `q`.

1. `B` is separable, unital, nuclear and prime.  The induced trace `sigma_B`
   is faithful, extreme and not quasidiagonal, and `q_* y` separates it from
   `T_qd(B)`.
2. Either `B` is quasidiagonal, and then `B` is a **prime witness** whose
   separated trace is faithful and extreme; or `B` is not quasidiagonal, and
   then `B` is a separable nuclear algebra with a faithful trace that is not
   quasidiagonal.  The second case is a negative answer to STW IX(1)
   (`stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal`), and `B` is
   outside the UCT class by Tikuisis--White--Winter.
3. If `r_A` is injective (Proposition 3), so is `r_B`.

*Proof.*
- **Nuclear and prime.**  Quotients of nuclear algebras are nuclear.  If `I`
  and `J` are nonzero ideals of `B` with `IJ = 0`, their weak closures are
  nonzero weakly closed ideals of the factor `pi_sigma(A)''` with product `0`.
  But the only nonzero one is the whole factor.
- **The trace.**  `T(B)` is identified with the closed face of `T(A)` of
  traces vanishing on `J_sigma`, so `sigma_B` is extreme.  It is faithful
  because `J_sigma` is its trace kernel.
- **Separation.**  By Lemma 1.3, quasidiagonal traces of `B` pull back to
  quasidiagonal traces of `A`.  So `(q_* y)^ > 0` on `T_qd(B)` and
  `(q_* y)^(sigma_B) = y^(sigma) < 0`.
- **The dichotomy.**  If `B` is quasidiagonal, `T_qd(B)` is nonempty and
  Theorem 1, (b) => (a), makes `q_* y` singular.  If `B` is not
  quasidiagonal, it has the faithful trace `sigma_B`.
- **Part 3.**  This is the quotient clause of Proposition 3. QED

Context, not used above: Moradi--Amini (arXiv:2606.13924v1, Theorem 2.10,
unrefereed preprint; the proof sketch was read in the HTML version) state that
the quasidiagonal traces form a face of `T(A)` for separable `A`.

## 6. Scope

- Theorems 1 and 2 and Propositions 3 and 4 are complete proofs, modulo:
  - the cited literature: Künneth, Connes' uniqueness of `R`, uniqueness of the
    trace on a finite factor, Blackadar--Rordam--Haagerup, TWW/Schafhauser,
    Gabe (Corollary 3.1 and Remark 2.3 only);
  - [HB] Theorem C and (V1).
- None of them constructs a witness.  The hole remains open.
- Proposition 3 reduces it to a more natural statement: a nonquasidiagonal
  trace on a K_0-trace-separating separable unital nuclear quasidiagonal
  algebra, for instance one of real rank zero.  That statement is in general
  stronger than the hole.
- Failed constructions of a separating class from a nonquasidiagonal trace are
  recorded in `notes/qd-nuclear-algebra-with-qd-trace-positiv-swarm-2026-09-16.md`.
