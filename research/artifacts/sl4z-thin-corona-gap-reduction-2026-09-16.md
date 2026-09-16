# A thin relative spectral gap for corona representations of SL_4(Z)

Lane `swarm-sl4z-matricially-stable`, 2026-09-16.  UNREVIEWED.

This artifact proves the implications behind four nodes:

- `sln-z-thin-quasiregular-not-weakly-contained-in-fd` (Theorem B, Sections 2--4);
- `sl4z-thin-gap-from-matricial-stability` (Section 6);
- `sl4z-full-not-mf-from-thin-corona-gap` (Section 7);
- the equivalent forms of the open crux `sl4z-corona-reps-have-thin-relative-spectral-gap`
  (Section 8).

Literature used, with what was actually checked on 2026-09-16:

- [AGS] Aka--Gelander--Soifer, arXiv:1205.1140.  Abstract fetched: "for any n>2 one can
  find a four generated free subgroup of SLn(Z) which is profinitely dense."
- [BV] Bourgain--Varju, arXiv:1006.3365.  Abstract fetched: "Let S be a fixed finite
  symmetric subset of SL_d(Z), and assume that it generates a Zariski-dense subgroup G.
  We show that the Cayley graphs of pi_q(G) with respect to the generating set pi_q(S)
  form a family of expanders".
- Margulis superrigidity and the Bass--Milnor--Serre congruence subgroup property.
  Used only through the established repository claim `sln-z-thin-codense-tau-pair`.
- Property (T) of `SL_n(Z)`, `n >= 3` (Kazhdan 1967), the discrete Cheeger inequality,
  Peter--Weyl for finite groups, and lifting of projections and unitaries from
  `prod_n M_(k_n) / sum_n M_(k_n)`.  These are standard and were not re-read.

## 1. Setup

Fix `n >= 3` and put `Gamma = SL_n(Z)`.  `C*(Gamma)` is the maximal group C*-algebra, with
canonical unitaries `u_g`.  Every unitary representation `rho` of `Gamma` extends uniquely to
`C*(Gamma)`, and we use the same letter for the extension.

- **Thin subgroup.**  `C = <g_1, g_2, g_3, g_4> <= Gamma` is a free subgroup of infinite index
  with `pi_m(C) = SL_n(Z/m)` for every `m >= 1`, as in `sln-z-thin-codense-tau-pair` [AGS].
  `F = (g_1^(+-1), ..., g_4^(+-1))` is its symmetric generating list, `|F| = 8`.
- **Kazhdan set.**  `S` is a finite symmetric generating set of `Gamma`.
- **Matrix corona.**  For a sequence `k = (k_n)` of nonnegative integers,
  `Q_k = prod_n M_(k_n) / sum_n M_(k_n)`, with quotient map `q`.  The norm of `q((y_n))` is
  `limsup_n ||y_n||`.
- **Invariant subspace.**  For a unitary representation `rho` on `H`, `H^Gamma` denotes the
  `Gamma`-fixed vectors, `P_rho` the orthogonal projection onto it, and
  `H^0 = (H^Gamma)^perp`.  Both are `rho(Gamma)`-invariant.

**Two constants.**

1. **(T).**  There is `kappa_S > 0` such that for every unitary representation `rho` of
   `Gamma` and every `xi in H^0`,

   ```text
   sum_(s in S) ||rho(s) xi - xi||^2 >= kappa_S^2 ||xi||^2.              (KS)
   ```

2. **(tau) on congruence quotients.**  There is `kappa > 0` such that for every
   finite-dimensional unitary representation `rho` of `Gamma` and every `xi in H^0`,

   ```text
   sum_(c in F) ||rho(c) xi - xi||^2 >= kappa^2 ||xi||^2.                (KF)
   ```

*Proof of (KF).*
- **Uniform expansion.**  By [BV] and profinite density, the Cayley multigraphs
  `X_m = Cay(SL_n(Z/m), pi_m(F))` have edge expansion at least some `h > 0` for all `m`.
  - Finitely many small `m` are harmless, since each `X_m` is connected: `pi_m(F)`
    generates `pi_m(C) = SL_n(Z/m)`.
  - Using the multiset `pi_m(F)` instead of the set only adds edges.
- **Cheeger.**  The Laplacian `Delta = sum_(c in F) (1 - lambda(c))` on `l^2(SL_n(Z/m))`
  satisfies `<Delta f, f> >= (h^2 / 16) ||f||^2` for `f` orthogonal to the constants
  (degree `8`).  Since `F` is symmetric, `<Delta f, f> = (1/2) sum_c ||lambda(c) f - f||^2`.
  So `sum_c ||lambda(c) f - f||^2 >= (h^2/8) ||f||^2` on `l^2_0`.
- **Irreducibles.**  By Peter--Weyl, every nontrivial irreducible representation of
  `SL_n(Z/m)` is a subrepresentation of `lambda` on `l^2_0(SL_n(Z/m))`.  So (KF) holds on
  it with `kappa^2 = h^2/8`.
- **General finite-dimensional `rho`.**
  - By item 1 of `sln-z-thin-codense-tau-pair`, `rho` factors through some
    `pi_m : Gamma -> SL_n(Z/m)`.  Since `pi_m` is onto, `H^Gamma` is the trivial isotypic
    part.
  - So `H^0` is an orthogonal sum of nontrivial irreducible `SL_n(Z/m)`-summands.  On each
    summand `rho(c)` acts through `pi_m(c)`, and `c` runs over `F`.
  - Summing (KF) over the summands gives (KF) for `rho`.  QED.

**The test element.**  Put

```text
nu = (1/2) (1 + |S|^(-1) sum_(s in S) u_s),
mu = (1/2) (1 + |F|^(-1) sum_(c in F) u_c),
theta = 1 - kappa_S^2 / (4|S|),      epsilon = kappa^2 / (4|F|) = kappa^2 / 32.
```

**Identity (Q).**  For any unitary `u` and vector `xi`,
`Re <u xi, xi> = ||xi||^2 - ||u xi - xi||^2 / 2`.  The lists `S` and `F` are symmetric, so
`rho(nu)` and `rho(mu)` are self-adjoint.  In every unitary representation,

```text
<rho(mu) xi, xi> = ||xi||^2 - (4|F|)^(-1) sum_(c in F) ||rho(c) xi - xi||^2,
<rho(nu) xi, xi> = ||xi||^2 - (4|S|)^(-1) sum_(s in S) ||rho(s) xi - xi||^2.     (Q)
```

In particular `0 <= rho(mu) <= 1` and `0 <= rho(nu) <= 1`.

## 2. The Kazhdan projection (standard; proved here to fix notation)

**Lemma 2.1.**  The powers `nu^N` converge in `C*(Gamma)` to a projection `p`.
- (a) For every unitary representation `rho`, `rho(p) = P_rho`.
- (b) `u_g p = p = p u_g` for all `g in Gamma`, so `p` is central.
- (c) With `x = mu (1 - p)`, the following hold in `C*(Gamma)`:

  ```text
  0 <= x <= mu,     x <= 1 - p,     1 - nu >= (1 - theta)(1 - p).        (INEQ)
  ```

*Proof.*
- **Spectrum of `rho(nu)`.**  Let `rho` be a unitary representation.  `rho(nu)` fixes
  `H^Gamma` pointwise and preserves `H^0`.  By (Q) and (KS), `<rho(nu) xi, xi> <= theta ||xi||^2`
  for `xi in H^0`.  So `rho(nu)` restricted to `H^0` is a positive contraction with spectrum
  in `[0, theta]`, and `||rho(nu)^N - P_rho|| <= theta^N`.
- **Convergence.**  Taking `rho` to be the universal representation, which is isometric on
  `C*(Gamma)`, gives `||nu^N - nu^M|| <= theta^N + theta^M`.  So `p = lim nu^N` exists, and
  `rho(p) = lim rho(nu)^N = P_rho` for every `rho`.  This is (a).  `p` is a projection
  because its image under the universal representation is one.
- **(b).**  `rho(g) P_rho = P_rho`, since `P_rho` projects onto fixed vectors.  Taking adjoints
  at `g^(-1)` gives `P_rho rho(g) = P_rho`.  Apply this to the universal representation.
- **(c).**  It suffices to check the inequalities in every `rho`, since the universal
  representation is faithful.  `rho(p)` commutes with `rho(mu)` by (b).
  - `mu - x = mu p = p mu p >= 0`.
  - `(1 - p) - x = (1 - p)(1 - mu)(1 - p) >= 0`, because `0 <= mu <= 1`.
  - On `H^Gamma` both `1 - rho(nu)` and `(1 - theta)(1 - P_rho)` vanish.  On `H^0` the first
    is `>= 1 - theta` and the second equals `1 - theta`.  Both operators commute with
    `P_rho`.  QED.

## 3. The finite-dimensional gap

**Proposition 3.1.**  `||rho(x)|| <= 1 - epsilon` for every finite-dimensional unitary
representation `rho` of `Gamma`.

*Proof.*
- By Lemma 2.1, `rho(x)` vanishes on `H^Gamma` and equals `rho(mu)` restricted to `H^0`.
  That restriction is positive, so its norm is `sup <rho(mu) xi, xi>` over unit
  `xi in H^0`.
- By (Q) and (KF), `<rho(mu) xi, xi> <= 1 - kappa^2/(4|F|) = 1 - epsilon` for such `xi`.  QED.

This is the inequality `(PSG1)` of `thin-profinite-selected-gap-lemma`, specialised to the
thin pair of `sln-z-thin-codense-tau-pair` and packaged as a single element of `C*(Gamma)`.

## 4. The thin quasi-regular representation, and Theorem B

Let `sigma_C` be the quasi-regular representation of `Gamma` on `l^2(Gamma/C)`.

**Proposition 4.1.**  `||sigma_C(x)|| = 1`.

*Proof.*
- `Gamma` acts transitively on the infinite set `Gamma/C`.  So a `Gamma`-invariant vector of
  `l^2(Gamma/C)` is a constant square-summable function, hence `0`.  Therefore
  `sigma_C(p) = 0` and `sigma_C(x) = sigma_C(mu)`.
- The coset vector `delta_C` satisfies `sigma_C(c) delta_C = delta_(cC) = delta_C` for
  `c in C`.  So `sigma_C(mu) delta_C = delta_C`.
- `||sigma_C(mu)|| <= 1`.  QED.

**Theorem B.**  With `n >= 3` and `C`, `F`, `p`, `mu`, `x` as above:
1. `||x||_FD := sup_rho ||rho(x)|| <= 1 - epsilon`, the supremum taken over finite-dimensional
   unitary representations;
2. `||sigma_C(x)|| = 1`, hence `||x|| = 1` in `C*(Gamma)`.

Consequently:
- (i) `sigma_C` is not weakly contained in the set of finite-dimensional unitary
  representations of `Gamma`.  More generally, no representation `pi` with
  `sigma_C prec pi` is.
- (ii) `C*(SL_n(Z))` is not residually finite-dimensional.

*Proof.*
- Items 1 and 2 are Propositions 3.1 and 4.1.  `||x|| >= ||sigma_C(x)||` because the maximal
  norm dominates every representation.  `||x|| <= 1` because `0 <= x <= mu <= 1`.
- **(i).**  Weak containment `pi prec S` is equivalent to `||pi(y)|| <= sup_(rho in S) ||rho(y)||`
  for all `y in C*(Gamma)` (Dixmier, Section 3.4; Bekka--de la Harpe--Valette, Appendix F;
  standard, not re-read).  If `sigma_C prec pi prec FD`, then `y = x` gives
  `1 <= 1 - epsilon`.
- **(ii).**  If `C*(Gamma)` were RFD, its finite-dimensional *-representations would be
  isometric in the supremum.
  - Their nondegenerate parts are the finite-dimensional unitary representations of
    `Gamma`, and the degenerate part contributes `0`.
  - So `||x|| = ||x||_FD <= 1 - epsilon`, contradicting `||x|| = 1`.  QED.

*Provenance.*
- Non-RFD of `C*(SL_n(Z))`, `n >= 3`, is attributed to Bekka (Forum Math. 11 (1999)).  That
  paper was not re-read, so item (ii) is offered as an independent proof, not as new.
- For `n = 3` and the explicit pair `<a,b>`, statement (i) for the congruence-free part
  `pi_FD^0` already appears as `(THD2)` of `thin-hnn-regular-selected-module-is-profinite-discontinuous`.
- The new content is the single universal element `x`.  It is a fixed element of
  `C*(Gamma)`, not a sequence: compare `y_N` in `thin-leak-has-universal-fd-null-laplacian-witness`,
  which does not converge in `C*(Gamma)` because `C` is free.  Section 7 uses exactly this.

## 5. Three corona lemmas

**Lemma 5.1 (corners).**  Let `e in Q_k` be a projection.
- There are projections `P_n in M_(k_n)` with `q((P_n)) = e`.
- With `r_n = rank P_n`, `e Q_k e` is isomorphic to `Q_r`.
- Hence every *-homomorphism `psi : A -> Q_k` from a unital C*-algebra is, after
  corestriction to `psi(1) Q_k psi(1)`, a unital *-homomorphism `A -> Q_r` with the same norms.

*Proof.*
- **Lifting `e`.**  Lift `e` to self-adjoint `b_n`.  Then `||b_n^2 - b_n|| -> 0`, so the
  spectrum of `b_n` lies within `eta_n -> 0` of `{0,1}` for large `n`.  Let `P_n` be the
  spectral projection of `b_n` for `[1/2, infinity)`.  Then `||P_n - b_n|| <= eta_n`, so
  `q((P_n)) = e`.
- **The corner.**  Put `P = (P_n)`.
  - `P (prod M_(k_n)) P = prod P_n M_(k_n) P_n`, which is isomorphic to `prod M_(r_n)`.
  - `y -> q(y)` maps it onto `e Q_k e`, since `q(P y P) = e q(y) e`.
  - The kernel is `P(prod)P intersect sum M_(k_n) = P (sum M_(k_n)) P`, which corresponds to
    `sum M_(r_n)`.  So `e Q_k e` is isomorphic to `Q_r`.
- **Corestriction.**  `psi(y) = psi(1) psi(y) psi(1)`, so `psi` maps unitally into
  `psi(1) Q_k psi(1)`.  QED.

**Lemma 5.2 (asymptotic homomorphisms and corona representations).**
- (a) Let `pi : C*(Gamma) -> Q_k` be a unital *-homomorphism, and discard the indices with
  `k_n = 0` (this does not change `Q_k`).  Then there are unitaries `phi_n(g) in U(k_n)` with
  `q((phi_n(g))_n) = pi(u_g)` for every `g`.  Any such choice satisfies
  `||phi_n(gh) - phi_n(g) phi_n(h)|| -> 0` for all `g, h`.
- (b) Conversely, let `phi_n : Gamma -> U(k_n)`, `k_n >= 1`, satisfy
  `||phi_n(gh) - phi_n(g) phi_n(h)|| -> 0` for all `g, h`.  Then
  `g -> q((phi_n(g))_n)` is a group homomorphism into `U(Q_k)`.  It extends to a unital
  *-homomorphism `pi : C*(Gamma) -> Q_k`.

*Proof.*
- **(a) Lifting unitaries.**  A unitary `w in Q_k` lifts to `(b_n)` with
  `||b_n^* b_n - 1|| -> 0` and `||b_n b_n^* - 1|| -> 0`.  The unitary polar part `w_n` of
  `b_n` satisfies `||w_n - b_n|| <= ||(b_n^* b_n)^(1/2) - 1|| -> 0`.  For the finitely many
  `n` where this is not small, choose `w_n` arbitrary.
- **(a) Defect.**  `q((phi_n(gh) - phi_n(g) phi_n(h))_n) = pi(u_gh) - pi(u_g) pi(u_h) = 0`.
- **(b).**  `q((phi_n(g))) q((phi_n(h))) = q((phi_n(g) phi_n(h))) = q((phi_n(gh)))`, and
  `q((phi_n(g)))` is unitary.  A group homomorphism sends `e` to `1`.  Now apply the
  universal property of `C*(Gamma)`.  QED.

**Lemma 5.3 (stable groups have product corona representations).**  Suppose `Gamma` is
point-norm matricially stable.
- Definition, as in `sl4z-matricially-stable`: for every `phi_n` as in 5.2(b) there are
  homomorphisms `rho_n : Gamma -> U(k_n)` with `||phi_n(g) - rho_n(g)|| -> 0` for every `g`.
- Conclusion: every unital *-homomorphism `pi : C*(Gamma) -> Q_k` has the form
  `pi(y) = q((rho_n(y))_n)` for genuine finite-dimensional unitary representations `rho_n`.
  In particular

  ```text
  ||pi(y)|| = limsup_n ||rho_n(y)|| <= ||y||_FD     for all y in C*(Gamma).       (PROD)
  ```

*Proof.*
- Take lifts `phi_n` by 5.2(a) and correct them to `rho_n`.
- Each `rho_n` extends to a *-homomorphism `C*(Gamma) -> M_(k_n)` of norm `<= 1`.  So
  `R(y) = (rho_n(y))_n` is a *-homomorphism `C*(Gamma) -> prod M_(k_n)`.
- `q o R` and `pi` are *-homomorphisms that agree on each `u_g`, since
  `q((rho_n(g))) = q((phi_n(g)))`.  So they agree on `C*(Gamma)`.  QED.

(PROD) says: under stability, every corona representation factors through the maximal
RFD quotient `C*_FD(Gamma)`, the completion of `C[Gamma]` in `||.||_FD`.

## 6. Stability implies the thin corona gap

From here on `n = 4`, so `Gamma = SL_4(Z)`.  The crux is

> **(C)** `sl4z-corona-reps-have-thin-relative-spectral-gap`: every unital *-homomorphism
> `pi : C*(SL_4(Z)) -> Q_k`, for every `k`, satisfies `||pi(x)|| < 1`.

**Theorem 6.1.**  If `SL_4(Z)` is point-norm matricially stable, then (C) holds.  Moreover,
`||pi(x)|| <= 1 - epsilon` with the finite-dimensional constant of Proposition 3.1.

*Proof.*  By Lemma 5.3, `||pi(x)|| = limsup_n ||rho_n(x)||` for genuine finite-dimensional
`rho_n`.  Each term is `<= 1 - epsilon` by Proposition 3.1.  QED.

The same proof shows that (C) holds for every corona representation of the form
`q o (rho_n)_n`, whether or not stability holds.  This includes:
- the congruence models;
- every MF embedding of the *reduced* algebra.  If `iota : C*_r(Gamma) -> Q_k` is
  isometric, then `||iota(lambda(x))|| = ||lambda(x)|| <= ||x||_FD <= 1 - epsilon`.  Here
  `lambda prec FD`, because `1_(Gamma(N)) -> delta_e` pointwise, with `Gamma(N)` the
  principal congruence subgroups.

So (C) is consistent with a positive answer to the MF question for `C*_r(SL_4(Z))`.  It does
not bear on the root `sl4z-reduced-cstar-is-not-mf`.

## 7. The thin corona gap implies that C*(SL_4(Z)) is not MF

**Theorem 7.1.**  Assume (C).  Let `psi : C*(SL_4(Z)) -> Q_k` be a *-homomorphism with
`||psi(y)|| >= ||sigma_C(y)||` for all `y`, i.e. `sigma_C prec psi`.  Then we get a
contradiction.  In particular:
- (i) `C*(SL_4(Z))` is not MF;
- (ii) `C*_(sigma_C)(SL_4(Z)) = sigma_C(C*(SL_4(Z)))` is not MF;
- (iii) no C*-completion of `C[SL_4(Z)]` whose norm dominates `||sigma_C(.)||` is MF.

*Proof.*
- **Corner.**  By Lemma 5.1, `psi` corestricts to a unital *-homomorphism `psi' : C*(Gamma) -> Q_r`
  with `||psi'(y)|| = ||psi(y)||`.
- **Contradiction.**  By Proposition 4.1, `||psi'(x)|| >= ||sigma_C(x)|| = 1`, contradicting (C).
- **(i).**  An injective `iota : C*(Gamma) -> Q_k` is isometric, and `||y|| >= ||sigma_C(y)||`.
- **(ii).**  For an injective `iota' : C*_(sigma_C)(Gamma) -> Q_k`, put `psi = iota' o sigma_C`.
- **(iii)** is the common form of (i) and (ii).  QED.

*Remarks.*
1. **Overgroups.**  For a group `Lambda >= SL_4(Z)`, the canonical map
   `C*(SL_4(Z)) -> C*(Lambda)` is injective (restriction of induced representations; standard,
   not re-read).  MF passes to C*-subalgebras, so under (C) no `C*(Lambda)` is MF.
2. **Refutation criterion.**  Theorems 6.1 and 7.1 together say: *any MF model of
   `C*(SL_4(Z))` or of `C*_(sigma_C)(SL_4(Z))` refutes point-norm matricial stability of
   `SL_4(Z)`.*  More economically, any corona representation of `C*(SL_4(Z))` with
   `||pi(x)|| = 1` refutes it.
3. **Two cruxes, opposite behaviour.**  The committed crux
   `sl4z-corona-representations-have-block-sl2-norm-four` behaves oppositely to (C).
   - It *fails* on MF embeddings of `C*_r` and *holds* on faithful representations of
     `C*(Gamma)`, since the trivial representation is weakly contained.
   - (C) *holds* on MF embeddings of `C*_r` and *fails* on faithful representations of
     `C*(Gamma)`.

   Stability implies both.

## 8. Equivalent forms of the crux

Terminology.
- A *corona representation* is a unital *-homomorphism `pi : C*(Gamma) -> Q_k` with all
  `k_n >= 1`.  By Lemma 5.1 and the remark in Lemma 5.2(a), nothing is lost by requiring
  `k_n >= 1`.
- A *Hilbert space realization* of `pi` is `sigma o pi` for a unital representation
  `sigma : Q_k -> B(H)`.  It is a unitary representation of `Gamma`, so Lemma 2.1(a) applies
  to it.

### 8.1 Vector form

**Proposition 8.1.**  Let `rho` be a unitary representation of `Gamma` on `H`, and let
`0 <= t <= 1`.  Then `||rho(x)|| <= t` if and only if, for every `xi in H`,

```text
(1 - t) ||(1 - P_rho) xi||^2  <=  (4|F|)^(-1) sum_(c in F) ||rho(c) xi - xi||^2.      (V_t)
```

*Proof.*
- Write `xi_1 = P_rho xi` and `xi_0 = (1 - P_rho) xi`.  Since `rho(c) xi_1 = xi_1`, we have
  `rho(c) xi - xi = rho(c) xi_0 - xi_0`.
- By Lemma 2.1, `rho(x) = (1 - P_rho) rho(mu) (1 - P_rho) >= 0`.  So `||rho(x)|| <= t` iff
  `<rho(x) xi, xi> <= t ||xi||^2` for all `xi`.
- By (Q), `<rho(x) xi, xi> = <rho(mu) xi_0, xi_0> = ||xi_0||^2 - (4|F|)^(-1) sum_c ||rho(c) xi - xi||^2`.
- **(V_t) for all `xi` implies the norm bound.**  The last expression is at most
  `t ||xi_0||^2 <= t ||xi||^2`.
- **The norm bound implies (V_t).**  Apply the bound at `xi_0`.  Both sides of (V_t) are the
  same at `xi` and at `xi_0`.  QED.

**Corollary 8.2 (fixed-vector form).**  The following are equivalent.
- (C).
- (C_fix): for every corona representation `pi` and every Hilbert space realization
  `sigma o pi`, every `C`-invariant vector is `Gamma`-invariant.

*Proof.*
- **(C) implies (C_fix).**  If `||pi(x)|| = t < 1`, then `||sigma(pi(x))|| <= t`.  Proposition 8.1
  gives `(1 - t) ||(1 - P) xi||^2 <= 0` for `C`-invariant `xi`.
- **(C_fix) implies (C).**
  - Suppose `||pi(x)|| = 1`.  Since `pi(x) >= 0`, some state `omega` of `Q_k` has
    `omega(pi(x)) = 1`.  Let `(sigma, H, xi)` be its GNS triple.
  - From `x <= mu <= 1` (INEQ) we get `<sigma pi(mu) xi, xi> = 1`.  By (Q), `xi` is fixed by
    every `c in F`, hence by `C`.
  - From `x <= 1 - p` we get `||sigma pi(p) xi||^2 = omega(pi(p)) = 0`.  By Lemma 2.1(a)
    `sigma pi(p)` projects onto the `Gamma`-invariant vectors.  So the unit vector `xi` is
    `C`-invariant but has no `Gamma`-invariant component, contradicting (C_fix).  QED.

So (C) is a *thin relative property (T) for corona representations*: the pair `(Gamma, C)`
is not a relative (T) pair, as `sigma_C` shows, but (C) asks that it behave like one on
Hilbert space realizations of matrix corona representations.

**State picture.**
- (C) fails iff some state `omega o pi` of `C*(Gamma)`, with `pi` a corona representation
  and `omega` a state of `Q_k`, has `omega(pi(u_c)) = 1` for `c in F` and `omega(pi(p)) = 0`.
- The forward direction is the proof above.  Conversely, let `xi` be the GNS vector of such
  an `omega`.  Then `sigma pi(u_c) xi = xi` for `c in F`, because `<sigma pi(u_c) xi, xi> = 1`
  for a unitary and a unit vector.  Also `sigma pi(p) xi = 0`.  Since `p` is central,
  `x = (1 - p) mu (1 - p)`, so `<sigma pi(x) xi, xi> = <sigma pi(mu) xi, xi> = 1` and
  `||pi(x)|| = 1`.

### 8.2 Finite robust form

For a finite set `E` of `Gamma` and a map `phi : Gamma -> U(k)`, put
`def_E(phi) = max_(g,h in E) ||phi(gh) - phi(g) phi(h)||` (operator norm).  For `eta > 0`
consider:

> **(b_eta)** There are a finite set `E` of `Gamma` and `delta > 0` such that, for every
> `k >= 1`, every map `phi : Gamma -> U(k)` with `def_E(phi) < delta`, and every unit vector
> `v in C^k`,
>
> ```text
> sum_(c in F) ||phi(c) v - v||^2 < delta   implies   sum_(s in S) ||phi(s) v - v||^2 < eta.
> ```

**Lemma 8.3 (lifting inequalities).**
- Let `a <= b` be self-adjoint elements of `Q_k`, and let `(A_n)`, `(B_n)` be self-adjoint lifts.
- Then there are `e_n -> 0` with `<A_n v, v> <= <B_n v, v> + e_n` for every `n` and every
  unit vector `v in C^(k_n)`.

*Proof.*
- Put `D_n = (B_n - A_n)_+`.  Functional calculus commutes with `q`, so
  `q((D_n)) = (b - a)_+ = b - a = q((B_n - A_n))`.
- Hence `e_n = ||B_n - A_n - D_n|| -> 0`, and `<(B_n - A_n) v, v> >= <D_n v, v> - e_n >= -e_n`.
  QED.

**Proposition 8.4.**  The following are equivalent.
- (a) (C).
- (b) (b_eta) holds for every `eta > 0`.
- (b') (b_eta) holds for some `eta` with `0 < eta < kappa_S^2`.

*Proof.*  (b) implies (b') trivially.

**(a) implies (b).**
- **Setup.**  Suppose (b_eta) fails for some `eta > 0`.  Enumerate `Gamma`, let `E_n` be its
  first `n` elements, and put `delta_n = 1/n`.  We get maps `phi_n : Gamma -> U(k_n)` and unit
  vectors `v_n` with
  - `def_(E_n)(phi_n) < 1/n`,
  - `sum_c ||phi_n(c) v_n - v_n||^2 < 1/n`,
  - `sum_s ||phi_n(s) v_n - v_n||^2 >= eta`.
- **Corona representation.**  For fixed `g, h`, the defect `||phi_n(gh) - phi_n(g) phi_n(h)||`
  tends to `0`.  So Lemma 5.2(b) gives a corona representation `pi` with
  `pi(u_g) = q((phi_n(g))_n)`.
- **A state.**  Fix a free ultrafilter `U` on `N`.  `omega((y_n)) = lim_U <y_n v_n, v_n>` is a
  state of `prod M_(k_n)` that vanishes on `sum M_(k_n)`, so it is a state of `Q_k`.  Let
  `(sigma, H, xi)` be its GNS triple.
- **Invariance.**  For `g in Gamma`,

  ```text
  ||sigma pi(u_g) xi - xi||^2 = omega(pi(2 - u_g - u_g^*)) = lim_U ||phi_n(g) v_n - v_n||^2.
  ```

  So `xi` is fixed by every `c in F`, hence is `C`-invariant.  But
  `sum_s ||sigma pi(u_s) xi - xi||^2 >= eta > 0`, so `xi` is not `Gamma`-invariant.  This
  contradicts (C_fix), which is equivalent to (a) by Corollary 8.2.

**(b') implies (a).**  Suppose `pi` is a corona representation with `||pi(x)|| = 1`, and let
`E`, `delta` and `eta < kappa_S^2` be given.
- **Lifts.**
  - By Lemma 5.2(a), choose unitary lifts `phi_n(g)` of `pi(u_g)`.  Then
    `def_E(phi_n) -> 0` for every finite `E`.
  - Put `M_n = (1/2)(1 + (2|F|)^(-1) sum_c (phi_n(c) + phi_n(c)^*))`, and define `N_n` the same
    way from `S`.  Since `F` and `S` are symmetric, these are self-adjoint lifts of `pi(mu)`
    and `pi(nu)`.
  - Let `P_n` be projections lifting `pi(p)` (Lemma 5.1).
  - Let `X_n = (Y_n)_+` for any self-adjoint lift `(Y_n)` of `pi(x) >= 0`.  Then
    `q((X_n)) = pi(x)` and `limsup_n ||X_n|| = 1`.
- **Exact matrix identities.**  Because each `phi_n(g)` is unitary, (Q) holds for every unit
  vector `v`:

  ```text
  <M_n v, v> = 1 - (4|F|)^(-1) sum_c ||phi_n(c) v - v||^2,
  <N_n v, v> = 1 - (4|S|)^(-1) sum_s ||phi_n(s) v - v||^2.
  ```

- **Lifted (INEQ).**  Apply `pi` to (INEQ) and use Lemma 8.3.  There are `e_n -> 0` such
  that for all unit `v`:

  ```text
  <X_n v, v> <= <M_n v, v> + e_n,
  <X_n v, v> <= 1 - <P_n v, v> + e_n,
  1 - <N_n v, v> >= (1 - theta)(1 - <P_n v, v>) - e_n.
  ```

- **Top eigenvectors.**  Choose `n_j -> infinity` with `t_j = ||X_(n_j)|| -> 1`, and unit
  vectors `v_j` with `X_(n_j) v_j = t_j v_j`.  With `n = n_j` and `v = v_j`:
  - `sum_c ||phi_n(c) v - v||^2 = 4|F|(1 - <M_n v, v>) <= 4|F|(1 - t_j + e_n) -> 0`;
  - `1 - <P_n v, v> >= t_j - e_n -> 1`;
  - `sum_s ||phi_n(s) v - v||^2 = 4|S|(1 - <N_n v, v>) >= 4|S|((1 - theta)(t_j - e_n) - e_n) -> 4|S|(1 - theta) = kappa_S^2`.
- **Conclusion.**  For large `j`, `phi_(n_j)` and `v_j` violate (b_eta) for the given `E` and
  `delta`.  Since `E` and `delta` were arbitrary, (b') fails.  QED.

**Corollary 8.5 (automatic uniformity).**  Assume (C), and take `E`, `delta` from (b_eta)
with `eta = kappa_S^2 / 2`.  Then every corona representation satisfies

```text
||pi(x)|| <= t_0 := max(1 - delta/(4|F|), 1/2) < 1.
```

*Proof.*
- Let `t = ||pi(x)||` and suppose `t > 1 - delta/(4|F|)`.  Take `n_j`, `v_j` as in the proof
  above, now with `t_j -> t`.
- For large `j`: `def_E(phi_(n_j)) < delta`, and `sum_c ||phi(c) v_j - v_j||^2 <= 4|F|(1 - t_j + e) < delta`.
- So (b_eta) gives `sum_s ||phi(s) v_j - v_j||^2 < kappa_S^2/2`, i.e.
  `1 - <N v_j, v_j> < (1 - theta)/2`.
- Combined with `1 - <N v_j, v_j> >= (1 - theta)(t_j - e) - e`, letting `j -> infinity` gives
  `t <= 1/2`.  QED.

Under stability Theorem 6.1 gives the explicit value `t_0 = 1 - epsilon`.  Under (C) alone,
`t_0` depends on the unknown modulus in (b).

**Remark 8.6 (what a proof of (C) must use).**
1. **Genuine representations.**  For a genuine finite-dimensional representation `rho` and
   any unit `v`, (KF) gives `kappa^2 ||(1 - P) v||^2 <= sum_c ||rho(c) v - v||^2`.  Hence
   `sum_s ||rho(s) v - v||^2 <= 4|S| ||(1 - P) v||^2 <= (4|S|/kappa^2) sum_c ||rho(c) v - v||^2`.
   So (b_eta) holds on genuine representations, with `delta = eta kappa^2 / (4|S|)` and any
   `E`.  (b) asks that this inequality survive, qualitatively and uniformly in the
   dimension, under small operator-norm defect on one fixed finite set.
2. **No universal certificate.**  (C_fix) fails for the genuine infinite-dimensional
   representation `sigma_C`, because of `delta_C`.  So no inequality valid in all unitary
   representations of `Gamma`, such as a sum-of-squares certificate in `C*(Gamma)`, can
   prove (C).  A proof must use that the representation comes from matrices.  This is the
   same firewall as for the Hilbert--Schmidt transfer modulus in
   `thin-sln-robust-relative-commutant-transfer`.
3. **Restriction to `C`.**  `C` is free, and free groups are point-norm matricially stable:
   the lifts `phi_n(g_i)` of the four generators define genuine representations `psi_n` of
   `C` with `pi|_C = q o (psi_n)`.  After cutting down by `1 - pi(p)`, (C) says:
   *`1_C` is not weakly contained in `(1 - pi(p)) pi|_C` in any Hilbert space realization.*
   The difficulty is entirely in the interaction of the free correction on `C` with the
   rest of `Gamma`.

## 9. Relation with the Hilbert--Schmidt transfer program

Write `||T||_2 = (tr(T^* T)/k)^(1/2)` for the normalized Hilbert--Schmidt norm on `M_k`.

**Proposition 9.1 (operator-norm commutant transfer).**  Assume (C).  For every `eta > 0`
there are a finite set `E` of `Gamma` and `delta > 0` with the following property.  Let
`k >= 1`, let `phi : Gamma -> U(k)` satisfy `def_E(phi) < delta`, and let `T in M_k` have
`||T||_2 = 1`.  Then

```text
sum_(c in F) ||phi(c) T - T phi(c)||_2^2 < delta   implies   sum_(s in S) ||phi(s) T - T phi(s)||_2^2 < eta.
```

*Proof.*
- **The conjugation map.**  `L^2(M_k, tr/k)` is a `k^2`-dimensional Hilbert space.
  `Phi(g) T = phi(g) T phi(g)^*` defines unitaries on it, and
  `||Phi(g) T - T||_2 = ||phi(g) T - T phi(g)||_2`.
- **Defect.**  Using `||A T B||_2 <= ||A|| ||T||_2 ||B||`,

  ```text
  ||phi(gh) T phi(gh)^* - phi(g) phi(h) T phi(h)^* phi(g)^*||_2 <= 2 ||phi(gh) - phi(g) phi(h)|| ||T||_2.
  ```

  So `def_E(Phi) <= 2 def_E(phi)`.
- **Apply (b_eta).**  Proposition 8.4(b) gives `E` and `delta'` for `eta`, valid in every
  dimension, in particular `k^2`.  Take `delta = delta'/2`.  QED.

*Consequence.*  Let `r in Gamma` be a word of length `L` in `S`, and let `E` also contain the
prefixes of that word.  For unitary `v` with `||[v, phi(c)] - 1||_2` small for `c in F`,
Proposition 9.1 and the triangle inequality give

```text
||[v, phi(r)] - 1||_2 <= sum_i ||[v, phi(s_i)] - 1||_2 + 2 L def_E(phi),
```

which is small.  Tuples with small operator-norm relator defect give maps `phi` with small
`def_E` (fix normal-form words and use van Kampen diagrams).  So (C) implies the
*operator-norm-hypothesis case* of the transfer modulus `(TRC1)` of
`thin-sln-robust-relative-commutant-transfer`, for `Gamma = SL_4(Z)` and the thin pair of
`sln-z-thin-codense-tau-pair`.

*Comparison.*
- `(TRC1)` assumes only Hilbert--Schmidt relator defect.  So `(TRC1)` for `SL_4(Z)` also
  implies this operator-norm-hypothesis case.  The two programs meet there, but no
  implication between (C) and `(TRC1)` is derived.
- (b) concerns *single vectors* of almost-representations.  `(TRC1)` concerns vectors of the
  conjugation module weighted by the normalized trace, in which rank-one test vectors have
  vanishing weight.  So `(TRC1)` does not obviously give (b).
- Proposition 9.1 gives only normalized-trace conclusions.  An operator-norm corona
  commutant statement such as `pi(C)' cap Q_k = pi(Gamma)' cap Q_k` does not follow from
  it.
  - Such a statement would need (C_fix) for the conjugation representation on
    `H (x) conj(H)` of a Hilbert space realization.  That representation factors through
    `Q_k (x)_min Q_k^op`.
  - The conjugation corona representation `q o (phi_n (x) conj(phi_n))` lands in `Q_(k^2)`
    through the *-homomorphism `Q_k (x)_max Q_k^op -> Q_(k^2)`.
  - Whether (C) transfers across this passage was not settled.

## 10. What is not established

1. **(C) itself is open.**  It follows from stability (Theorem 6.1).  It is not known to be
   strictly weaker, and the converse is not claimed.
2. **(D) is open.**  (D) is `sl4z-full-cstar-is-not-mf`: `C*(SL_4(Z))` is not MF.
   - The composite "stability implies (D)" is immediate from Lemma 5.3 and Theorem B(ii),
     since an MF embedding factoring through `C*_FD` would make `C*(Gamma)` RFD.
   - What (C) adds is a single element and a single inequality that suffice for (D) and for
     non-MF of `C*_(sigma_C)(Gamma)`, without correcting any almost-representation.
3. **No refutation of stability.**  The refutation criterion of Section 7 needs a corona
   representation with `||pi(x)|| = 1`, for example an MF model of `C*_(sigma_C)(SL_4(Z))`.
   None is known to this lane.
   - Constructing one by rounding permutation almost-actions of `Gamma` on `Gamma/C` is
     impossible.  Distinct permutation matrices are at operator-norm distance at least
     `sqrt(2)`, and `Gamma` is finitely presented.  So an operator-norm asymptotic
     homomorphism by permutation matrices is eventually a genuine finite action.
   - Such an action factors through a congruence quotient, where `C` is co-dense.  So its
     corona representation has product form, and (C) holds on it by Proposition 3.1.
4. **Independence from the block-`SL_2` crux.**  `sl4z-corona-representations-have-block-sl2-norm-four`
   (for `C*_r`) and (C) (for `C*`) are independent as far as this lane knows.  Remark 3 after
   Theorem 7.1 explains why neither can be read off from the other on the standard models.
5. **Constants.**  `kappa` comes from [BV] and is not explicit, and `kappa_S` from property
   (T) was not computed.  None of the statements above needs explicit values.
