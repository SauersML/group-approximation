# Wave-3 linear verification (lane w3-vf-linear)

Lane `w3-vf-linear`, 2026-09-12. Independent re-derivations for the wave-3 lanes `w3-corner-*`,
`w3-kap-*`, `w3-gate-*` and for `gk-gate-compress`. Each section names the landing, the claims checked,
and the verdict. A verdict line citing this artifact is added to each proof route checked.

## 1. Compressor calculus and the scalar calibration (gk-gate-compress; 4afde801d, f4cbbb4ea, corrected 53fcaae60)

### 1.1 `compressors-conjugate-leak-free-root-pairs`: PASS in the corrected form

Re-derived from the unit `c'` of artifact Section 1:
`c'(e_2 r) = e_2 s_0 r`, `c'(e_3 r) = e_3 s_0 r`, `c'(e_1 v) = e_1 t_1 t_1 v + e_2 s_1 t_0 v + e_3 s_1 t_0 t_1 v`.

* **Unit.** `v -> (t_1 t_1 v, t_0 v, t_0 t_1 v)` is an isomorphism `R -> R^3` with inverse
  `(x, y, z) -> s_1 s_1 x + s_0 y + s_1 s_0 z`. Both composites were checked with `t_i s_j = delta_ij`
  and `s_0 t_0 + s_1 t_1 = 1`. Surjectivity and injectivity of `c'` then follow from `R = s_0 R ⊕ s_1 R`.
* **Kernel of the conjugated nilpotent.** `e_1 w = c'(e_1 s_1 s_1 w)`, `e_2 s_1 y = c'(e_1 s_0 y)` and
  `e_3 s_1 y = c'(e_1 s_1 s_0 y)`. So `c' x_12(a) c'^-1 - 1` kills columns 1 and 3, and column 2 is
  `(t_1 t_1 a t_0, s_1 t_0 a t_0, s_1 t_0 t_1 a t_0)`.
* **Leak-free set.** The two leak entries vanish iff `t_0 a = 0` and `t_0 t_1 a = 0` (cancel `s_1` by
  `t_1`, then multiply by `s_0` on the right), iff `a = s_1 s_1 t_1 t_1 a`. So the set is `s_1 s_1 R`, and
  the surviving entry is `a'' t_0`.
* **The 23 root.** `c' x_23(b) c'^-1 = x_23(s_0 b t_0)`, by the same kernel computation.
* **The `c` half.** Spot-checked column 2 of `c x_12(a) c^-1 - 1` (`e_2 s_1 y = c(e_3 s_1 s_0 y)`): it is
  `x_12(s_0 a t_0)`, in agreement with `gk-vf-linear` Section 48.

The claim node at tip carries exactly the corrected `c'` half. Nothing downstream consumed the false
first version.

### 1.2 `scalar-two-root-rank-data-cannot-force-the-identity`: PASS

* **(i) Conjugation.** If `g` conjugates the pair `(x_12(a), x_23(b))` to `(x_12(a'), x_23(b'))`, then
  `sigma(g)` conjugates `n_23(b) n_12(a)` to `n_23(b') n_12(a')`, so the ranks agree.
* **(ii) Subadditivity.** In characteristic two `x_12(a)^2 = 1`, so `X^2 = 0`, and the root subgroup is
  abelian, so `n_12(a+a') = X + X' + X X'` with `X`, `X'` commuting. Then
  `Y n_12(a+a') = Y X (1 + X') + Y X'`. In `b`: `n_23(b+b') X = Y X + (1 + Y) Y' X`.
* **(iii)** is immediate, since `n(0) = 0`.
* **Calibration.** `eps [a != 0][b != 0]`:
  * satisfies (i), because conjugation preserves nontriviality of root elements, and `x_ab(a) = 1` iff
    `a = 0`;
  * satisfies (ii), because `a + a' != 0` forces `a != 0` or `a' != 0`;
  * satisfies (iii) trivially.
* **Lemma 4.**
  * `R t_1 t_1` contains no unit: `b s_0 = 0`.
  * The outputs `s_0 a t_0`, `s_0 b'`, `a'' t_0` and `s_0 b t_0` are one-sided zero divisors, killed by
    `s_1` or `t_1`.
  * Diagonal unit moves `diag(g_1, g_2, g_3)` give `delta(u, v) = delta(1,1)` for units `u`, `v`.
  * The swap unit gives `delta(e_0, 1) = delta(e_1, 1)`.

Scope as stated: the no-go covers arguments using only (i)–(iii). It does not cover operator identities
such as the defect factorization.

## 2. Twisted rank models kill cyclic corner witnesses (w3-corner-f4; c2155a49c1)

### 2.1 `twisted-rank-models-kill-visible-cyclic-corner-witnesses` (Theorem 2.1): PASS

* **Hypotheses used.**
  * `m | q − 1` gives a primitive `m`-th root `zeta` in `F_q`.
  * `p ∤ m` makes `1/m` exist.
  * `p ∤ q − 1` makes the inclusion-character idempotent `eps_iota = (1/(q−1)) sum_z z^-1 [z]` exist.
* **The twist.** `g = sum_i s_(i+1) t_i` and `delta = sum_i zeta^i s_i t_i` give `delta g = zeta g delta`,
  and `delta^-1 = sum_i zeta^-i s_i t_i`. In `F_q[Gamma]` this reads `[delta][g^k][delta]^-1 = [zeta^k g^k]`.
  Multiplying by `eps_iota`, on which `[z]` acts by `z`, gives `eps_iota [zeta^k g^k] = zeta^k eps_iota [g^k]`.
  So conjugation by `[delta]` shifts the character of each isotypic idempotent `e_psi` by a generator of
  the dual of `Z/m`, and permutes the `m` of them cyclically.
* **Ranks.** `sigmabar` is the linear extension of a group homomorphism into units, hence an algebra map.
  The images `sigmabar(e_psi)` are orthogonal idempotents, pairwise conjugate by powers of `sigma(delta)`,
  summing to `sigmabar(eps_iota)`. Sylvester rank functions are additive on orthogonal idempotents and
  invariant under unit conjugation, so `r(sigmabar(eps_iota)) = m · r(sigmabar(e_1))`.
* **No witness.** `c' e_1 b' = eps_iota` gives `r(sigmabar(eps_iota)) <= r(sigmabar(e_1))`. That forces
  `r(sigmabar(eps_iota)) = 0`, hence `sigmabar(eps_iota) = 0` by positivity on idempotents, which is the
  contradiction.
* **State.** `s([P]) = r(M_n(sigmabar)(P)) / r(sigmabar(eps_iota))` is additive, invariant under
  equivalence, nonnegative, and normalized at `[eps_iota]`.
* **Specialization at (3,2,2).** `g = w`, `delta = s_0 t_0 − s_1 t_1 = d`,
  `eps_iota = 2(1 − [z]) = eps_-` and `e_1 = eps_- · 2(1 + [w])`. This is the verified
  `anti-central-rank-models-kill-ternary-corner-witnesses` (`gk-vf-linear` Section 46).
* **Support filter.** A finite-dimensional representation `rho` over a field containing `F_q`, with the
  normalized matrix rank, sends `eps_iota` to the projection onto the vectors on which every scalar acts
  by itself. So it has no such vector.

### 2.2 Routes from the binary cyclic corner: PASS

* **`binary-cyclic-corner-fullness-gives-kaplansky-failure`.**
  * `e = 1 + [g] + [g^2]` is idempotent in `F_2[R^x]`: squaring in characteristic two gives
    `1 + [g^2] + [g^4] = e`.
  * `alpha = c e`, `beta = e b` give `alpha beta = c e b = 1`.
  * If `beta alpha = 1`, then `e = e beta alpha = beta alpha = 1`, so `[g] = [g^2]`, which is false
    since `g` has order 3.
* **`binary-cyclic-corner-ascends-to-quaternary-twisted-corner`.**
  * `R^x <= L_(F_4)(1,2)^x`, and `eps_iota = [1] + omega^2 [omega] + omega [omega^2]` is a central
    idempotent, since `1/3 = 1`.
  * `x -> x eps_iota` is a unital ring map into the visible factor and sends `e` to `e_1`.
  * `(4,2,3)` is admissible: `3 | 3`, `2 ∤ 3`, `omega` of order 3.
* **Image equation (Proposition 3.1(1)).** `g b = b` for `b = s_1 + s_2 + s_3`, and
  `c b = sum_(i,j) t_i s_j = 3 = 1`.
* **Census.** Items 3, 4 and 6 of artifact Section 1 were spot-checked and are consistent: `tau(e_psi) = 1`,
  lifted traces `1/3` and `1/9`, and Malcev plus simplicity for `R^x`. They are remarks, not claims.

## 3. Odd-measure crossed product (w3-corner-crossed; 12bf7b4ed8)

### 3.1 `thompson-action-on-odd-measures-is-essentially-free`: PASS

* **Fixed sets.** `(g mu)(f) = mu(f o g)`, so `Fix(g) = Ann(D_g) ∩ M_-` with `D_g = {f o g + f}`.
* **Null annihilators.** `V` acts by automorphisms of the discrete group `C(X, F_2)`, hence preserves Haar
  measure on the dual `M` and the coset `M_-`. A closed subgroup `Ann(D)` has finite index in `M` iff `D`
  is finite. So `Ann(D)` is Haar-null when `dim D` is infinite.
* **Infinite dimension.** A moved point gives a cylinder `C` with `C ∩ g^-1 C` empty. For disjoint
  subcylinders `C_j` of `C`, the vectors `1_(C_j) + 1_(g^-1 C_j)` restrict to `1_(C_j)` on `C`, so they are
  independent.

### 3.2 `star-compression-designs-need-weight-four-colliding-columns` (Theorem 4.1): PASS, one precision remark

* **Conventions.**
  * `[g] -> [g^-1]` is an anti-automorphism of `F_3[H]` fixing `eps_-` and each `[tau_C]`.
  * Functions are polynomials in the commuting symmetric `[tau_C]`, hence fixed.
  * `(f[g])* = [g^-1] f = (f o g)[g^-1]` matches `[g] f [g]^-1 = f o g^-1`.
  * Then `x* x = sum_(g,h) (a_g a_h) o g [g^-1 h]`, and grouping by `k = g^-1 h` gives (2.1).
* **Column norms.** Lemma 2.1 re-derived. `c ≡ 1 mod 3` holds everywhere, because nonzero squares in
  `F_3` are 1; no freeness is needed.
* **Part 1.** `∫ c = sum_g lambda(g^-1 supp a_g) = sum_g lambda(supp a_g) = ∫ n`, by `V`-invariance.
* **Part 2.** `mu([0]) + mu([1]) = 1` on `M_-`, so `lambda(U_[0]) = 1/2`. Then `∫ n >= 1` and
  `∫_(U_[0] \ A) n <= 1/2` give `∫_A n >= 1/2`.
* **Part 3.** Both columns contain `nu` with nonzero entries, and their pairing is 0 by Lemma 2.1. So they
  share at least two points.
* **Part 4.** The pair count and the bound `c >= 4` hold on the relevant points, so `∫_W c >= ∫_A n >= 1/2`,
  and `c <= |F|` gives `lambda(W) >= 1/(2|F|)`.
* **Precision remark.** The proof removes `union_(k in F^-1 F, k != 1) Fix(k)`. The argument also needs:
  * `nu` outside `Fix(g' g^-1)` with `g' g^-1` in `F F^-1`, so that `mu != mu'`;
  * trivial stabilizers at the points `mu = g^-1 nu` used in Lemma 2.1, involving products from
    `(F^-1 F)^2`.

  The repair costs nothing. Remove `N = union_(k in V, k != 1) Fix(k)`, a countable union of null sets
  by Proposition 3.1. It is `V`-invariant, since `g Fix(k) = Fix(g k g^-1)`, so every `g^-1 nu` is
  off `N`. All four parts then hold as stated. The author found the same gap independently, and the
  artifact carries exactly this set at `2ec8fa09e`.
* **Corollary 5.0 (at 2ec8fa09e): PASS.** The column weight at a point is at most `|F|`, and Part 4
  needs `lambda(c >= 4) > 0`, so `|F| >= 4`.
* **Proposition 5.1 (at 2ec8fa09e): PASS.**
  * **Hypothesis.** `(g, g') -> g^-1 g'` is injective on ordered pairs of distinct elements.
  * **Why the earlier version failed.** An involutive difference `k` comes from both `(g, g')` and
    `(g', g)`, so the `k` component then has two terms. The removed corollary "two-term designs are
    dead" was false on its original grounds; Corollary 5.0 supersedes it.
  * **Proof.** Under injectivity each off-identity component has one term `(a_g a_(g')) o g`. So the
    supports are pairwise disjoint, `n <= 1`, and Part 2 fails.

## 4. Binary swap-group matrix units (w3-kap-visible; artifact Section 1)

### 4.1 `binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap`: PASS

* **The group.**
  * `u^2 = 1 + s0 t1 s0 t1 = 1`, since `t1 s0 = 0`; likewise `v^2 = 1`.
  * On the depth-one matrix units, `u = [[1,1],[0,1]]`, `v = [[1,0],[1,1]]`, and `g = uv = [[0,1],[1,1]]`
    has order 3.
  * `E_00 + E_11 = 1`, so this `M_2(F_2)` is a unital copy in `R`, and `<u, v> = GL_2(F_2) ~= S_3`.
* **Proposition 1.2.**
  * **(1)** `x^2 = [1] + [u^2] = 0`.
  * **(2)** Recomputed `xyx = v + g + g^2 + w` and `xyxy = 1 + u + v + g`, using `gv = u`, `g^2 v = vuv = w`
    and `wv = g^2`. The braid relation `uvu = vuv` holds in `S_3`.
  * **(3)** Holds.
  * **(4)** `xy + yx = g + g^2 = 1 + z`, and `z^2 = 1 + g^2 + g^4 = z`. The value `pi(z) = I + g + g^2 = 0`
    is also a direct `M_2(F_2)` computation, so this step does not need the cited node.
  * **(5)** In characteristic two, `xy z = xy + xy(xy + yx) = 0`; the other side and `yx` work the same
    way. So `xy`, `yx` and `z` are orthogonal idempotents with sum `1`. `P0^ = xy + z = u + v + g^2` with
    `g^2 = vu`, and `pi(u + v + vu) = 1 + s1t1 = s0t0` directly.
* **Lemma 1.1.** The binomial expansion of the commuting `1` and `n`, and the Frobenius in `F_2[<u>]`.
* **Scope.** A partial lift: `xy + yx` misses the kernel idempotent `z`. It decides nothing about one-sided
  pairs, as the node says. Remark 1.3 is unused; only its Sylow count was checked (`2^6` does not divide `4`).
* **Artifact Sections 2–3** (telescoping, obstructions) are queued separately.

## 5. Mixed-depth lifts of the ternary Leavitt pair (w3-corner-cohn-a; artifact at 5837c75433)

### 5.1 `natural-leavitt-pair-lifts-have-partial-symmetry-defect` (Lemma 2.1, Remarks 2.2–2.3): PASS

* **Conventions.**
  * `f[k] = [k](k^-1 . f)` follows from `[g] f [g]^-1 = g . f`.
  * `k^-1 . 1_U = 1_(k^-1 U)`.
  * `g U_C = U_(gC)`, because `(g mu)(gC) = mu(C)`.
* **Lifts.** In the checker convention, `s_0 = S[00]T[0] + S[01]T[1] = g_0 p_0 + g_1 p_1` and
  `t_0 = g_0^-1 p_00 + g_1^-1 p_01`.
* **Grades of `tau sigma`.**
  * `(0,0)` and `(1,1)` give `P_0 + P_1 = 1` on `M_- = U_0 ⊔ U_1`.
  * `(0,1)` gives `[h] 1_(U_A) P_1`, and `(1,0)` gives `[h^-1] 1_(U_(B')) P_0`.
  * `A ⊆ 0` because `g_1(1) = 01`, and `B' ⊆ 1` because `g_0(0) = 00`.
* **Item 1.**
  * `g_1(0) = 00 ∪ 1` gives `g_1^-1(1) = 0 \ A`, which is nonempty, and `(1,1,1)` on the atoms `(A, 0\A, 1)`
    is odd. So `W_1` is nonempty.
  * `h != 1`, since `h(A) = 0` strictly contains `A`. So `D` has no identity grade.
* **Item 2.** `h(A) = 0` and `h(1) = B'`. Also `h^-1(1) = 1 ∪ (0\A)` and `h(0) = 0 ∪ (1\B')`, from
  `g_0(1) = 01 ∪ 1` and `g_0^-1(1) = 1 \ B'`. The total-mass contradictions hold.
* **Item 3.** All eight products recomputed.
* **Item 4.** `(F ± D)^2 = 2(F ± D)`, `8 = 2`, `e + e' = 4F = F`, and the identity grade of `e'` is `2F != 0`.
* **Item 5.** `c = (1 - F) + 2e = 1 + D = tau sigma`, so `tau'' sigma = c^2 = (1 - F) + e = 1 - e'`, with
  `pi(c) = 1`.
* **Left invertibility.** It holds iff `e'` lies in `S_- sigma`:
  * if `y sigma = 1`, then `e' = (e' y) sigma`;
  * if `x sigma = e'`, then `(tau'' + x) sigma = 1`.
* **Remark 2.2.** `lambda(W_i) = 1/4`, since one of the four odd functions on three atoms qualifies. So
  `Tr(e') = 2 · 1/2 = 1`.
* **Remark 2.3.**
  * `vu = f_1`, `uv = f_2`, `u = f_2 u f_1` and `v = f_1 v f_2`.
  * `xy = e'` and `yx = 4 f_1 = f_1`, using `f_1 u = 0` and `v f_1 = 0`.
  * `W_2 ⊆ U_0`.
  * If `1 ~ f_1`, then `1 ≲ P_0`, and the first-letter swap gives `1 ≲ P_1` orthogonally. That is a Cohn
    family.
* **Cited, not re-derived.** `signed-thompson-algebra-is-odd-measure-crossed-product`, for `B ⊆ S_-` and
  for "no Dirac measure implies `ker pi`".
* **Addendum: a missed display slip.**
  * **What was wrong.** The claim node and its route displayed the correction factor as
    `(1 − F) + 2(F + D)`. That element is `(1 − F) + e = 1 − e'`, and `(1 − e')(1 + D) = 1 + D`, so it
    returns `tau sigma` unchanged.
  * **The correct factor** is `c = (1 − F) + 2e = 1 + D`, as in artifact item 5 and above.
  * **Who caught it.** This verification missed the display slip. `w4-vf-linear-b` caught it and landed
    the correction at `67642b6fe3`.

### 5.2 `no-equivariant-lattice-lift-of-cylinder-idempotents` (Theorem 3.1): PASS, two remarks

* **The proof.** Stone duality gives `r`. Equivariance `r(g mu) = g r(mu)` was recomputed, V-invariance
  of `lambda` is Section 3.1 above, and the halving contradiction with `h_1`, `h_2` and the swap holds.
* **Remark 1: hypothesis 3 is unused.** The contradiction needs only hypotheses 1–2 and a nonempty `M_-`.
  So there is no `V`-equivariant Boolean homomorphism `Clopen(X) -> Clopen(M_-)` at all.
* **Remark 2: the claim's "Equivalently" sentence.**
  * **Different statement.** Idempotent lifts in `B` need not lie in `C(M_-, F_3)`, so this is not the
    Stone-duality statement.
  * **Still true, more simply.** `tau(f[g]) = delta_(g,1) ∫ f d lambda` is an `F_3`-valued trace on `B`.
    Dyadic values reduce mod 3, and the trace property uses V-invariance of `lambda`.
  * **Proof.** Take any `V`-equivariant, finitely additive `Phi : Clopen(X) -> B` with `Phi(X) = 1`. Then
    `nu = tau o Phi` is invariant and additive. `h_1` and `h_2` give `nu(0) = 2 nu(0)`, so `nu(0) = 0`;
    the swap gives `nu(1) = 0`, contradicting `nu(X) = 1`.
  * **Not needed.** Idempotency, commutation and Dirac compatibility.

## 6. F_9 Hadamard spectral idempotents (w3-corner-cohn-b; artifact at 136a93c518)

### 6.1 Theorem 1.1 and the routes: PASS

* **`rho` is a unital ring embedding.** `rho(i)^2 = -I`, and `F_9 = F_3[i]/(i^2 + 1)` since `-1` is a
  non-square mod 3.
* **`Phi` is a unital ring map.** `rho (x) id` is a unital algebra map `F_9 (x) S_- -> M_2(S_-)`, and
  `J` is unital, so `Phi` preserves `tau_i sigma_j = delta_ij 1`.
* **Routes.**
  * `anti-central-cohn-family-extends-to-f9` (inclusion): valid.
  * `f9-cohn-family-descends-to-anti-central-summand` (via `Phi`): valid.
  * The cycle between the two routes is intentional.

### 6.2 `f9-hadamard-spectral-idempotents-are-half-idempotents` (Propositions 2.1–2.3): PASS

* **Lemma 2.0.** Recomputed with `(c_ab) <-> sum c_ab s_a t_b`:
  * `h^2 = -I = z` and `u^2 = I`;
  * `uh = [[1,1],[0,2]]` and `uhu = [[2,-1],[2,-2]] = -h`;
  * `[z] = -1_-`, since `eps_- [z] = -eps_-`.
* **Proposition 2.1.**
  * `f_+^2 = 4(2 + 2i[h]) = f_+` and `f_+ f_- = 4(1 - i^2 [h]^2) = 0`.
  * `[u] f_+ [u] = f_-`.
  * The matrix-unit products hold, for example `E_12 E_12 = f_+ ([u] f_+ [u]) = f_+ f_- = 0`.
* **Proposition 2.2.**
  * `tau_2 sigma_2 = c f_+ [u]^2 f_+ b = 1_-`.
  * Both cross products equal `c f_+ [u] f_+ b = c [u] f_- f_+ b = 0`.
* **Proposition 2.3.**
  * `sigma(eps_-) = 2(1 - sigma(z))` is idempotent because `sigma(z)^2 = 1`, and nonzero because
    `sigma(z) != 1`.
  * The rank state is constant on equivalent idempotents: `r(xy) = r(xyxy) <= r(yx)`.
  * `xy = f_+ b c f_+` is an idempotent below `f_+`, so `1 = s(xy) <= s(f_+) = 1/2`.
* **Route** `hadamard-spectral-fullness-gives-f9-cohn-family`: valid given its two required claims.

### 6.3 Section 3: Lemma 3.3 PASS, prose consistent

* **Lemma 3.3 and its consequence.** The evaluation is `2(lambda_+ g_+ + lambda_- g_-) +
  2i(lambda_+ g_+ − lambda_- g_-) h`. Rationality forces `lambda_+ g_+ = lambda_- g_-`, and then the value
  is a unit, not `s0`.
* **Section 3.1.** `tr(ih) = 0` and `det(ih) = -1`. The eigenvalues `±1` are distinct in characteristic
  three, so `ih` is conjugate to `d = 1 + s1t1` over `F_9`. Also `2(1 + [1+p]) = 1 − P_p`.
* **Section 3.2 wording.** `rho (x) id` carries an `F_9` design to a `2 x 2` `F_3` design. The converse needs
  entries commuting with `rho(F_9)`, so "is the same as" should read "gives".

## 7. Covariance obstruction and the V rank gate (w3-gate-v; artifact at dbb8cb8979)

### 7.1 `thompson-v-cantor-system-has-no-covariant-rank-model`: PASS

This is a third derivation; `gk-vf-linear` Section 50 was the second.

* **Lemma 2.1(b), recomputed.**
  * A vector in `im e_k ∩ im f_k` lies in `im(e_k − e_k^2) + im(e_k f_k)`.
  * `im e_k ⊆ im(e_k + f_k) + im(e_k^2 − e_k) + im(f_k e_k)`.
  * Hence `rank e_k + rank f_k <= rank(e_k + f_k) + o(n_k)`.
* **Lemma 2.2 and Theorem 2.3.** Both hold. The proof uses covariance by units only, never
  multiplicativity of `sigma`.
* **Proposition 2.4.**
  * The four prefix codes are complete.
  * `|m(h_i C) − m(C)| <= eps` by rank subadditivity.
  * So `m([0]) <= 2 eps` and `m([1]) <= 2 eps`, which gives `eps >= 1/4`.
* **Section 3.1 is prose.** Feeding compressions into Proposition 2.4 requires rounding almost-idempotents
  to idempotents at small rank cost. The step is standard but not written out.
* **Calibration 5.2.** `(x−1)(y−1) = 1 + x + y + xy` is the all-ones matrix over `F_2`, of rank 1. Each
  `x − 1` has rank `4 − 2 = 2`.

### 7.2 Rank-gate wiring and Section 4.4: PASS

* **The two open claims.** `thompson-v-is-f2-linear-sofic` and `thompson-v-has-no-nontrivial-f2-rank-model`
  are OPEN and refute each other. `V` is simple, so a nontrivial homomorphism into `M^x` is injective.
  Units of `M` lift to almost invertible sequences, so homomorphisms into `M^x` are exactly the linear
  sofic approximations.
* **Route `thompson-v-f2-linear-sofic-from-soficity`.** Valid. If a `delta` fraction of points is not
  fixed, then `rank(P − I) = n − #cycles >= delta n/2`.
* **Route `non-linear-sofic-via-thompson-v-rank-triviality`.** Valid and conditional.
* **Dead route `thompson-v-f2-linear-sofic-via-covariant-cantor-truncation`.** Correctly invalidated by the
  ESTABLISHED covariance claim.
* **Section 4.4 scope.** Correct. A nontrivial `phi` on the simple group `R^x` is injective and restricts
  to a nontrivial homomorphism of `V`. That yields only the binary characteristic-two case of
  `leavitt-el3-rank-models-over-finite-fields-are-trivial`, so not landing a route into it is right.
  Simplicity (`binary-leavitt-unit-group-is-simple`) was not re-derived here.
* Agrees with `gk-vf-linear` Section 51.

## 8. Halving-invariant states (w3-corner-module; artifact at 5c0ded347f)

### 8.1 `twisted-leavitt-k0-states-can-be-chosen-halving-invariant`: PASS

* **Notation.** In "`F(mu) = u`", `mu` is the class `m·u`: `Phi = M_m(psi)` sends `[M_m(A)]`, which
  corresponds to `m·u`, to `[A] = u`. So `x = F(u)` satisfies `m x = u`, and that is the only property used.
* **Step 2.** `Phi_s(u) = m s(x) = s(m x) = 1`.
* **Step 3.** A summand `P` of `A^n` has `[P] <= n u`, so `|s(a)| <= n`.
* **Step 4.** `Phi(M_N) − M_N = (Phi^N s − s)/N` telescopes. Each coordinate of `Phi` is continuous in the
  product topology, so a limit point is fixed.
* **Consequence.** "Corner full iff no halving-invariant state" holds with Theorem E.
* **Scope.** A normalization; it decides nothing.

## 9. Finite-join defects (w3-kap-kernel; artifact at aaafa6dcc4)

### 9.1 `mixed-finite-subgroup-defects-need-infinite-generation`: PASS after one precision repair

* **Precision.** The hypothesis `0 != f <= e` allows `f = e`. Then `e − f = 0 = I − AB` with `A = B = I` is a
  configuration, against "no such configuration exists". The proof uses `f < e`.
  * **Repair:** assume `f != e`, equivalently a nonzero defect.
  * The hypothesis `f != 0` is not needed.
* **The argument, with `f < e`.**
  * `e − f` is a nonzero idempotent of `M_n(F_p[H])`.
  * LFT1 gives `t_p = dim((e−f) F_p[H]^n)/|H| > 0`, a rational number in `Z_(p)`.
  * `A : F_p[G]^n -> AB F_p[G]^n` is an isomorphism with inverse `B`, and `F_p[G]^n = AB F_p[G]^n ⊕ d F_p[G]^n`.
    So the defect class is `0`.
* **Content.** This is consequence 2 of `lifted-trace-detects-finite-subgroup-projectives` applied to the
  finite group `H = <H_1, H_2>`. The node says so; it is a corollary, not a duplicate.
* **Cited, not re-derived.** Additivity of `t_p` on `K_0(F_p[G])` is taken from that node.
* **Amended** by the author at `0a51664ba9`.

## 10. The two-root defect piece and a Kazhdan calibration (w3-gate-bridge-b; b62a0dc006, 6ebb4155b8)

### 10.1 `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model` (Theorem 1.2, Corollary 1.3): PASS

* **Lemma 1.1.** `sigma(s) q ∈ qM` gives `sigma(s) q = q sigma(s) q`, so `q sigma(s) q sigma(t) q = q sigma(st) q`.
  Invariance under `s^-1` gives inverses.
* **(1)** `x'` and `y'` are supported on `[1000]`, so they commute with `Gamma`, and `P` commutes with
  `sigma(Gamma)`.
* **(2), the fixed case.**
  * `q sigma(gamma) q = q` gives `sigma(gamma) q = q`. So `qM ⊆ Fix_r(sigma(Gamma)) = fM` by globality
    (cited), and `P = fP`.
  * `sigma(g) f = f` gives `(1−f) sigma(g) f = 0`, hence `(1−f) sigma(g)(1−f) = (1−f) sigma(g)`. So
    `sigma_W` is unital and multiplicative.
  * `N'_23 f = 0` gives `(1−f) N'_23 (1−f) = (1−f) N'_23`. The corner product of `sigma_W` is
    `(1−f) P (1−f) = (1−f) f P (1−f) = 0`.
  * Corner locality (cited) makes `sigma_W` trivial. Then `sigma(g) = 1 + f sigma(g)(1−f)`. For `a, b` in
    `fM(1−f)`, `ab = 0`, so `sigma` factors through an abelian group and is trivial by perfection.
* **(2), rank and injectivity.** `rk(P) > 0` is corner locality at `1000` for the nontrivial `sigma`.
  Injectivity is simplicity of `R^x`.
* **(3)**
  * `iota_0 o iota_P' = iota_(0P')`, recomputed with `T[0P'] = T[P'] T[0]`.
  * By Lemma 1.1, `(sigma(gamma) − 1) q = q (sigma(gamma) − 1) q` on `Gamma`. So the `P'`-corner product of
    `tau_Q o iota_0` is `q N^(0P')_23 N^(0P')_12 q`, which is nonzero by corner locality.
* **Corollary 1.3.**
  * A prefix replacement `u` with `u[1000] = [0P']` satisfies `u iota_1000(g) u^-1 = iota_(0P')(g)`.
  * So `q sigma(u) P sigma(u)^-1 q != 0`, and `P = qP` then forces `q sigma(u) q != 0`.
* **Cited, not re-derived.**
  * `leavitt-rank-models-kazhdan-fixed-ideals-are-global` in degree `(1,0)`;
  * audit Lemma 1;
  * `two-root-identity-is-corner-local-for-leavitt-rank-models`;
  * perfection and simplicity of `R^x`.
* **Scope.** Not decision-level. It reproduces the problem on a corner, and gives no bound on the descent
  (Remark 1.4).

### 10.2 `kazhdan-groups-without-fd-reps-violate-two-root-identity` (Theorem 2.5): PASS

This is a rank-model construction, checked with full care. The model is of `EL_3(A_X)`, not of `R^x`, so
the gate is untouched.

* **Lemma 2.1.**
  * Suppose `nu_2(d) = k <= j − 1`. Of the two classes `2^k`, `3·2^k` of `i − b'` mod `2^(k+2)`, exactly
    one gives `i − a' ≡ 2^(k+1)`.
  * `W` has length `2^(j+1) >= 2^(k+2)`, so such an `i` exists in `W`.
  * Valuations `k` and `k+1` lie below `j+1`, so `x(i)` would get two parities.
  * Locality and `sigma(C^j_a) = C^j_(a−1)` follow.
* **Matrix units.** `chi_(C_b) u^m = u^m chi_(C_(b−m))`, so `e_ab e_cd = delta_bc e_ad` and
  `sum e_aa = 1`.
* **Lemma 2.2.**
  * `c = [[0,1],[1,1]]` has order 3 and determinant 1.
  * `x^3 − 1` is separable when the characteristic is not 3, including characteristic 2.
  * In characteristic 3, commuting involutions diagonalize with `±1`.
* **Proposition 2.3.**
  * `EL_3(M_m(F_2)) = SL_(3m)(F_2)`: block transvections give the elementary transvections between
    blocks, commutators give those inside a block, and all have determinant one.
  * Over `F_2`, permutation matrices lie in `EL_3(F_2)`, and `x_13(b) = [x_12(1), x_23(b)]`.
* **Lemma 2.4.**
  * `rho_J(u) rho_J(f) rho_J(u)^-1 = rho_J(f o sigma)`.
  * An `f` in `I_X` reading `[−r, r]` vanishes at interior positions, since those windows are windows
    of `z`. So `rank <= 2r`.
  * Kernel elements have bounded rank, so `phi` factors through `A_X`.
* **Theorem 2.5.**
  * **(1)** Finite type. Property (T) is cited.
  * **(3)** With `X = E_12 (x) 1` and `Y = E_23 (x) 1`, the tensor square has `N = X(x)1 + 1(x)X + X(x)X`,
    and `YX = 0`. So `P = Y(x)X + X(x)Y`, two independent pieces of rank `1/9`, total `2/9`. Confirmed
    directly.
  * **(4)** `rk [p_(beta,J), rho_J(u)] <= 2`, and `p_(beta,J)` commutes with diagonal matrices.
  * **(5)**
    * `u e u^-1 = 1 − e`, so the corner is full and of finite type.
    * `(g + eI)(I + E_12 e) = (I + E_12 e)(g + eI)`, using `(1−e)e = 0`.
    * `rk phi(e) = 1/2` gives `rk P_H = 2 · (1/6)^2 = 1/18`.
    * `Gamma_H` acts as the identity on `F_2^3 (x) phi(e)V`.
    * `N_12 P_H = XY(x)X + X(x)XY != 0`.

## 11. Characteristic-three rank models of G_3 (w3-gate-char3; 6d56811c0d)

### 11.1 `ternary-leavitt-rank-models-move-z-iff-nontrivial` (Theorem 2.1): PASS, conditional scope as stated

* **Lemma 1.1.** `[K<z>, K<z>] = [K, K]` since `z` is central; then perfection.
* **Lemma 1.2(a)** holds in any characteristic.
* **Lemma 1.2(b).**
  * `ker(A(x)A − I)` is `Hom_(k[x])((k^n, A^(−T)), (k^n, A))`.
  * The Jordan count gives `sum_nu sum min(a_i, b_j) <= sum_nu g(nu) m(nu^−1)`.
  * If `nu* != nu*^−1`, then `m(nu*^−1) <= n − g(nu*) <= delta n` and `sum_(nu != nu*) g(nu) <= delta n`.
    The total is at most `2 delta n^2`, which is below `(1 − delta) n^2` iff `delta < 1/3`.
* **Lemma 1.2(c).** Perturb representatives to invertible matrices at small rank cost; the signs are
  ω-almost constant.
* **Theorem 2.1.**
  * `iota(G) ∩ <z> = 1`, because `s1t1 != −s1t1` in characteristic three.
  * `f = 2(1 − sigma(z))` is a central idempotent with `sigma(z) f = −f`.
  * `T(z) = 1`, and a trivial `T` gives a sign character, which perfection kills.
* **Conditional scope.** Lemma 1.1 and (4) ⟹ (5) use simplicity of `PG`, which is conditional on the
  imports of `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`. (1) ⟺ (6) and (6) ⟹ (4) do not.
* Agrees with `gk-vf-linear` Section 53.

## 12. Nested idempotents with p-regular intersection (w3-kap-kernel; e1289c2f88, amended 0a51664ba9)

### 12.1 `nested-idempotents-from-p-regular-intersections-are-equal` (Theorem 2): PASS

* **Lemma 1.** `h_t H_2 = h_s H_2` forces `h_s^-1 h_t` into `C`.
* **Step 1.**
  * `M_n(F_p[C])` is semisimple by Maschke, so `Λ = M_n(F_p[C])(1 − π)` and `x ∈ Λ` iff `x π = 0`.
  * So `π f = f`, `eps_t π = 0` for `t != 1`, `eps_1 π = π`, and `e π = π`.
* **Step 2.** `πe` is an idempotent below `e`, equivalent to `π` through `(πe, π)`, inside `M_n(F_p[H_1])`.
* **Step 3.** `fπ` is an idempotent below `π`, equivalent to `f` through `(f, fπ)`, inside `M_n(F_p[H_2])`.
* **Step 4.** The equalities force `e = πe` and `π = fπ`, so `e = fπe = fe = f`.
* **Comparisons** are made in `Q` through LFT1.
* **Scope.** The theorem allows `f = e`. The no-mixed-defect consequence needs a nonzero defect, as
  amended.

### 12.2 `modular-nested-equivalence-refutes-leavitt-direct-finiteness`: valid, conditional on the open hole

* **Normalization.** `x' = exf`, `y' = fye` give `x'y' = e x (yx) y e = e` and `y'x' = f`.
* **Padding.** `(1−e) x = x (1−e) = 0` and `(1−e) y = y (1−e) = 0`, since `(1−e) e = 0` and `ef = fe = f`.
  So `AB = 1` and `BA = 1 − (e − f) != 1`.

### 12.3 Correction: Sections 9.1 and 12 are subsumed, and the open hole is refuted

`w4-kap-join` pointed to `nested-two-finite-subgroup-idempotents-have-strict-rank`, ESTABLISHED 2026-09-07. It
says: for finite `H`, `K`, idempotents `e ∈ M_n(k[H])` and `f ∈ M_n(k[K])` with `ef = fe = f` and `e != f`,
`dim(e k[H]^n)/|H| > dim(f k[K]^n)/|K|`. It holds over any field, with no condition on `<H,K>` or on `H ∩ K`.
Both checks above missed this node.

**Re-derived here in general.** Put `C = H ∩ K`, `Z = e k[H]^n` and `U = Z ∩ k[C]^n`.
* **Upper bound for `f`.**
  * `e k[G]^n = ⊕_r Z r` over right coset representatives of `H`.
  * `Hr ∩ K = Cr` for `r ∈ K`. So the part of `e k[G]^n` supported in `K` is `⊕_(r ∈ C\K) U r`.
  * `f k[K]^n ⊆ f k[G]^n ⊆ e k[G]^n` is supported in `K`, so `dim(f k[K]^n)/|K| <= dim U/|C|`.
* **Lower bound for `e`.** `U k[H] = ⊕_(t ∈ C\H) U t ⊆ Z`, so `dim Z/|H| >= dim U/|C|`.
* **Equality forces `e = f`.**
  * Equality gives `f k[K]^n = U k[K]`, so `f` fixes `U`.
  * `e k[G]^n = ⊕ U k[H] r`, so `f` fixes `e k[G]^n`, and `fe = e`. With `fe = f`, `e = f`.

**Consequences.**
* **9.1.** `mixed-finite-subgroup-defects-need-infinite-generation` is correct, but its framing is stale. The
  "infinite join" case it calls the only survivor is already excluded.
* **12.1.** `nested-idempotents-from-p-regular-intersections-are-equal` is correct, but it is the special case
  `k = F_p`, `p ∤ |C|` of the 09-07 node. Its `distinct_from` should name that node, and Theorem 2 adds
  nothing to it.
* **The open hole is refuted.** `modular-nested-idempotents-equivalent-over-leavitt-units` asks for
  `xy = e`, `yx = f`, `0 != f < e` from two finite subgroups. Equivalence gives equal classes, hence equal
  lifted traces, hence equal LFT1 ranks, contradicting the strict gap. The 09-07 node states this
  consequence itself. The claim needs `refuted_by: nested-two-finite-subgroup-idempotents-have-strict-rank`.
* **The route is dead.** `modular-nested-equivalence-refutes-leavitt-direct-finiteness` has a valid padding
  step, but its prerequisite is false. The "even intersections survive" part of artifact Section 4 is also
  dead.

## 13. Compressor extensions of level models (w3-gate-construct; ceb14cf1d2)

### 13.1 `transvection-displacement-forces-exact-local-embedding` (Theorem 4, Corollary 5): PASS

* **Lemma 1.** `Fix(g) ⊆ Fix(g_p)`. `P` restricted to `<g_p>` is free, so `dim Fix(g_p) = n/|g_p|`.
* **Lemma 2.** `rk(AB − 1) <= rk(A−1) + rk(B−1)`, and `u z^-1 u^-1 − 1 = u z^-1 (1 − z) u^-1`.
* **Lemma 3.**
  * **Choice.** `φ` vanishes on `v, zv, z^-1 v`. So `ψ(zv) = φ(v) = 0`, `ψ(v) = φ(z^-1 v) = 0` and `φ(zv) = 0`.
  * **First commutator.** `A^2 = B^2 = AB = BA = 0`, and `(1+B)^-1 = 1 + B`, so `[z,u] = 1 + A + B`.
    `zv` and `v` are distinct nonzero vectors over `F_2`, so `N != 0`.
  * **Second commutator.** `chi o N = 0` gives `y u'' y^-1 = 1 + yw ⊗ chi`. `chi(w) = 0` kills the cross
    term, so `[y, u''] = 1 + Nw ⊗ chi`. Also `Nw = a + β(w) b != 0` and `chi(Nw) = 0`.
* **Theorem 4.**
  * `τ_k(1) = 1` and `τ_k(g^-1) = τ_k(g)^-1` follow from multiplicativity on `F`.
  * `g^-1 h ∈ F^-1 F`, and `σ(g^-1 h) != 1` for `g != h`, give injectivity.
* **Corollary 5.**
  * **(a)** `u_13(0,0)` is a transvection.
  * **(b)** Lemma 1 at `p = 2`.
  * **(c)** A finitely presented LEF group is residually finite, and an infinite simple group is not.
  * **(d)** Lemmas 2–3 inside `SL_m(F_2) <= F_K` for `m >= 4`.

### 13.2 `natural-compressor-extension-fails-at-toeplitz-commutator` (Proposition 7, Corollary 8): PASS

* **Relations.** The Steinberg forms (Σ1)–(Σ5) were checked against `t0 e_ab = e_(a−1,b)` and
  `e_ab s0 = e_(a,b−1)`, including the vanishing boundary cases.
* **Forcing.** In every relation the two transvections commute, so `q u q^-1 = w u`. Rank-one factors over
  `F_2` are determined. This recovers:
  * `X^ δ_a^(2) = δ_a^(2) + δ_(a−1)^(1)`;
  * `δ_b^(2)* o Y^^-1 = δ_b^(2)* + δ_(b−1)^(3)*`;
  * `δ_b^(1)* o Z^^-1 = δ_b^(1)* + δ_b^(3)*`.
  The commutations pin the remaining components.
* **Commutator.** `(1+A)(1+B)(1+A)(1+B) = 1 + AB` when `A^2 = B^2 = BA = 0`, and `T_N S_N = 1 − P_(N−1)`.
  So `Z^^-1 [X^, Y^] = u_13(N−1, N−1)`.
* **Corollary 8.** The index swap conjugates the error to `u_13(0,0)`, and `X^2 = Y^2 = 1` in
  characteristic two.

## 14. Two-piece lifts and obstructions (w3-kap-visible; artifact Sections 2–3 at b2d4e757a9)

### 14.1 `two-piece-s0-lifts-telescope-to-a-corner`: PASS; triangular route valid

* **Lemma 2.1.**
  * `pi(a) = s00 t0 + s01 t1 = s0`.
  * `P_0 g1^-1 = g1^-1 P_00 = s0 t00`, so `pi(b) = (s0t0 + s1t1) t0 = t0`.
  * `pi(X) = g1^-1 P_00 P_01 g2 = 0`.
* **Theorem 2.2.**
  * `YX = E1^ − C'C`, and `(1+Y)(1 + X + YX) = 1 + X + Y`.
  * **Inverse.** `S = E^ + Xw + w` inverts `[[E^, X],[0, d]]`, using `dX = 0` and `wX = 0`.
  * **Converse.** Peirce blocks of an inverse give `r = 0` and `sd = ds = E1^`.
* **Proposition 2.4.** `(X+Y)^2 = XY + YX` in orthogonal corners, and `(YX)^(k+1) = Y(XY)^k X`.
* **Remark 2.5.** `g1^-1 P_0 g1 = P_0 + q`, with `q = P_1 − g1^-1 P_1 g1 < P_1`.

### 14.2 Obstructions (Lemma 3.1, Lemma 3.3, Computation 3.5, Proposition 3.6): PASS

* **Lemma 3.1.** `D` acts freely on `F × F`. The relation `f1 h f2 = f1' h f2'` forces
  `f1^-1 f1' = h f2 f2'^-1 h^-1 ∈ D`. So orbits go to distinct group elements.
* **Lemma 3.3.**
  * Truncating supports to `H'` is an `F_2[H']`-bimodule map, so inverses stay on `H'`.
  * `w = E1^ T^-1 E1^` inverts `C'C`, and `pi(C C'') = pi(h) P_1 pi(h)^-1 = q != P_1`.
  * So `(C'' + E^)(C + E^) = 1 != (C + E^)(C'' + E^)`.
* **Computation 3.5.** `g1`, `g2` and `h` checked on prefixes.
  * On `δ_00y` the points `0y`, `100y` and `1y` are distinct for `y != 0^∞`, which forces upper triangular
    matrices.
  * On `δ_10x` the points `0x` and `000x` are distinct for `x != 0^∞`, which forces the identity.
  * So `D = 1`.
* **Proposition 3.6.**
  * **(1)** The block `F_2[S_3](1+z) = M_2(F_2)` maps injectively, and the local block `F_2[C_2] z` is killed.
  * **Supports.** They have sizes 4 and 3.
  * **`D = C_2`.** Vanishing forces `S1 f = S1` and `f' S2 = S2`, so both sizes would be even.
  * **`D = C_3`.** `h^-1 D h = D`, so the twist fixes `z`. In the `F_4` component, `E^(1+z) = xy` and
    `(1+z) E1^ = yx`.
  * **`D = F`.** Equal right ideals would force `q = P_1`, or `pi(h)^-1 P_0 pi(h) = P_0`.
* **Scope.** Remark 3.4 cites the 09-07 strict-rank node, which is re-derived in 12.3.

## 15. Haar law and torus normal form (w3-gate-char3; 6601af31f3, artifact Sections 4–5)

### 15.1 `anti-central-rank-models-see-haar-measure-on-signed-diagonal` (Theorem 4.1): PASS

* **Half split.** `τ_(X∖C) = 1 − 2(1 − P_C) = z τ_C`. So `phi(Q_(X∖C)) = 1 − phi(Q_C)`, and transitivity of `V`
  gives rank `1/2`.
* **Fourier inversion.**
  * `sum_ε a_ε χ_S(ε) = 1 − 2 rho(phi(Q_(c_S)))`, which is `1`, `−1` or `0`.
  * So `a_ε = 2^-n (1 − χ_[n](ε))`, which is `2^(1−n)` on odd patterns, `= lambda(A_ε)`.

### 15.2 `ternary-rank-model-root-element-torus-normal-form` (Proposition 5.1): PASS

* **Allowed components.** `diag(s)` conjugates `E_12` by `s_1 s_2`. So `τ_11` and `τ_0 τ_10` commute with
  `x_12(1)`, and only `ε` and `ε'` occur.
* **Reflection.**
  * `x_12(1)^3 = 1` gives `N^3 = 0`, and `σ(x_12(−1)) − 1 = −N + N^2`.
  * Conjugation by `τ_0` gives `D − A = −D − A + N^2`, so `D = −N^2`.
* **Squares.** `D^2 = N^4 = 0`, so `N^2 = A^2`, `N = A − A^2` and `A^3 = −(DA + AD)/2 = 0`.
* **(c)** Theorem 4.1 for the code `(0,10,11)`: the odd patterns give the four weights, each of rank `1/4`.
* **Hub wiring.** `ternary-anti-invariant-swap-corner-is-full` has
  `refuted_by: ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`. This is valid through
  Theorem 2.1 and Corollary 3.1.
* Agrees with `gk-vf-linear` Section 54.

## 16. Corner rank data and the two-root deviation (w3-gate-bridge-a; 47302b9818)

### 16.1 `corner-rank-data-cannot-contract-the-two-root-deviation`, parts 1–3: PASS, one precision remark

* **Part 1.** Derived directly.
  * Put `V' = (1+Y)(1+X) = 1 + X + Y + YX`. Then `n_13 V' = XY − YX`, so
    `n_13 − XY = −(1 + X) YX V'^-1`, using `Y^2 = 0`. Hence `rk(n_13(1) − XY) = rk(YX)`.
  * `rk(n_13(1)) = rho` is part 1 of the displacement claim, and also follows from Weyl conjugation.
* **Part 2.**
  * Part 4 of `leavitt-rank-models-have-uniform-root-displacement` explicitly covers a single idempotent
    ("in particular `rho(e) = rho`").
  * Part 1 transports the value to the `13` root.
* **Part 3.**
  * `t_γ' s_γ = 0` for `γ != γ'` of equal length, so `w^2 = sum_(|μ| = k) e_μ = 1`.
  * `w s_γ = s_γ'` and `t_γ w = t_γ'`, so `w e_γ w = e_γ'`.
* **Scope.** Parts 1–3 do not use `rank-modelled-coefficients-violate-two-root-identities`.
* **Precision remark (claim consequence paragraph, artifact Section 4).** "Additivity is refuted" overstates.
  * **What the calibration shows.** Take the tensor-square model over `D = colim M_(2^k)(F_2)`, with
    `X_γ = E_12 ⊗ phi(e_γ)`. There `P_γ = Y_γ ⊗ X_γ + X_γ ⊗ Y_γ`, whose image lies in the independent blocks
    `phi(e_γ)V ⊗ phi(e_γ)V`. So `sum_γ rk P_γ = 2^(1−k)/9 <= 1` at every level: the displayed inequality
    holds there.
  * **What it refutes.** Orthogonality of the ranges of the root branch defects `a_γ`, `b_γ`. It does not
    refute the displayed branch-rank inequality.
  * **Why no calibration can do more.** In a Leavitt model that inequality, with part 3, would imply the
    open `leavitt-corner-deviations-vanish-along-levels`. A calibration over another coefficient ring cannot
    refute it.
  * **Suggested wording.** "Corner data do not supply additivity".

### 16.2 `two-root-identity-via-level-contraction`: valid, conditional, one notation remark

* **Why it cannot fire yet.** Both prerequisites are OPEN.
* **Notation.** The route writes `delta(0) = rk(n_23(e_0) n_12(e_0))`. That quantity is `delta(1)` (word `0`).
  `delta(0)` is the empty word, `e = 1`, the unit pair itself.
* **Shorter conclusion.** `delta(0) = 0` is `N_23 N_12 = 0` on the unit pair, without the branch split or
  corner locality. The prose chain also works, but it cites nodes that are not in `requires`.

## 17. V gate, second batch (w3-gate-v; cd762e2b8a, 88813f5c48)

### 17.1 Lemma 3.1a and Proposition 3.1b (`beta >= 1/32`): PASS, one wording remark

* **Lemma 3.1a.**
  * The intersection bound is `rk(e − e^2) + rk(ef)`.
  * The five-image inclusion bounds the sum.
  * Subtracting gives losses `2, 1, 2, 1`.
* **Compression errors.** `(ST)_W − S_W T_W = P S (1−P) T|_W`, of rank at most `d_T(W)`, because `1−P` kills
  `W` inside `TW + W`.
* **Defects.**
  * `e_C^2 − e_C = −P rho(1_C)(1−P) rho(1_C)|_W`.
  * `e_C e_D = −P rho(1_C)(1−P) rho(1_D)|_W`.
  * The sum `sum e_C = 1_W` is exact.
* **Rounding.** `ker S_i` embeds in `(sigma(h_i)W + W)/W`, since `sigma(h_i)` is injective.
  * *Wording:* `A_i` should be obtained by changing `S_i` on its kernel (keep `S_i` on a complement, and send
    the kernel bijectively onto a complement of the image), not "on a complement of its kernel".
  * The bound `rank(A_i − S_i) <= beta dim W` is correct.
* **Covariance defect.** At most `2 beta` (replacing `A_i` by `S_i`) plus `(2 beta + beta)` from the
  compression errors, since `d_(rho(1_[0])) <= d_(rho(1_[00])) + d_(rho(1_[01]))`. So `eps <= 5 beta`.
* **Counting.**
  * `m([0]) >= m([00]) + m([01]) − 6 beta` and `m(h_i C) >= m(C) − eps`, so `m([0]) <= 2 eps + 6 beta`.
  * `1 <= m([0]) + m([1])` by subadditivity on the exact sum.
  * So `1 <= 20 beta + 12 beta`.

### 17.2 `thompson-v-rank-models-displace-every-element-uniformly`: PASS

* **The factor 2.** `[g,h] − 1 = (g − hgh^-1) h g^-1 h^-1`.
* **Conjugacy of clopen 3-cycles.**
  * `g w g^-1` recomputed on `[a']`, `[b']` and `[c']` gives `tau_b`, `tau_c tau_b^-1` and `tau_c^-1`.
  * `g` lies in `V`, since the four images partition `X`.
* **First commutator.**
  * `[a0] ∪ z[a0]` misses `z[a1]`.
  * `S` misses `x_0`, because `z^-1 x_0 ∉ [c] ∪ [d]`.
  * `u` is the identity on `z[a]`, while `z u z^-1` carries `z[a]` onto the disjoint `z[c]`, so `y != 1`.
* **Second commutator.**
  * `y v y^-1` is supported on `y[p] ∪ [q] ∪ [r]`.
  * `[y, v]` acts as `y`, `v y^-1` and `v^-1` on `[p]`, `y[p]` and `[q]`, and as the identity on `[r]` and off
    these sets. That is a clopen 3-cycle with nonempty complement.
* **Conclusion.** `d_3 <= 4 rk(sigma(z) − 1)`. If `d_3 = 0`, `sigma` kills the normal closure of `t`, which is `V`.

### 17.3 `thompson-v-rank-models-through-displacing-sym-reps-are-trivial`: PASS

* **Bounded degree.**
  * If `m_k <= 7` on an ω-large set, one value `m` is ω-large.
  * The image then has at most `m!` elements, a finite quotient of the infinite simple group `V`, hence
    trivial.
* **Lemma 1** (`m >= 8`).
  * `z(a) ∉ {a, c, d}` forces `z u z^-1 != u`.
  * `|supp y| <= 6` leaves room for `q` and `r`.
  * The commutator is the 3-cycle `(p y(p) q)`.
* **Exactness.**
  * The pairs `(1, s_i)` and `(s_i, s_i^-1)` give `phi_k(1) = 1` and inverses.
  * Induction along relator prefixes evaluates every relator to `1`, so `psi` is a homomorphism with
    `psi(s_1) != 1`.
  * Simplicity embeds `V` in `S_(m_k)`, which is impossible.
* **Scope values.** The regular module has free orbits of size 3, so `d = 2/3`; the natural module has `d = 2/m`.

## 18. Moving-level normal form (w3-gate-construct; 74d1ec087, artifact Section 4)

### 18.1 `rank-models-are-exact-representations-at-moving-finite-levels` (Lemma 9, Proposition 10, Corollary 11): PASS

* **Lemma 9.**
  * `codim V_0 <= |H|^2 eps n`, and each `s(h)^-1 V_0` has the same codimension.
  * For `v ∈ U`: `s(k)v ∈ V_0`, and `s(h)s(k)v = s(hk)v ∈ V_0`, so `s(k)U ⊆ U`.
  * `s(1)` is an invertible idempotent on `U`, hence the identity.
  * `rho − s` vanishes on `U`, so its rank is at most `codim U`.
* **Proposition 10.** `{k : N_k >= N_0}` contains `K_1 ∩ ... ∩ K_(N_0) ∩ [N_0, ∞)`, which lies in `ω`. At `k`
  the error is at most `C_(N_k) eps_(k,N_k) <= 1/N_k`.
* **Corollary 11(a).** `rho_k(u_13(0,0))` is `o(1)`-close to `sigma_k(x_13(e))`. Transvections are conjugate in
  `H_(N_k)`, and Lemma 3 applies.
* **Corollary 11(b).** Rounding the generators and extending along fixed words changes each word by `o(1)`.
  The result is an injective level-factoring model with displacement tending to `c_0`, so Theorem 4 makes
  `R^x` LEF, which is impossible.
* **Corollary 11(c), checked inside `R^x` and not only on `W_∞`.**
  * Put `r = t0 − sum_(a=1)^M e_(a−1,a)`, so that `x_12(r) = x_12(t0) gamma_M^-1`.
  * `e t0 e = 0` gives `e_(c−1,c) e_ab = delta_(c,a) e_(a−1,b)`. So `r e_ab = e_ab r = 0` for `a, b < M`, and
    `x_12(r)` commutes with every `x_ij(e_ab)` generating `H_M`.
  * If the three corrections were `o(1)`, the Toeplitz defect would be the level-`(M+1)` error of
    Proposition 7, `rho_k(u_13(M,M))`, of displacement `c_0`.
* Agrees with `gk-vf-linear` Section 55.

### 18.2 `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` (OPEN): the established dichotomy checks

* **Radical inside `L`.** Regular representations of finite quotients of the residually finite
  `EL_3(F_2[z, z^-1])` separate points, so the radical lies in `L`.
* **Radical is `1` or `L`.** `L = GL_fin(F_2) = SL_fin(F_2)` is simple, and a normal subgroup of `E` inside `L` is
  normal in `L`.
* **Payoff.** It follows from injectivity of `EL_3(J) -> EL_3(R)` and simplicity of `R^x`.
* **Partial check on `psi`.** Finite-rank perturbations keep index `−1`, so `S + f` cannot be surjective.
* **Status.** Open, and not decided here.
