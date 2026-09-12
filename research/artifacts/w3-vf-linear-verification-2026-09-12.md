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

## 19. Star designs as a finite certificate (w3-corner-crossed; e79006d8a2, 2ec8fa09e)

### 19.1 `star-compression-design-solves-odd-measure-target`: valid, conditional on the open design claim

* **Why `x*` lies in `B`.** `[g] -> [g^-1]` is an anti-automorphism fixing `eps_-`, which is central. So
  `(y eps_-)* = eps_- y* = y* eps_-`.
* **The conclusion.** With `b' = x`, `c' = x*` and `q_[0] x = x`, we get `c' q_[0] b' = x* x = eps_-`.
* **Precision remark on the finite certificate.**
  * The component of `x* x` at `k` is a sum of the functions `mu -> a_g(g mu) a_h(g mu)`, which read the clopens
    `g^-1 C` for `g ∈ F`.
  * So the partition `P` must refine the translates of the read clopens by `F^-1`, not only by `F^-1 F`. These
    agree when `1 ∈ F`.
  * Restriction `M_- -> M_-^P` is surjective, so identities of functions factoring through it are identities
    on the finite set `M_-^P`.

## 20. Torsion spectra of rank models of V (w4-gate-v2; df1cadf7ed, 3e77da95d3)

### 20.1 `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees` (Theorem 1.3): PASS

* **Lemma 1.1.**
  * `h = g'^k phi g^-k` on `A_k`, and `psi` on `D`, maps the pieces onto the pieces and is piecewise a prefix
    replacement.
  * On `A'_k`, `h g h^-1 = g'^(k+1) phi g^-(k+1) g g^k phi^-1 g'^-k = g'`.
  * At `k = p−1` the wrap uses `g^p = g'^p = 1`.
* **Tree groups.**
  * `tau_w = tau_(w0) tau_(w1)`.
  * For `w' = wv`, `tau_w` permutes the cylinders `[c_k wv]` in the same cycle, so it commutes with `tau_(w')`.
  * Disjoint generators give `(Z/p)^(2^n)`.
* **Lemma 1.2.** `k -> k eps_w` permutes `Z/p`, so the `A_k` are disjoint and `g` shifts them. Words with
  `eps_w = 0` lie in `D`.
* **Theorem 1.3.**
  * **(1)** `|P| = p^m` is invertible, so the `e_chi` are orthogonal idempotents.
  * **(2)** `e_(g,zeta) = sum over chi(g) = zeta of e_chi`.
  * **(3)** Conjugation and Lemma 1.1 make `m_zeta(g)` global.
  * **(4)** Reindexing `k' = jk` gives `e_(g^j, zeta^j) = e_(g,zeta)`, and `g^j` is a clopen `p`-cycle. So `m_zeta` is
    constant on `zeta != 1`, since `(Z/p)^x` is transitive on primitive roots.
  * **(5)** `sum_(zeta != 1) zeta = −1`, so the transform is `c − (1−c)/(p−1) = a` off the identity, and inversion
    holds on `P^`.
  * **(6)** Positivity at `chi != 1` and at `chi = 1`, with `|E_n| -> ∞`, gives `0 <= a <= 1`.
  * **(7)** `sigma(tau) − 1 = sum_(zeta != 1)(zeta − 1) e_(tau,zeta)` has rank `1 − c = (1−a)(p−1)/p`.
* **Corollary 1.4.** Simplicity of `V`.

### 20.2 Calibration and slopes (Sections 2–3): PASS

* **Proposition 2.1.** `F[K]` restricted to `<g>` is `|K|/o` copies of `F[t]/(t^o − 1)`. There `P(t)` has kernel of
  dimension `deg gcd(P, t^o − 1)`, and on the trivial summand the rank is `[P(1) != 0]`. The limit depends only on `a`,
  `P` and `o`.
* **Proposition 3.1.** Length changes along `h^-1`, `g`, `h` cancel. The second `h` is applied at `g x = x`.
* **Example 3.2.**
  * `x_0` fixes `0^∞` (slope `|00| − |0| = +1`) and `1^∞` (slope `|1| − |11| = −1`), and no other point.
  * `x_0` lies in `F` and has no non-fixed periodic points, so `Fix(x_0^k) = Fix(x_0)`, with slopes `±k`.
* **Scope.** The revealing-pair remark is correctly marked unverified and unused.

## 21. Level-factoring and HNN models in characteristic three (w4-char3-construct; c48c760e43, 861b813c16)

### 21.1 `char-three-level-factoring-models-of-leavitt-units-are-trivial` (Theorem 1.4): PASS, conditional scope

* **Lemma 1.1(a).** In characteristic three a transvection has order three. A projective module is free over
  `<t>`, so `t − 1` has rank `2/3` of its dimension.
* **Lemma 1.3 over `F_3`.**
  * A non-scalar `x` has some `v` with `xv ∉ F_3 v`.
  * With `u^-1 = 1 − B` we get `[x,u] = (1 + A)(1 − B) = 1 + A − B`, since `AB = 0`.
  * `N != 0`, because `N y = psi(y) xv − φ(y) v` with `xv` and `v` independent.
  * Second commutator: `(1+N) u'' (1+N)^-1 = 1 + (w + Nw) ⊗ chi`, using `chi o N = 0`. Then
    `[1+N, u''] = 1 + Nw ⊗ chi`, using `chi(w) = 0`.
* **Theorem 1.4.**
  * **(2)** The centre of `GL_m(F_3)` is `{±1}`.
  * **(3)** `Phi` is a homomorphism into the algebraic ultraproduct of the `PGL_(m_k)(F_3)`.
  * **(4)** `Phi(w) = 1` forces `tau'_k(w) = ±1`, so `sigma'(w)` is central and `w ∈ Z(G)` by injectivity of
    `sigma'`. Simplicity of `PG` gives `Z(G) = <z>`.
  * **(5)** `G / ker Phi` embeds in an algebraic ultraproduct, so it is LEF, hence sofic, against the cited
    nonsoficity of `G` and `PG`.
* **Conditional scope.** Rests on:
  * simplicity of `PG` (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, with its imports);
  * nonsoficity of `G` and of `PG` (cited);
  * Theorem 2.1 of the characteristic-three gate (Section 11.1 above).
* **Corollary 1.5(b).** The twisted regular module `F_3[GL_m(F_3)] eps_-` is projective, since `z` has order two,
  which is prime to three.

### 21.2 `level-unit-hnn-extensions-have-anti-central-rank-models` (Theorem 2.1, Theorem 2.3, Corollary 2.4): PASS, one precision remark

This is a rank-model construction, checked with full care. It models HNN extensions of `L`, not `G_3`, so the gate is
untouched.

* **Theorem 2.1.**
  * `((1 − [z])/2)^2 = (2 − 2[z])/4 = eps_-`.
  * `F_3[L_j]` is free over `F_3[<z>]`, so `dim V_j = |L_j|/2`.
  * Level compatibility gives exact multiplicativity for `j >= j_0`.
  * Coset decomposition with central `eps_- ∈ F_3[Γ]` gives freeness of rank `[L_j : Γ]`.
  * **Injectivity.** For `a ∉ {1, z}` the supports `{a, az}` and `{1, z}` are disjoint, so `[a] eps_- != eps_-`. The
    rank of `[a] − 1` is `r >= 1` on `F_3[Γ] eps_-`, hence `2r/|Γ|` at every stage.
* **Theorem 2.3.**
  * `B_g` is a subgroup containing `z`, and `phi_g` fixes `z`, hence `eps_-`.
  * `i(j) -> ∞`, since for fixed `i_0` the level `j >= max(i_0, c(i_0))` works.
  * At stage `j`, `V_j` is free of rank `[L_j : Γ_i]` over `F_3[Γ_i] eps_-` through `sigma_j`, and through
    `sigma_j o phi_g`, since `phi_g(Γ_i) ∋ z` has the same order. Free modules of equal rank are isomorphic, which
    gives an exact `X_j`.
  * A fixed `a` lies in `Γ_(i(j))` for ω-almost all `j`.
* **Corollary 2.4.** The defining relations hold in `M^x`, and `t_g -> g` respects them.
* **Precision remark (Remark 2.5, torsion letters).**
  * **The gap.** "`n` divides `[L_j : Γ_i]` for large `j`" holds for each fixed `i`, since `ν_ℓ |GL_(2^j)(F_3)| -> ∞`
    for every prime `ℓ`. But `i = i(j)` moves with `j`, and `|Γ_(i(j))|` grows too.
  * **Repair.** Put the divisibility into the choice: take `i(j) = max{i <= j : c(i) <= j` and
    `n | [L_j : Γ_i]}`. For fixed `i_0` all conditions hold for large `j`, so `i(j) -> ∞` still.
  * **Transport step.** `F_3[Γ_i ⋊ Z/n]` is free of rank `n` over `F_3[Γ_i]`, and `eps_-` stays central because
    `phi_g` fixes `z`. So the transported generator gives `X_j^n = 1` with the intertwining property.
  * **Status.** The author applied this repair at `e1854a7722`.

## 22. Older L-family route with no verdict anywhere

A sweep of routes from the older `gk-l*` and `gk-r*` lanes against every verification artifact on main found
one route whose id and target appear in none of them. Every other target claim found in the sweep is
covered by some verification artifact.

### 22.1 `quaternary-leavitt-family-gives-anti-central-cohn-family`: valid, conditional on the open quaternary family

If `tau_i sigma_j = delta_ij 1_-` for `i, j <= 4`, the relations for `i, j <= 2` are among them. So `sigma_1, sigma_2,
tau_1, tau_2` is a unital two-pair Cohn family. The completeness relation `sum sigma_i tau_i = 1_-` is not needed.

## 23. Sylvester rank functions and the two-root defect (w4-rankfn; 5d0606ab57)

### 23.1 `leavitt-rank-functions-killing-two-root-defect-are-augmentation` (Theorem 1): PASS

This is a gate reduction, checked with full care. It proves no identity and constructs no model.

* **Setup.**
  * The three-leaf code gives `M_3(R) ≅ R`, and `GL_3 = EL_3` holds for every field
    (`leavitt-gl-equals-el-and-perfect-unit-group`, "every rank `n >= 2` and every field").
  * In characteristic two, `N_12^2 = [x_12(2)] + 1 = 0` in `K[Γ]`.
* **Quotient.**
  * `I = {rk = 0}` is a two-sided ideal, a matrix with entries in `I` has rank `0`, and `rk_B` is faithful.
  * Weyl symmetry turns the two identities into `N_ab N_cd = 0` for `b != c`. Signed permutation matrices lie in
    `EL_3(K)`, and if `(1+N)^-1 − 1 = M` with `M^2 = 0`, then `N = −M`.
* **[TRI] Theorem A.** Its converse uses only `X^2 = Y^2 = YX = 0`, so it is ring algebra, and it gives the matrix
  units in `B`.
* **Corner homomorphism, `p = 2`.** [RR] Proposition 6 is stated for rings of characteristic two. It uses
  `n^2 = 0` from `(1+n)^2 = 1`, the five-term commutator expansion, and block entries.
* **Corner homomorphism, `p` odd.** [RR] Proposition 8's proof was re-read step by step.
  * `Phi` on `M_3(F_p)`, with `(1+u)^λ = 1 + λu`.
  * Triangular order `(p_1, f, p_3)` gives `D^p = S^p = 0`.
  * The torus `diag(−1,−1,1)` gives `2D + D^2 = 0`, `2S + S^2 = 0` and `2Q + QD + SQ = 0`. A unit plus a nilpotent
    is invertible, so `D = S = Q = 0`.
  * `diag(1,−1,−1)` gives `2P = 0`, then Weyl transport.
  * No rank is used. [RR] Corollary 9's computation `C(ab) = psi_13(ab) u_31 = C(a) C(b)` is ring algebra.
* **No room in the corner.**
  * `rk_B/r` restricted to matrices over `p_1 B p_1` satisfies each Sylvester axiom, with `rk'(p_1) = 1`.
  * Pulling back along the unital `C` gives a Sylvester function on `R`.
  * `t_i (s_i t_i) s_i = 1` gives `rk''(s_i t_i) >= 1`. With [DI] 2.1 additivity
    (`diag(f_1, f_2) = [f_1; f_2][f_1, f_2]` and `[f_1, f_2] = (f_1 + f_2)[f_1, f_2]`), `1 >= 2`.
* **Triviality.**
  * `p_1 = 0` gives `u_ij = u_i1 u_1j = 0`.
  * `ker sigma` is normal and contains `[x_ik(a), x_kj(1)] = x_ij(a)`, so `sigma` is trivial on `EL_3(R) = Γ`.
  * [DI] Theorem 1.1(3) gives `rk_ε`.
* **Corollary 4.** The normalized rank of `M` pulls back along the linear extension to a Sylvester function, and
  faithfulness gives `sigma = 1`. So the Sylvester gate implies the ultraproduct gate.
* **Scope.** Corollary 5 also lists `toeplitz-isometry-defects-have-total-rank-at-least-one` as transferable. That was
  not re-derived here.

## 24. Abstract Sylvester scope for the characteristic-three gate (w3-gate-char3; 1bace02f7e, artifact Section 7)

### 24.1 Proposition 7.1: PASS

* **(F1)–(F3).** They follow from the axioms: additivity as in Section 23.1, conjugation from submultiplicativity
  both ways, and corner renormalization.
* **(a) Only (1) ⟹ (6) uses the rank function.**
  * `f = 2(1 − sigma(z))` is a nonzero idempotent central in `sigma(G)`, so `rho(f) > 0` and (F3) makes `fMf` an
    abstract rank algebra.
  * Lemma 1.1, (2) ⟹ (3), (4) ⟹ (5) and (5) ⟹ (3) are group theory together with injectivity of `iota` and
    `pi o iota`.
  * Excluding (6) ⟹ (4) is correct: Lemma 1.2 uses Kronecker products and Jordan forms.
* **(b)** Theorem 2.1 of the state-sources artifact is stated for Sylvester functions positive on idempotents.
* **(c)** The half split uses (F1), (F2) and `rho(1) = 1`. The atoms use (F1), and the Fourier inversion is arithmetic.
* **(d)** These are ring identities.
  * `(1 ± t)/2` are idempotents for involutions `t`.
  * Commuting with `sigma(τ_11)` and `sigma(τ_0 τ_10)` cuts out the components.
  * `N^3 = 0`, and conjugation by `τ_0` gives `D = −N^2`.
  * 5.1(c) is (c) at the code `(0,10,11)`.

### 24.2 Corollary 7.2 (rank functions are models): PASS

* **The ideal.** `ker N` is two-sided, by submultiplicativity and `a + b = (1 1) diag(a, b) (1 1)^T`.
* **Descent.** A matrix with entries in `ker N` has rank `0`, so `N` is constant on classes and positive on nonzero
  classes.
* **The model.** `eps_- [g]` has inverse `eps_- [g^-1]`. `eps_-[z] = −eps_-`, and `N(2 eps_-) = N(−eps_-) = 1`, so
  `1 != −1` in the quotient.
* **Scope.** The abstract "No" branch is stronger than the matrix form, and the matrix-unit, unipotent and flag
  triviality results need their own scope checks, as the artifact says.

## 25. Rank kill versus the counterexample (w3-strategist-neg; 0f7afb4dea, artifact Section 4.4)

### 25.1 Equivalences in `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (OPEN): PASS

* **Normalization.**
  * Take `rk` on `F_3[G]` with `rk(eps_-) = t > 0`. A matrix `X` over `S_-` has `eps_- X = X`, so `N(X) = rk(X)/t`.
  * Each Sylvester axiom (products, block sums, triangular blocks, `N(0) = 0`) is the same axiom for `rk` divided by
    `t`, and `N(eps_-) = 1`.
* **Extension.**
  * `eps_-` is a central idempotent, so `X -> eps_- X` is a unital ring homomorphism `F_3[G] -> S_-`.
  * `rk = N o (eps_- ·)` is a pullback along it, hence a Sylvester matrix rank function, with `rk(eps_-) = 1`.
* **The whole-algebra form.**
  * `1 − [z] = 2 eps_-` and `2` is a unit, so `rk(1 − [z]) = rk(eps_-)`. So (NR) holds iff every `rk` on `F_3[G]` kills
    `1 − [z]`.
  * The node's `eps_- = (1 − [z])/2` agrees with `2(1 − [z])`, since `1/2 = 2` in `F_3`.
* **Abstract models, model ⟹ `N`.**
  * `sigma(z) = −1` makes the linear extension `phi : F_3[G] -> M` unital, and `rho o phi` is a pullback Sylvester
    function.
  * `rho(phi(1 − [z])) = rho(2) = 1`. Positivity of `rho` on idempotents is not needed.
* **Abstract models, `N` ⟹ model.** This is Corollary 7.2 (Section 24.2).
* **The matrix "No" branch.** A nontrivial matricial model moves `z` (Section 11.1), and a faithful ultraproduct rank
  gives `rho(1 − sigma(z)) > 0`.

### 25.2 `ternary-counterexample-from-rank-kill-and-state-realization`: valid, conditional on two OPEN claims

* **Chain.**
  * The contrapositive of (U1) turns (NR) into (NS).
  * Part 2 of `anti-central-state-obstruction-equals-stable-finiteness` turns (NS) into `k u <= 0` for some `k`.
  * `k u <= 0` means `−k u = [Q]`, so `[Q ⊕ S_-^k] = 0`, that is, `S_-^r ≅ S_-^r ⊕ S_-^k ⊕ Q` for some `r`. That is the
    target exactly.
* **Necessity of the first requirement.**
  * The target gives no state: `s(k u) = k > 0` contradicts `k u <= 0`.
  * No state gives (NR): a normalized `N` gives the state `s([e S^n]) = N(e)`.
    * Equivalent idempotents `e = xy`, `f = yx` (with `x ∈ eMf`, `y ∈ fMe`) have `N(e) <= N(y) = N(yxy) <= N(f)`,
      and symmetrically.
    * Block sums add, and the Grothendieck property extends `s` to `K_0`.
  * So, given (U1), target ⟺ (NR).
* **Downstream route.** In `nonpositive-unit-class-refutes-ternary-surjunctivity`, `BA = 1 != AB` over `S_-`,
  padded by the central `eps_+ = 1 − eps_-`, is a one-sided pair in `M_r(F_3[G])`.

### 25.3 Body of `ternary-anti-central-states-give-sylvester-rank-functions` (OPEN): consistent

* **State versus rank condition.**
  * A state exists iff `[eps_-]` is not `<= 0`.
  * `u <= 0` iff `S_-^(r+1) ⊕ Q ≅ S_-^r` for some `r`, which is failure of the rank condition.
* **A rank function always gives the rank condition.** A summand `S_-^(n+1)` of `S_-^n` gives an idempotent in
  `M_n(S_-)` equivalent to `I_(n+1)`, so `n + 1 <= n`.
* **Risk paragraph.** The converse is correctly marked unverified, and nothing depends on it.

## 26. Jacobson rank radical Attempts (w3-gate-construct; 5bc7fc0bc, 84327b445)

These are Attempts entries on the OPEN `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`. Both check.

### 26.1 The shift-reversal `psi` does not extend: PASS

* **The shift.**
  * `a = a_12 = [[S, Q],[0, T]]` of `binary-jacobson-active-cycle-generates-rank-three`, which is `WP` with `P` the
    transposition of components `i`, `j`.
  * On basis vectors: `δ_b^(i) -> δ_(b+1)^(i)`, `δ_0^(j) -> δ_0^(i)`, `δ_b^(j) -> δ_(b−1)^(j)`. That is the stated
    single orbit.
* **First commutator.** With `u − 1 = sum_c δ_c^(j) ⊗ δ_c^(i)*`:
  * `a^-1 (u−1) a = sum_(b>=0) δ_(b+2)^(j) ⊗ δ_b^(i)* + δ_1^(j) ⊗ δ_0^(j)*`, matching the entry after reindexing.
  * Its image lies in component `j` and it reads components `i`, `j`. `v − 1` reads `i` and writes `k`.
  * So both products vanish, `a^-1 u a`, `u` and `v` pairwise commute, and `[[a^-1, u], v] = 1`.
* **Second commutator.** `a (u−1) a^-1 = δ_0^(i) ⊗ δ_1^(i)* + sum_(c>=1) δ_(c−1)^(j) ⊗ δ_(c+1)^(i)*`.
  * `(v−1)(a u a^-1 − 1) = δ_0^(k) ⊗ δ_1^(i)* != 0`, while the reverse product is `0`.
  * `u` commutes with `v`, so `[a, u]` does not commute with `v`, and `[[a, u], v] != 1`.
* **Conclusion.** An endomorphism fixing the constants with `a -> a^-1` would send the first relation to the
  second, so none exists, and the LEF criterion yields nothing.

### 26.2 Level models of `E_5 = EL_5(J)` die, and the MF transfer stops: PASS, cited inputs

* **Head-retaining models are injective.**
  * `ker sigma ∩ L` is normal in the simple `L = SL_fin(F_2)`, and `x_13(Q) ∈ L` survives, so the intersection is
    trivial.
  * `[ker sigma, L] ⊆ ker sigma ∩ L = 1`.
  * An operator on `F_2^(N x [n])` commuting with every finitary transvection `1 + v ⊗ φ` sends each `v` into
    `F_2 v`, so it is scalar, hence `1`. The natural representation of `J` is faithful.
* **Finite images kill the head (n >= 4).**
  * **Pigeonhole.** It gives `x_13(e_ab + e_a'b') -> 1` with `(a,b) != (a',b')`.
  * **The chain.** `[x_13(r), x_32(p)] = x_12(rp)`, `[x_31(q), x_12(rp)] = x_32(qrp)`,
    `[x_13(p'), x_32(qrp)] = x_12(p'qrp)` and `[x_12(p'qrp), x_23(1)] = x_13(p'qrp)`.
  * **Reaching the head.** `Q S = S − STS = 0` and `T Q = 0` give `e_ab e_cd = δ_bc e_ad`. So `e_0a r e_b0 = e_00 = Q`,
    since the second term needs `a = a'` and `b = b'`.
* **Not LEF.** A finitely presented Steinberg cover with finite-image collapse is not LEF. Finite presentation of
  `St_n(J)` is cited (`steinberg-finite-presentation-and-kazhdan-theorem`), not re-derived.
* **What transfers.**
  * `uHu^-1 <= H` gives `σ(u) F ⊇ F`, with equal rank, so `σ(u) F = F` by faithfulness.
  * `σ(c)` commutes with `σ(H)`, and `x_23(1) ∈ H` fixes `F` pointwise.
  * So `[u c u^-1, x_23(1)] = x_13(Q)` is the identity on `F`.
* **Blocks 1–2.** Prose, consistent.

## 27. Diagonal tensor images carry no rank function (w4-tensor-rankfn; artifact at d595e11a8)

### 27.1 `odd-char-leavitt-unit-tensor-images-have-no-rank-function` (Theorem 1, `2 <= n < p`): PASS

* **Step 1.**
  * `(1 + sum_(k∈T) e_ij(a_k))^(⊗n)` expands over slot maps `f : [n] -> {0} ∪ T`.
  * `sum_(T ⊇ im f) (−1)^(n−|T|) = [im f = [n]]`. With `n` slots, `f` must be a bijection onto the indices, which
    gives `Sym_ij`.
  * `B_n` is a `K`-subalgebra, so it contains `Sym_ij`.
* **Step 2.**
  * `e_21(t) e_12(s) = e_22(ts)`, and `t_γ s_δ = [γ = δ]` for incomparable words.
  * For `a = b` only `σ = τ` survives, giving `n!` copies of `P_2`, so `T_a S_a = P_2`. This uses `n!` invertible,
    that is, `n < p`.
  * For `a != b` all terms vanish. Then `f_a^2 = S_a P_2 T_a = f_a`, `f_0 f_1 = 0`, and `f_a <= P_1`.
* **Step 3.**
  * `rk f_a >= rk(T_a f_a S_a) = rk P_2`, so `rk P_1 >= rk f_0 + rk f_1 >= 2 rk P_2`.
  * `w = [[0,1,0],[−1,0,0],[0,0,1]]` has determinant `1`, and `w e_22 w^-1 = e_11`, so `rk P_1 = rk P_2 = 0`.
* **Step 4.**
  * `V`-transitivity on proper nonempty clopens (Section 7.1) makes every `p_A^(⊗n)` null.
  * Möbius inversion `Π_S = sum_(T ⊆ S)(−1)^(|S|−|T|) p_(A_T)^(⊗n)` and `1 = sum_(1 <= |S| <= n) Π_S` give `rk 1 = 0`.
* **The two forms.** A rank function vanishing on `ker Δ_n` descends to a quotient of `B_n`, and a map out of
  `B_n` pulls back.
* **Scope.** This is a no-go for one construction handle. The binary case and the degrees `n >= p` are open, as
  stated.

### 27.2 Binary tensor squares (artifact Section 2 at 1fe572ead): PASS

* **Lemma 2.1.**
  * `N = (1 + flip)(R ⊗ R)` is an ideal of the flip-fixed algebra, because `z (1+flip)(w) = (1+flip)(z w)` for
    flip-fixed `z`.
  * `(x+y)^(⊗2) = x^(⊗2) + y^(⊗2) + Sym(x,y)`, so `Φ` is a ring map mod `N`.
  * The flip permutes `b_i ⊗ b_j`, and `N` is spanned by `Sym(b_i, b_j)` for `i != j`. So `T(R)` has basis
    `[b_i ⊗ b_i]` and `Φ(1) != 0`.
  * `R` is simple, so `Φ` is injective, and `B_2/(B_2 ∩ N) ≅ R`.
* **Proposition 2.2.**
  * **Norms.** Summing `(1+x)^(⊗2)` over `{0, u, v, u+v}` kills the `1⊗1` and linear terms and leaves `Sym(u,v)`.
  * **Square-zero isometries.** The ranges `X_a`, `Y_b` and sources `X'`, `Y'` are pairwise disjoint, so
    `u^2 = v^2 = uv = vu = 0`.
  * **Products.** `Sym(u,v) Sym(u',v') = Sym(uu', vv') + Sym(uv', vu')`, so `T_ab S_cd = [a=c][b=d] Sym(p_(X'), p_(Y'))`
    and `S_ab T_ab = Sym(p_(X_a), p_(Y_b))`.
  * **Idempotents.** The `E_ab` are orthogonal idempotents with sum `E = Sym(p_X, p_Y)`, which is an idempotent in
    `B_2`.
  * **Rank.** `rk E_ab >= rk(T_ab E_ab S_ab) = rk Sym(p_(X'), p_(Y'))`, and conjugating by the first-letter swap
    gives `rk E >= 4 rk E`.
  * **All pairs.** `V` is transitive on ordered disjoint pairs with nonempty complement, by the Lemma 2.2
    refinement argument.
* **Corollary 2.3.**
  * `1 ⊗ 1 = Q_P + O_P`, with `O_P ∈ B_2` null and `Q_P ∈ B_2`.
  * `z − Q_P z Q_P = Q_P z O_P + O_P z Q_P + O_P z O_P` has rank `0`.
  * A rank function vanishing on the ideal `B_2 ∩ N` of `B_2` descends to `R`, which has none.
* **Theorem 2.4.**
  * `Δ_2(N_23) Δ_2(N_12) = e_12 ⊗ e_23 + e_23 ⊗ e_12`, recomputed with `e_23 e_12 = 0`.
  * `Sym(p_[10], p_[0]) Δ_2(D) = Δ_2(D)`, since `p_[10] e_12 = p_[0] e_23 = 0`. The union `[0] ∪ [10]` misses `[11]`,
    so `rk Δ_2(D) = 0`.
  * The pullback is `rk_ε` by Section 23.1 (characteristic two).
* **Remark on `B_2`.** A rank function on `B_2` pulls back to `rk_ε`, so it exists iff `ker Δ_2 ⊆ ker ε`.
* **Scope.** Degrees `n >= 3` in characteristic two stay open, as stated.

## 28. Fock-local rank models (w4-fock-model; artifact Sections 1–2)

### 28.1 `exterior-tensor-powers-are-asymptotically-free` (Lemma 1.1, Theorem 1.2, Corollaries 1.3–1.4): PASS

* **Free seed.**
  * The stabilizer of a dual basis tuple is trivial.
  * Every function on the finite `Z` is a polynomial of degree `<= w^2(q−1)`.
  * Restriction onto the orbit's permutation module `F_qΓ` is equivariant and onto. A surjection onto a
    projective module splits.
  * `F_q ⊕ W^(⊕w)` is the degree-`<= 1` summand of `(F_q ⊕ W)^(⊗w)`, and `F_q ⊕ W = Λ^0 ⊕ Λ^1` is a graded summand
    of `Λ(W)`.
* **Theorem 1.2.** `F_qΓ ⊗ Y ≅ F_qΓ^(dim Y)`, so every term with a free factor is free. The rest has dimension
  `(1−η)^s 2^(wm)`.
* **Corollary 1.3.** Both free parts have `c|Γ| >= (1−δ)D`. `X` intertwines on the free part, so the difference
  vanishes there and its rank is at most `δD`.
* **Corollary 1.4.**
  * `U_j` restricted to `L_i` is `U_i ⊗ F_q^(2^(j−i))`, so `Λ(U_j) = Λ(U_i)^(⊗2^(j−i))`.
  * Injectivity: left multiplication by `a != 1` on `F_qΓ` has fixed space of dimension `|Γ|/ord a`.

### 28.2 `fock-local-letters-extend-level-models-with-disjoint-commutation` (Theorem 2.2): PASS after two precision repairs

* **Checked.**
  * The exhaustion and `i(j) -> ∞`.
  * Both actions factor through `Γ_i/K` with the same `K`.
  * The non-free bounds and the local intertwiners of Corollary 1.3.
  * (R3) is exact, because `Λ(a) = 1 ⊗ Λ(a|_(A^c))`.
  * Faithfulness of `G` on `U_∞`, since `R` is simple.
* **Repair 1: `B_g^A` must preserve both `LC(A)` and `LC(A^c)`.**
  * An invertible level element preserving only `LC(A)` is block upper triangular. An example is
    `a = 1 + δ_(c1) ⊗ δ*_(c2)` with `c1 ⊆ A`, `c2 ⊆ A^c`.
  * For `g ∈ V` supported on `A`, `g a g^-1 = 1 + δ_(g c1) ⊗ δ*_(c2) ∈ L`, so `a ∈ B_g^A` as written.
  * For such `a`, "φ_g(a) agrees with `a` on `LC(A^c)`" is false, and `Λ(a) = ρ(a) ⊗ Λ(a|)` fails. So step 4 does not
    cover it.
  * With `B_g^A` restricted to block-diagonal level elements, step 4 holds as written. This matches Consequence
    2.4(b), where elements moving mass across the support are excluded.
* **Repair 2: in odd characteristic the letters must be parity-preserving.**
  * `X_g ⊗ 1` is defined through the `A_g`-first identification `ω_A ∧ ω_(A^c) -> ω_A ⊗ ω_(A^c)`.
  * Passing to the `A_h`-first identification costs the sign `(−1)^(|ω_g||ω_h|)`. So `1 ⊗ X_h ⊗ 1` in step 6 is
    `X_h ⊗ 1` only when `X_h` preserves parity.
  * Parity-preserving letters exist. Take `z_A ∈ Γ_i`, which acts by parity on `S_A` and is central with
    `φ_g(z_A) = z_A`, and choose parity-stable complements as in Remark 2.3.
  * In characteristic two the sign is `1`, so no repair is needed.
* **Status.** Both repairs are applied at `3951b78c90`. The claim now defines `B_g^A` through `LC(A)` and
  `LC(A^c)`, and states even letters in odd characteristic. Checked.

### 28.3 `natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter` (Proposition 3.1): PASS

* **Transvections.** `Λ(1 + v⊗φ)` expands with `v` at most once, and `v ∧ i_φ` reproduces the terms with signs
  `(−1)^(i−1)`. So `Λ(u) − 1 = v ∧ i_φ`.
* **Rank.** In the basis `e_1 = v`, `φ(e_2) = 1` and `e_3, ..., e_n ∈ ker φ`, the map sends `e_2 ∧ ω'` to `e_1 ∧ ω'`
  for `ω' ⊆ {3..n}`, and kills every other monomial. So its rank is `2^(n−2) = dim/4`, it preserves degree, and
  it has `2^(n−3)` monomials on each parity.
* **Section 3.2.**
  * If `S(c) ≅ S(c0) ⊗ S(c1)` with all three conjugate under `V`, then `dim S(c) = dim S(c)^2`.
  * `rk(E ⊗ 1)/dim S_j = rk E/dim S_A`.
* **Reading.** Models factoring through `Λ(GL)` have transvection displacement `1/4`, so Section 13.1 and
  Section 21.1 exclude them.

## 29. Jacobson rank radical: support bound, lamplighter cell, symbol firewall (w4-jacobson-radical; e62fcb1db2, f0b171892f)

### 29.1 `jacobson-compression-cell-is-a-commuting-lamplighter` (Proposition 2): PASS

* **(1)**
  * The `x_ij(Q)` are the elementary matrices on `span{δ_0^(1), δ_0^(2), δ_0^(3)}`, so they generate `GL_3(F_2)`.
  * `Q·SaT = SaT − S(TS)aT = 0` and `SaT·Q = 0`. So the root elements commute and `K_1` commutes with `uHu^-1`.
* **(2)** Conjugation gives `K_0 ⊆ C(H)`, and `ucu^-1 = x_12(Q)` gives `c ∈ K_0`.
* **(3)**
  * `u^(j−1) x_ik(Q) u^(1−j) = x_ik(e_(j−1,j−1))`.
  * For `j <= 0`, `H <= u^j H u^-j` gives `K_j <= C(H)`.
  * Conjugating by `u^-i` reduces pairwise commutation to `K_0` against `K_(j−i) <= H`.
* **(4)**
  * `x_ik(1) = x_ik(e) x_ik(1 − e)` with `(1−e)e = e(1−e) = 0`.
  * `x_23(1) = x_23(Q) x_23(ST) = x_23(Q)·u x_23(1) u^-1` gives `u^-1 x_23(1) u = w_0 x_23(1)`.
* **(5)** `GL_3(F_2)` is simple and `x_13(Q) ∈ K_1`.
* **Cited, not re-derived.** The cell identities (manuscript Lemma `lem:ring-compression-cell`).

### 29.2 `jacobson-amenable-symbol-subgroups-are-amenable` (Theorem 3, Corollaries 4–5): PASS

* **Kernel.** `ker pi ⊆ {g : g − 1 ∈ M_n(F)}` consists of finitary matrices, so it is locally finite.
* **Finitary elementary matrices in `L`.** `[x_ik(e_ac), x_ki(e_cb)] = 1 + E_((i,a),(i,b))` for `a != b`. It uses
  `X^2 = Y^2 = 0` and `YX = E_kk ⊗ e_cb e_ac = 0`, so `[1+X, 1+Y] = 1 + XY`. Hence `L = GL_fin(F_2)`.
* **Corollary 4.** `pi(u)` is scalar `z` on coordinates `1–3`, so `pi(B_Λ)` is a quotient of `Z x pi(Λ)`.
* **Tilted constants.** Conjugation by `d = diag(z, z^2, z^3)` sends `x_12(1)`, `x_23(1)`, `x_21(1)`, `x_32(1)` to
  `x_12(z^-1)`, `x_23(z^-1)`, `x_21(z)`, `x_32(z)`, and those four generate `SL_3(F_2)`.
* **Corollary 5.** A permutation with at most `εn` fixed points has at most `εn + (1−ε)n/2` cycles, so
  `rk(P − 1) >= (1−ε)n/2`.
* **Smallest nonamenable set.** The constants with `x_12(T)` give symbol image `EL_3(F_2[z^-1])`, by Weyl
  transport, commutators and additivity.
* **Scope.** This is a subsystem statement. It does not claim `E_4` amenable.

### 29.3 Artifact Proposition 1: PASS, scope remark

* **(1)** The rank form of the support bound is trivial: `rk(1 − e_K) <= 1 <= (κ c_0)^-1 rk(σ(b) − 1)`.
* **Not applied.** The cited `uniform-finite-support-rank-gap-upgrades-compression-collapse` is the unitary
  theorem, with the unnormalized `dim Fix^⊥` against `rank(σ(a) − I)` over finite-dimensional representations. It
  is not applied here, and "hypothesis (1) holds" should be read as its rank analogue.
* **(3)** Tautological: `σ([g,h]) = 1` iff the images commute.
* **(4)**
  * `κ = 1/4` by Lemma 3 inside some `GL_m(F_2)`, `m >= 4`.
  * All transvections of `GL_fin(F_2)` are conjugate in `L`, so each has displacement `c_0`. They generate `L`,
    so the normal closure of the head is `L`.
  * Since `x_13(Q) = [ucu^-1, x_23(1)]`, the model kills the head iff `σ(x_12(Q))` commutes with `σ(x_23(1))`.

## 30. Rank functions on V: fixed rank and wandering freeness (w5-v-infinite-order; 4b35997134, artifact at 84d0bda2e)

### 30.1 Section 0 and the abstract torsion law: PASS

* **Scalar extension.** `res : F'[V] -> M_d(F[V])` comes from the regular representation of `F'`. It is a
  unital ring map compatible with products, blocks and triangular blocks. So `rk(res ·)/d` is Sylvester, and it
  extends `rk` because `res A = A ⊗ I_d`.
* **(S3).** `diag(e, e') = (e; e')(e + e')(e, e')` when `e e' = e' e = 0`.
* **(S4).** Recomputed from `diag(col Y_1, col Y_2)`: add block columns, reorder rows, and subtract the row
  `(c_0 | 0)` from `(c_0 | c_0)`. This gives `[[col(Y_1 ∪ Y_2), B],[0, c_0]]`, and the triangular axiom finishes.
* **(S5), (S6), and independence of `phi_H` from `S`.** They follow from `1 − [gh] = (1−[g]) + [g](1−[h])` and
  `1 − [g^-1] = −[g^-1](1 − [g])`.
* **`phi_P = rk e_P`.** `(1 − [s]) e_P = 0` gives `1 − [s] = (1−[s])(1 − e_P)`, and `1 − e_P = |P|^-1 sum (1 − [g])`.
* **Answer to the audit question: [TS] Theorem 1.3 holds for abstract Sylvester rank functions.**
  * **Exact idempotents.** The `e_chi` are exact idempotents of `F'[V]`, since `|P|` is invertible. There is no
    eigenvalue rounding.
  * **Abstract substitutes.**
    * Step 1's additivity is (S3).
    * Step 3's conjugation invariance is (S1).
    * Steps 5–6 are arithmetic.
    * Step 7 uses `(sum c_i e_i)(sum c_i^-1 e_i) = sum e_i` for units `c_i`.
  * **The one matricial sentence.** "Matrix rank is field-independent" is replaced by the scalar extension above.

### 30.2 `v-rank-torsion-constant-equals-global-fixed-rank` (Lemma 1.1, Theorem 1.2, Corollary 1.3): PASS

* **Lemma 1.1.**
  * Clopen transpositions normally generate the simple `V`.
  * **Fragmentation.** Pieces inside the depth-two cylinders give commuting `t_i`.
  * **The case `A_i ⊆ [00]`, `C ⊆ [11]`.** `r r' r` recomputed pointwise:
    * on `A_i` it is `φψ = t`;
    * on `C` it is `ψ^-1 φ^-1 = t`;
    * on `D` it is the identity.
    * `r` is supported in `[0] ⊆ W`, and `r'` is supported in `[01] ∪ [11] ⊆ U`.
  * **Generators.** `V_O ≅ V` is simple and finitely generated. Its clopen `p`-cycles normally generate it, so
    finitely many generate.
* **Upper bound.** Adding rows cannot lower rank, and (S5) applies, so `phi_V <= phi_P = a + (1−a)/|P|`.
* **Clopen-cycle subgroups.** Disjoint cycles leaving a nonempty complement generate clopen-cycle subgroups,
  products included, as in [TS] Lemma 1.2. So `T_k`, `T'_k`, `T_k x T'_k` and `<s> x T_k` qualify, since `s` is
  supported in `U`, disjoint from `[00]`.
* **Step 1.** `{1 − e_(T_k), 1 − [s]}` and the augmentation elements of `<s> x T_k` generate the same left ideal,
  because `1 − [t] = (1 − [t])(1 − e_(T_k))`. The loss is `(1−a)p^-k(1 − 1/p) <= p^-k`. (S4) in the form
  `phi(Y_1 ∪ Y_2) >= phi(Y_1) + phi(Y_2) − phi(Y_0)` iterates to `a − m p^-k`.
* **Steps 2–3.** The bounds are recomputed as
  `(a − m p^-k) + (a + (1−a)p^-2k) − (a + (1−a)p^-k) >= a − (m+1)p^-k` and
  `(a − (m+1)p^-k) + (a − (m'+1)p^-k) − (a + (1−a)p^-2k) >= a − (m+m'+3)p^-k`.
* **Corollary 1.3.**
  * **(2)** `phi_V <= phi_(V_O)` because the rows of `V_O` lie in the left ideal of the rows of `V`. Also
    `phi_(V_O) <= a` from its tree groups.
  * **(3)** This is DI Theorem 1.1(3)–(4).
  * **(5)** Correctly marked matricial.

### 30.3 `v-rank-models-act-freely-by-wandering-elements` (Lemma 2.1, Setup 2.2, Theorem 2.3): PASS

* **Lemma 2.1.**
  * **Period one, negative slope.** `u` is a proper prefix of `u'`, so `x[u] = [u'] ⊊ [u]`. The forward
    annuli lie in `[u]`, and the backward annuli of the increasing chain lie outside `[u]`.
  * **Period `r`.** For `k = mr + i` with `0 < i < r`:
    * if `m >= 0`, `x^k W ⊆ x^i[u]`, which misses `[u]`;
    * if `m < 0`, `−k = (−m−1)r + (r−i)` reduces to that case.
  * **Positive slope.** It passes to `x^-1`, which has the same translates.
* **Setup 2.2.**
  * The lamps `g_j` have disjoint supports, and their union misses the periodic point, so every `B_J` is a
    clopen-cycle subgroup.
  * `e_ψ = sum over extensions of ψ of e_(ψ')`, so `S -> e_S` is a Boolean homomorphism with `e_C = 1`.
  * `rk e_S = a[1 ∈ S] + (1−a) μ(S)`: the torsion law on cylinders, with `μ = 1/|B_J|`, and (S3) on unions.
  * **Covariance.** Reindexing gives `[x] e_ψ [x]^-1 = e_(ψ o Ad x^-1)` on `B_(J+1)`, which is `e_(TS)`.
* **Theorem 2.3.**
  * **Towers.** The first-return sets `S_h` are clopen, and the levels `L_(h,i)` are disjoint.
  * **Uncovered set.** `1 ∉ S` and `T1 = 1`, so `1 ∈ Z_R`. Two-sided recurrence of the ergodic Bernoulli shift
    gives `μ(Z_R) -> 0`, and `μ(Bot) <= d p^-l`.
  * **Recursion.** Covariance gives `e_L [x]^k = [x]^k e_(T^-k L)`, so for `d <= i < h`,
    `e_(L_(h,i)) q([x]) = sum_k c_k [x]^k e_(L_(h,i−k))`, with `c_0 = q(0) != 0`.
  * **Left ideal.** The base levels satisfy `e_L = e_L e_Bot`, and induction puts every level in
    `R' q([x]) + R' e_Bot`.
  * **Count.** `1 = sum e_L + e_(Z_R)`, and (S6) with `rk e_Bot <= (1−a) d p^-l` and
    `rk e_(Z_R) = a + (1−a) μ(Z_R)` give the bound. Here `rk'` extends `rk`, and `q` has coefficients in `F`.

### 30.4 Section 3 (audit and calibration): consistent

* **Section 3.1.** It matches Section 30.1. Uniform displacement is abstract: `rk([g,h] − 1) <= 2 rk(g − 1)` and
  normality of `N_rk`. The covariance theorem, the `1/4` and `1/32` forms, and the symmetric-group stage theorem
  are correctly marked matricial or vacuous on `F[V]`.
* **Proposition 3.1.**
  * A Følner sofic approximation gives an almost free action, so finite subgroups are regular.
  * An infinite-order `h` has long cycles on most points. A cyclic shift `P_N` has
    `rk q(P_N) >= N − deg q`, so `rk_H q([h]) = 1`.
* **Proposition 3.2.** Elek–Szabó uniqueness is imported at statement level, as marked, and not re-derived. The
  inertness conclusions hold given it.
* **Section 3.3.** Correct: a proof of either gate would show `V` is not sofic, via
  `sofic-implies-linear-sofic-over-every-field`.
