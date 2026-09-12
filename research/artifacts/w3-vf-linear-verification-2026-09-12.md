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
