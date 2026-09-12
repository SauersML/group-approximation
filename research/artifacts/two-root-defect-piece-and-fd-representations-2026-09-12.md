# The two-root defect piece, and what the absence of finite-dimensional representations buys

Lane `w3-gate-bridge-b`, 2026-09-12. Supports the Cairn claim
`leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model` and
`kazhdan-groups-without-fd-reps-violate-two-root-identity`, and the Attempts entry on
`rank-models-of-el3-satisfy-the-two-root-identities`. It continues Section 3 of
`research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md`.

## 0. Summary

* **Section 1 (established).** Take a nontrivial characteristic-two rank model of `R^x`. The
  defect piece `Q = im(N'_23 N'_12)` of the corner pair on `[1000]` is invariant under the nine-leaf
  Kazhdan subgroup `Gamma`, and never pointwise fixed by it.
  * `Gamma` acts on `Q` by a nontrivial, injective rank model of `R^x`, of normalized rank
    `delta = rk(N'_23 N'_12)`.
  * Every corner-pair product inside `Gamma` compresses nontrivially onto `Q`.
  * A compressor carrying the pair into `Gamma` compresses nontrivially onto `Q`.

  So the fixed case of step 1 of the mechanism artifact is closed, and the invariant case
  reproduces the whole problem on a corner.
* **Section 2 (established).** A calibration for input (ii): a finitely generated Kazhdan group
  with no nontrivial finite-dimensional representation, whose rank model violates the two-root
  identity and has a diffuse relative commutant.
* **Section 3.** Where input (ii) can still enter.

Notation as in the mechanism artifact.
* `R = L_(F_2)(1,2)`, with prefix isometries `S[p]`, `T[p]`.
* `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`, an injective endomorphism of `R^x`.
* `Gamma = iota_0(R^x)`, the units supported on `[0]`.
* `x' = iota_1000(x_12(1))`, `y' = iota_1000(x_23(1))`.
* `sigma : R^x -> M^x` is a homomorphism into the units of a rank ultraproduct `M` over a field
  of characteristic two.
* `N'_12 = sigma(x') - 1`, `N'_23 = sigma(y') - 1`, `P = N'_23 N'_12`.

`M` is von Neumann regular with a faithful rank function, so `PM = qM` for an idempotent `q`,
with `rk(q) = rk(P)`. A corner `eMe` with `e != 0` is again a rank ultraproduct after
renormalizing, because idempotents lift at finite stages.

## 1. The defect piece carries a nontrivial rank model

**Lemma 1.1 (invariant corners).** Let `sigma : G -> M^x` be a homomorphism, `S <= G` a subgroup,
and `q` an idempotent with `sigma(s) qM = qM` for every `s` in `S`. Then
`sigma(s) q = q sigma(s) q`, and `tau_q(s) = q sigma(s) q` is a homomorphism `S -> (qMq)^x`.

*Proof.* `sigma(s) q` lies in `qM`, so `sigma(s) q = q sigma(s) q`. For `s, t` in `S`,
`q sigma(s) q sigma(t) q = q sigma(s) sigma(t) q`, since `sigma(t) q = q sigma(t) q`. Also
`tau_q(1) = q`, and `tau_q(s^-1)` inverts `tau_q(s)`. QED

**Fixed right ideals.** For a subgroup `S` write `Fix_r(sigma(S)) = {x in M : sigma(s) x = x for
all s in S}`. For finitely generated `S` this is `eM` for an idempotent `e` with
`sigma(s) e = e` (Lemma 1 of `research/artifacts/rank-row-compression-audit-2026-09-12.md`). By
`leavitt-rank-models-kazhdan-fixed-ideals-are-global` in degree `(1,0)`,
`Fix_r(sigma(Gamma)) = Fix_r(sigma(R^x))`.

**Theorem 1.2.** Let `sigma` be a nontrivial characteristic-two rank model of `R^x`, and `q` an
idempotent with `qM = PM`.

1. `qM` is `sigma(Gamma)`-invariant, and `tau_Q(gamma) = q sigma(gamma) q` is a homomorphism
   `Gamma -> (qMq)^x`.
2. `tau_Q` is nontrivial. So `tau_Q o iota_0` is an injective rank model of `R^x` on the corner
   `qMq`, of normalized rank `rk(q) = rk(P) > 0`.
3. For every prefix `P'`, with `N^(0P')_ab = sigma(iota_(0P')(x_ab(1))) - 1`,

   ```text
   rk( q N^(0P')_23 N^(0P')_12 q ) > 0 .
   ```

4. `qM` is not contained in `Fix_r(sigma(Gamma))`.

*Proof.*

1. `x'` and `y'` are supported on `[1000]`, which is disjoint from `[0]`, so they commute with
   `Gamma`. Hence `P` commutes with `sigma(Gamma)`, and `sigma(gamma) PM = P sigma(gamma) M = PM`.
   Apply Lemma 1.1.
2. Suppose `tau_Q` is trivial, that is, `q sigma(gamma) q = q` for all `gamma` in `Gamma`.
   * **Fixed.** By Lemma 1.1, `sigma(gamma) q = q`, so `qM` lies in `Fix_r(sigma(Gamma))`. By
     globality it lies in `Fix_r(sigma(R^x)) = fM`, where `sigma(g) f = f` for every `g`. So
     `P = fP`.
   * **Quotient model.** Put `sigma_W(g) = (1-f) sigma(g) (1-f)`. From `sigma(g) f = f` we get
     `(1-f) sigma(g) f = 0`, so `sigma_W` is a homomorphism into `((1-f)M(1-f))^x`. If `f = 1`
     then `sigma` is trivial, a contradiction. Otherwise `(1-f)M(1-f)` is a rank ultraproduct
     over the same field.
   * **Its corner product vanishes.** `N'_23 f = (sigma(y') - 1) f = 0`, so
     `(1-f) N'_23 (1-f) = (1-f) N'_23`, and

     ```text
     (sigma_W(y') - (1-f)) (sigma_W(x') - (1-f)) = (1-f) N'_23 N'_12 (1-f) = (1-f) f P (1-f) = 0 .
     ```

     By `two-root-identity-is-corner-local-for-leavitt-rank-models` ((3) implies (1), prefix
     `1000`), `sigma_W` is trivial: `(1-f) sigma(g) (1-f) = 1-f` for every `g`.
   * **Square-zero rest.** Now `sigma(g) = f + f sigma(g) (1-f) + (1-f) = 1 + f sigma(g) (1-f)`.
     The elements `1 + a` with `a` in `fM(1-f)` form an abelian group, because
     `(1+a)(1+b) = 1 + a + b`. So `sigma` factors through the abelianization of `R^x`, which is
     trivial (`leavitt-gl-equals-el-and-perfect-unit-group`). So `sigma` is trivial, a
     contradiction.

   Hence `tau_Q` is nontrivial. `tau_Q o iota_0` is a nontrivial homomorphism
   `R^x -> (qMq)^x`, so it is injective because `R^x` is simple
   (`binary-leavitt-unit-group-is-simple`).
3. **Composing corners.** `iota_0 o iota_P' = iota_(0P')`:

   ```text
   iota_0(iota_P'(g)) = S[0P'] g T[0P'] + S[0]T[0] - S[0P']T[0P'] + 1 - S[0]T[0]
                      = S[0P'] g T[0P'] + (1 - S[0P']T[0P']) .
   ```

   So the `P'`-corner pair of the model `tau_Q o iota_0` is `iota_(0P')` of the unit pair, which
   lies in `Gamma`. By Lemma 1.1, `(sigma(gamma) - 1) q = q (sigma(gamma) - 1) q` for `gamma` in
   `Gamma`, so that model's corner product is
   `q N^(0P')_23 q N^(0P')_12 q = q N^(0P')_23 N^(0P')_12 q`. The model is nontrivial by (2), so
   corner locality ((1) versus (3)) makes this product nonzero.
4. This is (2). QED

**Corollary 1.3 (compressor collision).** Suppose `u` in `R^x` conjugates `(x', y')` to
`iota_(0P')` of the unit pair for some prefix `P'`. An example is a prefix replacement taking
`[1000]` onto `[0P']`, such as the configuration's compressor onto `[0001]`. Then
`q sigma(u) q != 0`.

*Proof.* The conjugated pair has product `sigma(u) P sigma(u)^-1`, so Theorem 1.2(3) gives
`q sigma(u) P sigma(u)^-1 q != 0`. Since `P = qP`, this equals
`q sigma(u) q P sigma(u)^-1 q`, so `q sigma(u) q != 0`. QED

**Remark 1.4 (what changes, and where it stops).**
* **Fixed case closed.** Step 1 of Section 3 of the mechanism artifact records that `Q` is
  invariant but not fixed, and that globality only reaches fixed objects. Theorem 1.2 shows the
  fixed case is impossible in a nontrivial model. Globality has therefore already been used in
  full.
* **Self-reproduction.** On `qMq`, `tau_Q o iota_0` has its own configuration and its own defect
  piece `Q_2 = im(q N^(01000)_23 N^(01000)_12 q)`, which lies in `Q`. Iterating gives nested
  corners `Q ⊇ Q_2 ⊇ Q_3 ⊇ ...`, each carrying a nontrivial rank model of `R^x`, with ranks
  `delta >= delta_2 >= ... > 0`.
* **Where it stops.** Nothing proved here gives `delta_(k+1) >= c delta_k` for a uniform `c`, or
  any other bound on the descent. A contradiction along this line must produce such a bound, for
  instance from Corollary 1.3 together with property (T) of `Gamma`.
* **Scope.** Only corner locality uses characteristic two. The rest holds for rank models over any
  field.

## 2. A calibration: a Kazhdan group with no finite-dimensional representations

**The subshift.** Put `z(n) = nu_2(n) mod 2` for `n != 0` and `z(0) = 0`. Let `X` be the orbit
closure of `z` under `(sigma x)(i) = x(i+1)`. For `j >= 1` and `n` not divisible by `2^j`, put
`s_j(n) = nu_2(n) mod 2`. It depends only on `n mod 2^j`.

**Lemma 2.1 (odometer phases).** For every `x` in `X` and `j >= 1` there is `a'` in
`Z/2^(j+1)` with `x(i) = s_(j+1)(i - a')` whenever `i - a'` is not `0 mod 2^(j+1)`. Its reduction
`pi_j(x) = a' mod 2^j` is unique, depends only on `x` restricted to `[0, 2^(j+1))`, and satisfies
`pi_j(sigma x) = pi_j(x) - 1`.

*Proof.*
* **Existence.** For `x = sigma^k z` take `a' = -k`. For `x = lim sigma^(k_n) z`, pass to a
  subsequence with `k_n` constant mod `2^(j+1)`. Agreement at each position passes to the limit.
* **Uniqueness.** Suppose `a'` and `b'` both fit on `W = [0, 2^(j+1))`, and `d = a' - b'` has
  valuation `k <= j - 1`.
  * **Choice of i.** Of the two classes `2^k` and `3·2^k` mod `2^(k+2)` for `i - b'`, exactly
    one gives `i - a' = (i - b') - d` equal to `2^(k+1)` mod `2^(k+2)`. `W` contains every residue
    mod `2^(k+2)`, so pick such an `i` in `W`.
  * **Contradiction.** Then `nu_2(i - b') = k` and `nu_2(i - a') = k+1`, both below `j+1`. So
    `x(i) = k` and `x(i) = k+1` mod 2.

  Hence `a' = b'` mod `2^j`.
* **Locality and equivariance.** Locality is the uniqueness statement. Shifting `x` shifts
  every fitting phase by `-1`. QED

So `C^j_a = pi_j^-1(a)`, for `a` in `Z/2^j`, is a clopen partition of `X` with
`sigma(C^j_a) = C^j_(a-1)`.

**The algebra.** Let `A_X = C(X, F_2) x| Z`, the finite sums `sum f_m u^m`, with
`u f u^-1 = f o sigma`. Then `u chi_(C^j_a) u^-1 = chi_(C^j_(a+1))`, and `A_X` is generated by
`u`, `u^-1` and `chi = [x(0) = 1]`, because `u^i chi u^-i = [x(i) = 1]`. For
`a, b in {0, ..., 2^j - 1}` put `e_ab = u^(a-b) chi_(C^j_b)`. Since
`chi_(C^j_b) u^m = u^m chi_(C^j_(b-m))`, these are `2^j x 2^j` matrix units with
`sum_a e_aa = 1`. So `A_X` contains `M_(2^j)(F_2)` unitally, for every `j`.

**Lemma 2.2 (degree bound).** For `N >= 3` and any field `K`, every nontrivial homomorphism
`SL_N(F_2) -> GL_d(K)` has `d >= floor(N/2)`.

*Proof.* `SL_N(F_2)` is simple, so the homomorphism is injective.
* **char K != 3.** Block matrices built from `floor(N/2)` blocks `c = [[0,1],[1,1]]` of order
  three give `(Z/3)^floor(N/2)` inside `SL_N(F_2)`. Its image is a commuting family of elements of
  order dividing 3, simultaneously diagonalizable over the algebraic closure with eigenvalues in
  `mu_3`. So it injects into `mu_3^d`, and `floor(N/2) <= d`.
* **char K = 3.** The matrices `[[I, Y],[0, I]]` with `Y` of size `floor(N/2) x ceil(N/2)` give an
  elementary abelian 2-group. Commuting involutions in characteristic three diagonalize with
  eigenvalues `+-1`, so `floor(N/2) ceil(N/2) <= d`. QED

**Proposition 2.3.** `H = EL_3(A_X)` has no nontrivial homomorphism into any `GL_d(K)`.

*Proof.* Choose `j` with `floor(3·2^j / 2) > d`.
* **The finite subgroup.** The unital copy of `M_m(F_2)`, `m = 2^j`, gives
  `EL_3(M_m(F_2)) <= H`. This is `SL_(3m)(F_2)`: it contains every elementary transvection between
  different blocks, and commutators of those give the ones inside a block.
* **It dies.** By Lemma 2.2 it dies in `GL_d(K)`, so `rho(x_12(1)) = 1`.
* **Normal generation.** `x_13(b) = [x_12(1), x_23(b)]`, so `rho` kills `x_13(A_X)`. Permutation
  matrices lie in `EL_3(F_2) <= H` and conjugate `x_13(A_X)` onto every root subgroup, and root
  elements generate `H`. QED

**Lemma 2.4 (a unital rank model of `A_X`).** There is a unital ring homomorphism `phi` from `A_X`
into a rank ultraproduct over `F_2`.

*Proof.*
* **Stage J.** Let `y_J` be the `2^J`-periodic configuration equal to `z` on `[0, 2^J)`, and
  `V_J = F_2^(Z/2^J)`. Put `rho_J(u) e_i = e_(i-1)` and `rho_J(f) e_i = f(sigma^i y_J) e_i` for
  `f` in `C({0,1}^Z, F_2)`. Then `rho_J(u) rho_J(f) rho_J(u)^-1 = rho_J(f o sigma)`, so `rho_J` is
  a representation of `B = C({0,1}^Z, F_2) x| Z`.
* **The kernel.** Restricting coefficients gives `B -> A_X`, whose kernel is `I_X x| Z`, where
  `I_X = {f : f|_X = 0}`. Take `f` in `I_X` depending on coordinates in `[-r, r]`. If
  `r <= i <= 2^J - 1 - r`, the pattern of `y_J` around `i` is a pattern of `z`, which lies in `X`,
  so `f(sigma^i y_J) = 0`. Hence `rk rho_J(f) <= 2r`.
* **The ultraproduct.** Each kernel element has bounded rank at every stage. So
  `phi = [(rho_J)]` kills the kernel, and defines a unital ring homomorphism on `A_X`. QED

**Theorem 2.5 (calibration).**
1. `H = EL_3(A_X)` is finitely generated and has property (T).
2. `H` has no nontrivial finite-dimensional representation over any field.
3. `H` has a characteristic-two rank model with `rk((x_23(1) - 1)(x_12(1) - 1)) = 2/9`.
4. In the natural model `EL_3(phi)`, the relative commutant of the image contains idempotents
   `p_beta`, `0 <= beta <= 1`, with `rk(p_beta) = beta` and `p_beta p_gamma = p_min(beta,gamma)`.
5. Put `e = chi_(C^1_0)`. The corner pair `x_12(e)`, `x_23(e)` commutes with the Kazhdan subgroup
   `Gamma_H = EL_3((1-e) A_X (1-e))`, embedded by `g -> g + e I_3`. In the tensor-square model:
   * the pair's defect piece has normalized rank `1/18` and is pointwise fixed by `Gamma_H`;
   * it is not fixed by `x_12(e)`;
   * so `Fix_r(Gamma_H)` is not contained in `Fix_r(H)`, and globality fails.

*Proof.*
1. `A_X` is a finite-type `F_2`-algebra, so `EL_3(A_X)` is generated by the root elements of the
   algebra generators, and `elementary-group-property-t-over-free-algebras` gives (T).
2. Proposition 2.3.
3. Lemma 2.4 and `rank-modelled-coefficients-violate-two-root-identities`.
4. **Truncations.** At stage `J` let `p_(beta,J)` project onto `span{e_i : i < floor(beta 2^J)}`.
   It commutes with diagonal matrices, and `rk [p_(beta,J), rho_J(u)] <= 2`. So `p_beta` commutes
   with `phi(u)`, `phi(u^-1)` and `phi(chi)`, hence with `phi(A_X)`, and `I_3 (x) p_beta` commutes
   with `EL_3(phi)(H)`.
5. **The corner.**
   * **Kazhdan.** `1 - e = u e u^-1`, so `e` is full. A full corner of a finite-type algebra is of
     finite type: insert `1 = e + u e u^-1` between letters. So `Gamma_H` has (T).
   * **Commuting.** It commutes with `I + E_ab e`, because `e (1-e) A_X (1-e) = 0` on both sides.
   * **The product.** In the tensor square, with `X = E_12 (x) phi(e)` and `Y = E_23 (x) phi(e)`,
     `N_ab = X (x) 1 + 1 (x) X + X (x) X`. Since `YX = 0`, `P_H = Y (x) X + X (x) Y`.
   * **Rank.** Its image lies in `W (x) W` with `W = F_2^3 (x) phi(e) V`, and `rk phi(e) = 1/2`
     (`chi_(C^1_0)` reads four coordinates), so `rk P_H = 2 · 1/36 = 1/18`.
   * **Fixed by Gamma_H.** On `W` every element `g + e I_3` of `Gamma_H` acts as the identity,
     because entries in `(1-e) A_X (1-e)` kill `phi(e)`. So `Gamma_H` fixes `W (x) W` pointwise.
   * **Not fixed by x_12(e).** `N_12 P_H = XY (x) X + X (x) XY` with `XY = E_13 (x) phi(e) != 0`.
   QED

**Remark 2.6 (what the calibration has and lacks).**
* **Has.** Finite generation, property (T), no finite-dimensional representation, corner pairs
  with a Kazhdan subgroup in their centralizer, a violating model, a diffuse commutant.
* **Lacks.** A coefficient ring without rank model, since `A_X` has one. Fixed-ideal globality,
  by (5).
* **Consequence.** Input (ii), even together with (T), does not round almost-invariant pieces, does
  not make the commutant atomic, and does not force the identity. In the Leavitt case, Theorem 1.2
  shows globality in degree `(1,0)` is already fully consumed. What remains specific to `R^x` is
  that `R` has no rank model, and the compression relation.

## 3. Where input (ii) can still enter

* **As a group property it is exhausted.** Section 2 is a finitely generated Kazhdan group with
  no finite-dimensional representation, where the identity fails, the commutant is diffuse, and a
  defect piece is fixed by a Kazhdan centralizer.
* **Forms already landed.** Level-group involution profiles
  (`dyadic-involution-profiles-kill-bounded-degree-content`), and bounded-block models
  (`flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`).
* **Open step.** Along Remark 1.4, bound the descent `delta_(k+1) >= c · delta_k` of the nested
  defect pieces, or build from `tau_Q o iota_0` an approximately multiplicative unital map from
  `R` into a corner. Corollary 1.3 (collision `q sigma(u) q != 0`) together with property (T) of
  `Gamma` is the natural input for the first. Neither is known.
