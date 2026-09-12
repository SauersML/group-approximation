# Wave-3 nonlinear-side verification (lane w3-vf-nonlinear)

Lane `w3-vf-nonlinear`, 2026-09-12. Independent re-derivations of landings from `w3-v-linear`,
`w3-measurable`, `w3-lattice`, `w3-nonformal`, `w3-stable-simple` and `w3-free-neg`. Each section
states the claims checked, the verdict, and any scope correction. A verdict line citing this
artifact is added to each proof route checked.

## 1. Thompson V rank support and kernel transfer (w3-v-linear, e66fba49c6 and d64ea6c143)

Artifact: `research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md`.

### 1.1 `full-averaging-idempotent-kills-its-element-in-rank-models`. Verdict: PASS.

- `sigma : H -> M^x` extends to a unital algebra map `F[H] -> M`, so
  `sigma(c) sigma(e_g) sigma(b) = 1` and `1 = rk(1) <= rk(sigma(e_g))`.
- A Sylvester rank function satisfies `rk(e) + rk(1-e) = rk(1)` for idempotents, because
  `diag(e, 1-e)` is equivalent to `diag(1, 0)` by invertible matrices and the rank of a block
  diagonal is the sum. So `rk(1 - sigma(e_g)) = 0`.
- Faithfulness on idempotents holds in both examples: normalized rank on `M_n(k)` is faithful on
  every element, and so is the induced rank on a rank ultraproduct, since the rank-null ideal has
  been quotiented out.
- `g e_g = e_g`, so `sigma(g) = sigma(g) sigma(e_g) = sigma(e_g) = 1`.
- Matrix form: the normalized rank on `M_n(M)` gives `rk(sigma(e_g)) = 1` in the same way.

### 1.2 `thompson-v-linear-witness-supports-kill-g-in-rank-models`. Verdict: PASS, with one scope sharpening.

- Target forms checked against main: both targets are scalar equations `c e b = 1` in `F_p[V]`.
  For `w` of order 2 over `F_3`, `2^-1 = 2` gives `e_w = 2(1+w)`. For `h` of order 3 over `F_2`,
  `3^-1 = 1` gives `e_h = 1 + h + h^2`. In both cases `p` does not divide the order.
- `b, c, e_g` lie in `F_p[H]`, so the equation holds in `F_p[H]` and Lemma 1.1 applies to `H`.
- Rank targets that would keep `g` alive:
  - A finite quotient `Q` gives the regular representation over `F_p`, faithful on `Q`. So `g` is
    in every finite-index normal subgroup, i.e. in the finite residual.
  - A sofic (or LEF) approximation into `Sym(n_i)` gives permutation matrices. For a permutation
    `P`, `rk(P - 1) = n - #cycles >= (moved points)/2`, and `rk(P - Q) <= #{i : P e_i != Q e_i}`.
    So the ultraproduct over `F_p` is a homomorphism with `rk(sigma(g) - 1) >= 1/2` for `g != 1`.
    This is `monomial-rank-models-are-hamming-models` with trivial scalars.
  - A linear sofic approximation separates elements by a positive constant, so its ultraproduct is
    injective.
- The exclusions (finite, locally finite, residually finite, amenable, linear supports) are
  correct: `H` is finitely generated, so locally finite means finite; amenable implies sofic; and
  finitely generated linear groups over any field are residually finite (Malcev).
- `w` is the rotation by `1/2` and `h` sends `[0,1/4), [1/4,1/2), [1/2,1)` onto
  `[1/4,1/2), [1/2,1), [0,1/4)` affinely. Both preserve the cyclic order, so both lie in `T`.
- **Scope sharpening.** The sentence "T-internal witnesses pass the filter" overstates. The filter
  is a statement about `H = <g, supp b, supp c>`, and `H <= T` need not be `T`. A witness supported
  in `T` whose `H` is residually finite is excluded. What is true: `T` itself equals its finite
  residual and has no nontrivial finite-dimensional representations (Malcev plus simplicity), while
  its soficity and linear soficity are open. So witnesses with `H = T`, or with `H` any subgroup
  where `g` survives in no known rank model, are not excluded by anything known. Sent to the author
  to reword.

### 1.3 `thompson-v-direct-finiteness-failures-transfer-into-kernel`. Verdict: PASS.

- `p = 3`: `x = (00 01)`, `y = (10 11)` have disjoint supports and order 2, and
  `(2(1-x))^2 = 8(1-x) = 2(1-x)` over `F_3`. So `q = (1-x)(1-y) = (2(1-x))(2(1-y))` is idempotent,
  with four distinct group elements in its support.
- `p = 2`: `x, y` are 3-cycles on depth-3 prefixes in `[0]`, `[1]`, and `(x+x^2)^2 = x + x^2`.
- `pi(q) = 0`, checked directly in `L_(F_p)(1,2)` without the sequence module:
  - `p = 3`: `pi(1-x) = (S00 - S01)(T00 - T01)` and `pi(1-y) = (S10 - S11)(T10 - T11)`. The middle
    factor `(T00 - T01)(S10 - S11)` vanishes, since `T_a S_b = 0` for incomparable `a, b`.
  - `p = 2`: `pi(x + x^2) = sum_(j != i) S_i T_j` over the three moved prefixes in `[0]`, and
    likewise in `[1]`. Every cross product contains some `T_(0..) S_(1..) = 0`.
  - The artifact's module argument (a nonzero module over the simple algebra is faithful) is also
    correct.
- `delta(g)(u eta) = u g(eta)` for `|u| = k` is an injective homomorphism into `V`. `x, y` act
  only on the depth-`k` prefix, so they commute with every `delta(g)`. `delta(g)` fixes every
  depth-`k` prefix, and nontrivial elements of `<x, y>` move one, so `delta(V) ∩ <x, y> = 1`.
- `mu(a) = delta_*(a) q` is multiplicative because `q` commutes with `delta_*(S)`, unital onto `q`,
  and injective: `delta(g) xi = delta(g') xi'` forces `g = g'` and `xi = xi'`, so the coefficient
  of `delta(g) xi` in `mu(a)` is `a_g q_xi`.
- Padding: `(1-q) mu(a) = 0 = mu(a)(1-q)`, so `CA = (1-q) + mu(ca) = 1`, and `AC = 1` would give
  `mu(ac) = mu(1)` and `ac = 1`. `pi(A) = 1`, so `A, C` lie in `F_p 1 + K`.
- Matrix sizes: apply `mu` entrywise. Diagonal entries of `(1-q) I + mu(a)` lie in `1 + K`, and
  off-diagonal entries lie in `K`.

**Decision status.** Nothing decision-level. `thompson-v-ternary-swap-idempotent-is-full` and
`thompson-v-order-three-averaging-idempotent-is-full` stay OPEN.

## 2. Defect-coupled routed codes (w3-measurable, b4a8cb1de3, 1e4526eaff, 6c8ed0fc09)

Artifact: `research/artifacts/defect-coupled-routed-codes-2026-09-12.md`.

### 2.1 `single-maximal-stage-routed-codes-cannot-compress` (Theorem C). Verdict: PASS.

- `R_1(c, d) = (c, y)` with `y(g) = pi_c(g)(d(rho_c(g)))` is exactly the form of Theorem A
  (`measurable-certificate-routing-preserves-bernoulli-measure`). `tau` injective on a conull Borel
  `X_0` makes `R_1` injective there, so `(R_1)_* mu = mu`. If `|D| = 1`, `R_1` is the identity and the
  step is trivial.
- Lusin–Souslin makes `Y_0 = R_1(X_0)` Borel, and `mu(Y_0) = mu(R_1^-1 Y_0) >= mu(X_0) = 1`.
- If `S(y) = S(y')` with `y = R_1 x`, `y' = R_1 x'`, then `tau x = tau x'`, so `x = x'`. So `S` is
  injective on a set of full uniform measure, and descent is applied to the uniform measure only.
- Descent (`bernoulli-codes-descend-to-window-subgroup`) is stated for Borel `f : A^K -> E`, not only
  finite windows. The coset decomposition `S(x)(gk) = S_K(z)(k)`, `z(k) = x(gk)`, covers it.
- Finite `K`: every point of `A^K` has positive mass, so `S_K` is injective and `|A|^|K| <= |E|^|K|`.
- Infinite `K`: Proposition 1 of `measurable-alphabet-compression-2026-09-12.md`, whose proof uses only
  `H(beta) <= log |E|`, gives `h^Rok_K <= log |E|`. Maximality gives `|E| >= |A|`.
- Sofic implies Rokhlin-maximal at every alphabet, by the consequence of
  `sofic-radical-localizes-bernoulli-deficit-witnesses` (ESTABLISHED, independently verified).
- `R_2` enters only through `|B| = |E|`.
- Not consumed, not re-derived: the remark citing the two-root census for subgroups containing the
  nine-leaf configuration.
- Scope, correctly recorded in the artifact's Section 5: one combining stage between
  alphabet-preserving maps. Several combining stages are not covered.

### 2.2 `compression-codes-are-small-generating-partitions` (Proposition D). Verdict: PASS.

- The name map is equivariant: `tau(h.x)(g) = b` iff `g^-1 h.x` is in `beta_b` iff
  `tau(x)(h^-1 g) = b`.
- Converse: take a countable separating family `{B_n}` of Borel sets. "Generating modulo null sets"
  gives `A_n` in `sigma(g beta : g in G) = tau^-1(Borel)` with `B_n Δ A_n` inside a Borel null `N_n`.
  On `X_0 = complement of the union of the N_n`, two points with equal `tau`-values lie in the same
  `A_n`, hence in the same `B_n`, hence coincide.
- Forward direction: the proof of Proposition 1 does not use `|B| < |A|`.

### 2.3 `profinite-localization-is-vacuous-over-leavitt-units` (Proposition E). Verdict: PASS on the statement, with a scope correction on its consequence.

- The statement holds. `U` is infinite and simple (`binary-leavitt-unit-group-is-simple`, whose route
  goes through `binary-leavitt-elementary-group-is-simple` and the Lean root-detection file; relied on
  here, not re-derived). A finite-index subgroup contains its normal core, which has finite index and is
  normal, hence equals `U`. So the profinite topology of `U` is indiscrete and every proper subgroup is
  non-closed in it.
- **Scope correction.** The consequence sentences say the non-closed-stabilizer localization "has no
  analogue over U that could filter codes" and "carries no filtering content over U". That overstates.
  - In `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers` closedness is measured in the
    profinite topology of `pi(K)`, where `K` is generated by the witness. It is not measured in the
    ambient group.
  - The analogue over `U` concerns `K <= U`, and `K` can be residually finite, for example free or
    finite. There closedness is a real condition, and residually finite `K` is already excluded,
    by Theorem C for windows and by the localization theorem for configurations.
  - What Proposition E shows is only that closedness in `U`'s own profinite topology filters nothing.
  - The same applies to "invisibility is automatic (`Rad(U) = U`)". The localization theorem constrains
    `Rad(K)` of the generated subgroup, which is nontrivial only when `K` is nonsofic. Sent to the author.

**Decision status.** Nothing decision-level. `measurable-alphabet-compression-over-leavitt-units` stays
OPEN.

## 3. The Kun–Thom Clifford cover as a test host (w3-free-neg)

Artifact: `research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md`. Setting: the
Kun–Thom Theorem E pair `Gamma < G` (G residually finite), `X = G/Gamma` infinite,
`E_S = Vtilde_S semidirect G`, central involution `eps`, `W = E_S/<eps>`.

### 3.1 `kun-thom-clifford-cover-has-no-finitary-site-structure`. Verdict: PASS.

- (D) gives `N_empty = 1`, so (A2) with `U` empty gives `p_T(alpha_g n) = 1` whenever `g L(n)` misses `T`.
- `{g : g l = t}` is empty or a left coset of `Stab(l)`, which is conjugate to `Gamma` and has infinite
  index. B. H. Neumann: finitely many cosets of infinite-index subgroups do not cover `G`.
- For `g` outside them, `p_T(alpha_g c_o) = p_T(alpha_g c_y) = 1`. Any sign in
  `alpha_g(c_o) = +- c_(go)` is central and drops out of the commutator. `[alpha_g c_o, alpha_g c_y] =
  alpha_g(eps) = eps`, so `p_T(eps) = 1` for every finite `T`, and (A1) fails for `eps`.

### 3.2 `complete-graph-clifford-cover-center-dies-in-finite-quotients`. Verdict: PASS.

- For the complete graph `b_S(x, y) = 1` for all `x != y`. The form is alternating, since
  `b(u, u) = sum over x != y of u_x u_y` counts every pair twice.
- If `f(eps) = z != 1`, distinct lamps have images with commutator `z`, so the images are pairwise
  distinct, and `X` is infinite.

### 3.3 `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`. Verdict: PASS, with one wiring note.

- `eps` is central of order 2 and `2` is invertible mod 3, so `e_+- = (1 +- eps)/2` are orthogonal
  central idempotents summing to `1`. `e_+ F_3[E_S] = F_3[W]`.
- `E_S` is split over `G`, so `F_3[E_S] = F_3[Vtilde_S] * G`. `e_-` is central and `G`-fixed, so the
  `-` factor is `(e_- F_3[Vtilde_S]) * G`, the lamp algebra with `eps = -1` crossed by `G`. The `G`-action
  may carry signs, `alpha_g(c_x) = +- c_(gx)`. That does not change the skew-ring structure.
- A one-sided pair in a product ring projects to a one-sided pair in some factor, and a pair in one
  factor pads to the product. `F_3[W]` is directly finite at every size, so failure is decided on `A_S`.
- **Wiring note.** The route requires `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`,
  which says `k[W]` is stably finite iff `k[G]` is. The conclusion also needs `F_3[G]` stably finite for
  the residually finite base. That is supplied by `kun-thom-wreath-stably-finite` (`k[W]` stably finite
  for every field), which is on main but not named. Sent to the author.

### 3.4 The root, its linear route and the Attempts entries. Verdict: correct as scoped.

- `clifford-cover-nonsurjunctive-from-anti-half-df-failure` is valid: pad a pair in `A_S` with `e_+`,
  then apply `stable-finiteness-failure-refutes-surjunctivity` at `n = 1` over `F_3`. The route cannot
  fire while `clifford-cover-anti-half-skew-ring-not-directly-finite` is open.
- Payoff sentence: `W` is surjunctive (`kun-thom-nonsofic-wreaths-are-surjunctive`), so a strict
  automaton on `E_S` would also refute `finite-normal-subgroups-do-not-affect-surjunctivity`. Correct.
- Support filter (artifact Section 4.1): a witness supported in `Vtilde_S semidirect H` pads into
  `F_3[Vtilde_S semidirect H]`. Sofic groups have stably finite modular group algebras, so that group is
  nonsofic and `H` is nonamenable, since `Vtilde_S` is locally finite. Correct.
- Spinor obstruction (Section 4.2): `N = c_v c_w` has `N^2 = -1` when `q(v) = q(w)`. `U = 1 + N` has
  inverse `(1 - N)/2` and conjugates `c_v` to `+- c_w` while fixing the other lamps. `U - 1 = N` is
  invertible. This is heuristic evidence against one construction, recorded only in Attempts, and
  correctly not a claim.
- Binary case (landing b8b797c4a): in characteristic 2 the kernel of `F_2[E_S] -> F_2[W]` is
  `(1 + eps) F_2[E_S]`, and it squares to zero. If `b a = 1`, then `a b = 1 + j` with `j` nilpotent, so
  `a` is invertible. This holds at every matrix size, so `F_2[E_S]` is stably finite with `F_2[W]`.
  Correct.
- Local-embedding observation: correct as scoped. Exact finite models of the coset action on arbitrary
  windows cannot exist, and the entry says so.

**Decision status.** Nothing decision-level. `kun-thom-clifford-cover-nonsurjunctive` and
`clifford-cover-anti-half-skew-ring-not-directly-finite` stay OPEN.
