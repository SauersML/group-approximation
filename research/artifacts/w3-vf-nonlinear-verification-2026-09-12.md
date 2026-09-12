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

**Follow-ups landed by authors.**
- w3-v-linear (0daab32073): the `T` remark was reworded as recommended.
- w3-free-neg (a1fc94a048): the splitting route now requires `kun-thom-wreath-stably-finite`.
- w3-measurable (10ee1dfb45): the Proposition E consequence was reworded as recommended.

## 4. Z_3 normal rotation and the eigen-hyperplane stabilizer (w3-nonformal, b9667076bd)

Artifact: `research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md`.
Setting: `(Rx)_i = x_(i-1)` on `A^3` over `F_2`, `s = x_0 + x_1 + x_2`, `u = x_0 + w x_1 + w^2 x_2`
over `F_4 = F_2(w)`, and `ubar` its conjugate.

### 4.1 `z3-equivariant-automorphisms-have-constant-normal-rotation`. Verdict: PASS.

- `u o R = x_2 + w x_0 + w^2 x_1 = w u`. `T o R = R o T` gives `R^* T^* = T^* R^*`, so `T_u` has weight 1:
  every monomial `s^k u^a ubar^b` in it has `a - b = 1 mod 3`.
- `Fix(R)` is the diagonal `{u = ubar = 0}`. Adding the two equations over `F_4` gives `x_1 = x_2`,
  then `x_0 = x_1`. `T` and `T^-1` preserve it, so `T` acts there by an automorphism of `A^1` over `F_2`,
  which is `s -> s + b`.
- Degree-one terms of `T_u` in `(u, ubar)`: `s^k u` has weight 1 and is allowed, `s^k ubar` has weight 2
  and is excluded, and there is no weight-0 term. So along the line
  `J = diag(d_s T_s, lambda(s), lambdabar(s))`, since `T_s` has weight 0 and no degree-one terms.
- `det J` is a unit of `F_2[x]`, hence `1`. So `lambda lambdabar = 1` in `F_4[s]`, and `lambda` is a
  constant in `F_4^x`. The chain rule at points of the line gives multiplicativity.

### 4.2 `z3-eigen-hyperplane-stabilizer-is-the-triangular-group`. Verdict: PASS.

- `N = u ubar = sum x_i^2 + sum_(i<j) x_i x_j`, using `w + w^2 = 1` and `w^3 = 1`, is defined over `F_2`,
  and `C = H ∪ Hbar`.
- **(i) ⇒ (ii), the pressure point.**
  - `T(H)` is closed, irreducible and two-dimensional inside `H ∪ Hbar`, so it equals `H` or `Hbar`.
  - If `T(H) = Hbar`, then `T_ubar` vanishes on `H`, so `u | T_ubar`. `T` is defined over `F_2`, and
    Frobenius on coefficients sends `T_ubar` to `T_u` and `u` to `ubar`, so `ubar | T_u`.
  - Then `d T_u / du = ubar d_u beta` vanishes on the diagonal, contradicting `lambda(T) != 0`. Correct.
- (ii) ⇒ (iii): `u` is prime, so `u | T_u` and `u | (T^-1)_u`. `u = (u beta')(T) = u beta (beta' o T)`,
  so `beta` is a unit, hence the constant `lambda(T)`.
- (iii) ⇒ (iv): `T_ubar = lambdabar ubar` by conjugation. `(s, lambda^-1 v) o T` fixes `F_2[V]`, and an
  `F_2[V]`-automorphism of `F_2[V][s]` is `s -> s + c(v)`, since `F_2[V]^x = {1}`. Equivariance makes `c`
  invariant. (iv) ⇒ (i): `N o T = lambda lambdabar N = N`.

### 4.3 Shadow group and Section 3. Verdict: correct.

- **Index 3, the pressure point.**
  - `E = C_2 x (C_3 wr C_2)` has order 36: a swap of `000, 111`, then a swap of the free orbits `O_1, O_2`,
    and rotations `(r_1, r_2)`.
  - The triangular shadows are `(s + f(v), R^k v)`. `f` takes one value at `v = 0` and one on `v != 0`, and
    `k` is uniform. So `K = C_2 x (Delta x <sigma>) = C_2 x C_6` has order 12.
  - `K` is not normal: `(a, b) sigma (a, b)^-1 = (a - b, b - a) sigma` lies outside `K` when `a != b`.
  - Index 3 is prime, so a subgroup containing `K` is `K` or `E`. The weight-one rotation has
    `(r_1, r_2) = (1, 0)`, which is outside `K`.
- **Shape on `H`:** the monomials `s^k ubar^b` with `-b = 1 mod 3` give `T_u|_H = ubar^2 g(s, ubar^3)`.
- **Line crossing.** `gamma(t) = (t, t+1, t+1)` has `(s, u, ubar) = (t, 1, 1)`. `u` is unchanged by
  complementation, so after normalizing `p(0) = w^(r_2)` and `p(1) = w^(r_1)`. A nonconstant `p` is
  nonzero at `0, 1`, so its roots lie outside `F_2`. The monodromy description is consistent with this.
- **Section 4 and the Attempts entries.**
  - The two-track shear `(s, v_1 + s v_2, v_2)` is an equivariant automorphism whose normal block
    derivative has determinant 1.
  - The corrected scope on `non-surjunctive-group-with-stably-finite-group-algebras` is right:
    `tau x id` is strict iff `tau` is, and stable finiteness of `F_2[G]` passes to finite-index subgroups,
    so both stable and virtual formalizations would force Kaplansky failure.

**Decision status.** Nothing decision-level. `z3-weight-one-rotation-is-not-an-automorphism-shadow` stays
OPEN.

## 5. Radu's BMW lattice as a host (w3-lattice, fe61f2234)

Artifact: `research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md`.
`Gamma_R = <a,b,c,x,y,z | a^2,...,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>` acts simply transitively
on the vertices of `T_3 x T_3`. This action, irreducibility, non-residual-finiteness and `(xz)^4` in
the finite residual are imported through `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, which was
read from the PDF. They are not re-derived here.

### 5.1 `strict-composites-have-strict-factors`. Verdict: PASS.

- If `tau = tau_1 ... tau_k` is injective, so is `tau_k`, and so is every tail.
- If `tau_k` is bijective and `tau_1 ... tau_(k-1)` identified `tau_k w` and `tau_k w'`, then
  `tau w = tau w'`. So the shorter composite is injective with the same image, and induction gives a
  strict factor.
- Memory inside a surjunctive `S`: `tau_j` acts coset by coset on `prod_(gS) A^(gS)` as one automaton
  over `S`. A product map is injective iff each component is, so `tau_j` is surjunctive.
- Scope: one fixed alphabet, as the claim states. `distinct_from` names
  `linear-reversible-words-strict-via-strict-linear-factor`.

### 5.2 `radu-bmw-lattice-has-no-invariant-output-injective-automata`. Verdict: PASS.

- **Any group.** `N` is normal of finite index. `Fix_N`, the configurations invariant under left
  translation by `N`, which are constant on the cosets `gN = Ng`, is `tau`-invariant because `tau`
  commutes with translations. It has `|A|^[G:N]` points. Its outputs are constant on `gN` and on `gH`,
  hence on `gHN`. Injectivity gives `[G:N] <= [G:HN]`, so `H <= N`.
- **Involutions.**
  - A finite-order element fixes a point of the CAT(0) space, so it preserves the open cell containing
    it. It fixes no vertex, and the action preserves the two tree factors.
  - So it inverts an edge, and is conjugate to a letter, or it is a half-turn of a square.
  - The half-turn at `o` is the unique element `hv` carrying `o` to the opposite corner. It is an
    involution iff `hv = vh`, which holds in rows `(a,x)`, `(a,y)`, `(b,x)`.
  - Elements of odd order would fix a vertex, so a nontrivial finite `H` contains an involution.
- **Abelianization.** `azbz`, `bycy`, `cxcz` give `a + b`, `b + c`, `x + z`, so
  `Gamma_R^ab = (Z/2)^3` on `a, x, y`. The images of `a, b, c, x, y, z, ax, ay, bx` are `a, a, a, x, y,
  x, a+x, a+y, a+x`, all nonzero. So no involution lies in `[Gamma_R, Gamma_R]`, which has index 8, and
  `H = 1`. `invariant-output-injective-ca-need-torsion` supplies finiteness of `H`.
- **Linear shadow.** For odd `p` some character `chi : Gamma_R -> {+-1}` has `chi(t) = -1`. It kills
  `(1+t)/2`, so that idempotent is full at no matrix size. Correct.

### 5.3 Remaining screens, routes and root. Verdict: correct as scoped.

- **Corollary 4.** `<h, v>` is dihedral, hence amenable. `A` and `V` are `C_2 * C_2 * C_2`, whose kernel
  onto `(Z/2)^3` is free by Kurosh, so they are virtually free and sofic.
  - The corner memory `{1, h, v', hv}` of a row `(h,v) -> (v',h')` lies in the dihedral `<h, v'>`. In every
    row of the table either `v = v'` or `h = h'`, and `hv = v'h'`.
  - So square-reading layers, horizontal or vertical layers, and their alternations are never strict.
- **Lemma 5.** Inverting `s m = s' m'` with `s, m, s', m'` involutions gives `m s = m' s'`. So every letter
  identification keeps its transpose. Correct, and consistent with
  `transposed-hinges-are-conjugated-commutators`.
- **Routes.**
  - `radu-bmw-nonsurjunctivity-gives-lattice-target`: a simply transitive vertex action is faithful,
    discrete and cocompact.
  - `radu-bmw-nonsurjunctivity-gives-nonsoficity`: via `sofic-groups-are-surjunctive`.
  - Both are valid and cannot fire while `radu-bmw-lattice-nonsurjunctive` is open.
- **Root consequences.** A strict `Gamma_R` gives nonsurjunctive `pi_1(S_R)` by finite-index overgroup
  closure, then nonsurjunctive `K` by subgroup heredity. That is a Gottschalk counterexample and a
  refutation of `fg-simple-kazhdan-groups-are-surjunctive`. The equivalence with `pi_1(S_R)` is correct.

**Decision status.** Nothing decision-level. `radu-bmw-lattice-nonsurjunctive` and
`strict-automaton-on-lattice-in-product-of-trees` stay OPEN.
