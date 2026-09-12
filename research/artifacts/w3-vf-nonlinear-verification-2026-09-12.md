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

### 5.4 `radu-bmw-coordinate-subgroups-are-sofic` and the linear target (65da28695b). Verdict: PASS.

- **Letter-closure, the pressure point.**
  - Rows with `v = y` are `(a,y) -> (y,a)`, `(b,y) -> (y,c)`, `(c,y) -> (y,b)`, so `v' = y`.
  - Rows with `v` in `{x,z}` have `v'` in `{x,z}`: `a` and `b` keep the letter, and `c` swaps `x <-> z`.
  - Inverting rows gives the same for pushing vertical letters leftward.
  - With unique normal forms, `A.{1,y}` and `A.D` are exactly the subgroups `P_y` and `P_xz`. Both are
    proper, since neither contains both `y` and `x`.
- **`P_y = A ⋊ <y>`.** `y a y = a`, `y b y = c`, `y c y = b`. `A = C_2 * C_2 * C_2` has index 2, so
  `P_y` is virtually free.
- **`P_xz`, the pressure point.**
  - `L = P_xz / A` is in bijection with the reduced `{x,z}`-words, and it is a bi-infinite path.
  - `a` and `b` fix every vertex, and `c` reflects the path by swapping letters. So `A` acts through the
    `c`-parity character, and any element fixing `A` as a vertex lies in `A`. The kernel is `A_ev`, of
    index 2 in `A`, virtually free and sofic.
  - The quotient embeds in `Aut(L) = D_infinity`, which is amenable. So `P_xz` is sofic by
    `sofic-kernel-amenable-quotient-permanence`.
- **Generation.** `cxc = z` gives `<A,x> = <A,z> = P_xz`, and adding `y` gives all letters. `zaz = b`,
  `zbz = a`, `yby = c`, `ycy = b` show one horizontal letter with `V` generates `Gamma_R`.
- **Screen.** If no memory element has `y` in its vertical part, the memory lies in `P_xz`. If none
  has `x` or `z`, it lies in `P_y`. Correct.
- **`radu-bmw-lattice-group-algebra-not-stably-finite` (open) and its route.**
  - The route `radu-bmw-stable-finiteness-failure-gives-nonsurjunctivity` is valid and cannot fire.
  - Support filter: a pair supported in a sofic `S` would make `S` nonsurjunctive, which is impossible.
  - For odd `p`, characters kill `(1+t)/2`. For `p = 2`, `(1+t)^2 = 0` supplies the torsion that
    Lemma D demands, and characters into `F_2^x` are trivial. All correct as scoped.

**Decision status.** Nothing decision-level. `radu-bmw-lattice-nonsurjunctive`,
`radu-bmw-lattice-group-algebra-not-stably-finite` and `strict-automaton-on-lattice-in-product-of-trees`
stay OPEN.

## 6. Unbalanced designs (w3-bal-design, f1c487b47)

Artifact: `research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md`, Section 1. The
conventions are those of `canonical-table-groups-for-automaton-designs-2026-09-12.md`:
- `E <= E'` means `E'` is coarser, and `𝓕_D` is an up-set;
- Lemma 1: `sigma_rho tau_rho = id` iff `E_rho` is in `𝓕_D`;
- Lemma 4: injective automata have automaton left inverses;
- Lemma 5: if `E_rho >= E`, then `x_a -> rho(a)` is a homomorphism `U_E -> G`.

No node of this lane cites the corrected `finite-left-inverse-identity-does-not-force-balance`.

### 6.1 `unbalanced-effective-rule-certifies-strictness` (Proposition 1, Corollary 2). Verdict: PASS.

- `E_rho >= E` in `𝓕_D` gives `E_rho` in `𝓕_D`, then `sigma_rho tau_rho = id`.
- `tau_rho(x)(g)` reads `x` at the distinct points `g rho(M)`, which carry independent uniform symbols. So
  its one-site law is `(mu_rho)_*` of the uniform law, and it is uniform iff `mu_rho` is balanced.
- If `tau_rho` were bijective it would preserve `lambda` (`bijective-ca-preserve-uniform-bernoulli-measure`,
  verified by gk-vf-positive, Section 1.3), and its marginal would be uniform. So an unbalanced `mu_rho`
  gives a strict `tau_rho`.
- Over `U_E`: `E_(rho_E) >= E` and `kappa_(rho_E) = kappa_E`. Pairwise distinct letters give `mu_E = mu`.
- **Sofic quotients.** For `q : U_E -> Q`, the realization `q o rho_E` only adds coincidences, so its forward
  table is `>= E`. A sofic `Q` is surjunctive, so the effective rule is balanced. Correct.
- **Robust unbalance over `F_2`.**
  - The parity of the weight of a Boolean function is its top ANF coefficient, by Möbius inversion.
  - Substituting `x_m -> y_(q(m))` gives `mu_kappa` the top coefficient `sum over q(T) = M/kappa of c_T`.
  - An odd weight on at least two variables is not `2^(k-1)`, so the rule is unbalanced.
  - For "affine part plus `x^M`" only `T = M` contributes.
  - With `Gamma_E` connected, `U_E = Hol_M(E)` (`table-groups-are-memory-holonomy-groups`, `c = 1`) is
    generated by the letters, so it has no nontrivial sofic quotient. Correct.

### 6.2 `unbalanced-forward-tables-identify-memory-letters` (open) and Theorem 3. Verdict: correct; both routes valid as an intended cycle.

- (1) ⇒ (2) is Corollary 2.
- (2) ⇒ (1):
  - `strict-automata-give-injective-ca-with-skewed-site-marginals` (ESTABLISHED, passed by w3-vf-positive)
    gives an injective `kappa` with a non-uniform one-site law. Its memory elements are distinct in `G`, so
    its rule is unbalanced, and adjoining an unread `1` leaves the law unchanged.
  - Lemmas 4 and 1 give a design with `E_rho` in `𝓕_D`, and finiteness gives a minimal `E <= E_rho`.
  - Lemma 5 gives `pi : U_E -> G` with `pi(x_m) = m`, so the letters are pairwise distinct. Contradiction.
- The group-by-group form is correct. The alphabet changes in the amplification, which is why it says
  "over every alphabet".
- `gottschalk-via-unbalanced-table-memory-collisions` and `unbalanced-table-memory-collisions-from-gottschalk`
  form an intended cycle. Neither can establish anything without the other.

## 7. Clifford covers: finite pullbacks and infranormal closures (w4-clifford-nonlinear, 368274a18)

Artifact: `research/artifacts/clifford-cover-orbital-localization-2026-09-12.md`, Sections 0–2.

### 7.1 `clifford-cover-center-separable-iff-graph-is-finite-pullback` (Theorem A). Verdict: PASS.

- **Setting.** `G` acts without signs, `g(c_x) = c_(gx)`, and `q` is constant. The normal-form bound
  `<= 2^(|T|+1)` on finite site sets gives `eps != 1`.
- **If.**
  - Map `c_x -> c_(Kx)`, `eps -> eps`, `g -> gK` into `Vtilde_Sbar(K\X) semidirect G/K`, which is finite.
  - Squares, commutators across fibres (by pullback), commutators within fibres (both sides trivial), and
    conjugation (by equivariance of `pi_K`) are preserved. `g eps g^-1 = eps` also holds in the image.
- **Only if.**
  - `x -> f(c_x)` is `G`-equivariant for conjugation, and `[f(c_x), f(c_y)] = f(eps)^(b_S(x,y))`.
  - The kernel `K` of `G -> Sym(Z)` is normal of finite index, and the site map is constant on `K`-orbits.
  - The non-commuting graph pulls back to `S`. Equal images commute, so fibres carry no edge.
- **Corollary A.1.** `<eps>` injects into a finite quotient, and `W = F_2 wr_X G` is surjunctive over a
  surjunctive `G`. The separated finite-normal theorem (verified, gk-vf-positive Section 6.3) applies. Correct.
- **Corollary A.2.**
  - Factoring through `G/L` with `L = K Gamma`, and conversely with `K` the core of `L`, is equivalent to `D(S)`
    being `L`-bi-invariant and missing `L`.
  - Finite degree: `[L : Gamma]` is infinite, so `L g L ⊆ D(S)` gives `o` infinitely many neighbours.
  - Complete graph: `L != Gamma` meets `G minus Gamma`. Correct.

### 7.2 `infranormal-subgroups-have-normal-profinite-closure` (Lemma 2.2). Verdict: PASS.

- `f(t Gamma t^-1) = f(t) f(Gamma) f(t)^-1` lies in `f(Gamma)` and has the same order, so they are equal.
  Taking preimages gives `K t Gamma t^-1 = K Gamma`, and `t K t^-1 = K`, so `t` normalizes `K Gamma`.
- The normalizer is a subgroup containing the generating set `P_Gamma`, so it is `G`. An intersection of
  normal subgroups is normal.
- **Lemma 2.1:** `K a Gamma = a K Gamma` because `K` is normal.
- **Remark 2.3:**
  - `t^-1 Gamma t <= t^-1 Gammabar t = Gammabar`, so the phase edge joins inseparable sites.
  - A non-normal infranormal `Gamma` is not closed.
  - For the Theorem E pair, `N` is normal with residually finite quotient, hence closed. So `Gammabar <= N`,
    and `G/Gammabar` is infinite. Correct.

**Decision status.** Nothing decision-level. `kun-thom-clifford-cover-nonsurjunctive` stays OPEN.

## 8. Screens a biased binary rule must pass (w3-bal-design, 5a73418397)

Artifact Section 2. Claims `monotone-binary-injective-rules-are-copies` and
`three-address-binary-injective-rules-are-balanced`. Verdict: PASS on both.

- **Lemma 4.** Perturb the constant `c` at site `1`. The output at `h` reads site `1` only when `h = m^-1`,
  at the single address `m`, with `c` everywhere else. So if every such output is unchanged, `tau` collides.
- **Lemma 5.**
  - Background `0` gives `mu(0) = 0` and `mu(e_t) = 1`, so `mu >= x_t` by monotonicity. Background `1`
    gives `mu <= x_t'`.
  - Evaluating at `e_t` gives `t' = t`. Nonincreasing rules are the complement.
- **Lemma 6.** A never-blind coordinate makes `mu = x_m + g(rest)`, which is balanced. If the sets `D_m` are
  pairwise disjoint, the contexts `r_m` sit on distinct sites other than `1`, and the flip at `1` is
  invisible. This is the same statement as w4-bal-census's Sidon theorem (Section 9.1).
- **Corollary 7.**
  - The cross-coincidences among `D_1 = {a,b}`, `D_a = {a^-1, a^-1 b}`, `D_b = {b^-1, b^-1 a}` are exactly
    `a^2 = 1`, `b^2 = 1`, `(a^-1 b)^2 = 1`, `ab = 1`, `b = a^2` and `a = b^2`. I checked all twelve pairs.
  - The last three make `<a,b>` cyclic, and two of the first three make it dihedral. So exactly one
    involution relation holds.
  - With `a^2 = 1` the only shared variable is the site `a`, read as address `a` by block `1` and as
    address `1` by block `a`. So satisfiability means the projections meet, and injectivity forces
    complementary singletons.
- **Theorem 8.**
  - Re-rooting and relabelling reduce to `a^2 = 1`, and input complementation normalizes the projections.
    The normal form `mu(x_1,0,x_b) = x_1 + f(x_b)` and `mu(1,1,x_b) = f(x_b)` follows.
  - I rechecked all 28 coincidences among `1, a, b, ab, b^-1, b^-1 a, ab^-1, ab^-1 a`. Each gives `a = 1`,
    `b = 1`, `a = b`, a cyclic relation, `b^2 = 1`, `(ba)^2 = 1` or `ab = ba`, and each makes `<a,b>` amenable.
  - **Double flip.** Blocks `1` and `a` both see `(0,0) -> (1,1)` in their first two coordinates, so both
    output `f`. Blocks `b^-1` and `a b^-1` read a flipped site only at address `b`, with private contexts
    chosen in `Ins_b`.
- **Example.** `mu = x_1 + x_1 x_a x_b` has `Ins_1 = {(1,1)}`, while `pi_(x_1)(Ins_a) = {0,1}`. So the first
  row already fails. Correct.

## 9. Small-memory balance census (w4-bal-census)

Artifact: `research/artifacts/small-memory-balance-census-2026-09-12.md`.

### 9.1 `binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`. Verdict: PASS.

- Lemma 3.1 is as in Section 8.
- **Sidon condition.** Sidon means the sets `{m^-1 m'}` are pairwise disjoint and have distinct elements,
  so the sites `h m^-1 m'` are distinct and not `h`. The flipped site is read only by the sites `h m^-1`,
  each at one coordinate in context `r_m`.
- **Duplicate content.** This is w3-bal-design's Lemma 6 under another name. The authors should link the two
  with `distinct_from` or cite one from the other.
- **Remark 3.4, corrected example.** `R = x - y + z` over `F_3`, patched at `(0,2,2)` from `0` to `1`.
  - Constants map to themselves.
  - The blind pairs are `{0,1}` for `x` at `(2,2)`, `{1,2}` for `y` at `(0,2)`, and `{0,2}` for `z` at `(0,2)`.
  - The symbols have 8, 10 and 9 preimages. Correct.

### 9.2 `binary-three-address-injective-automata-have-balanced-rules` (Theorem 4.1). Verdict: PASS. It duplicates a claim.

- **Step 1.**
  - Constants force `mu(000) != mu(111)`.
  - Flipping the constant `1` is invisible unless `T` contains a weight-two vector. Flipping `0` is
    visible for `w <= 3`.
  - Up to address permutation, which is (R2) followed by relabelling, the survivors are `{000,110}`,
    `{000,100,110}`, `{000,110,001}` and `{000,110,101}`.
- **Blind sets.** I recomputed all four tables.
- **Case (2).** The only conflict is `hb^-1`, `hb^-1 a` both in `{hb, h a^-1 b}`, which means `a = b^2`, or
  `b^2 = 1` together with `(b^-1 a)^2 = 1`.
- **Case (3a).** Choice A conflicts only if `a^2 = 1`, and choice B only if `b^2 = 1`.
- **Case (3b).** Both context sites are forced to `1` only under `ab = 1`, `a = b^2`, `b = a^2`, or `b^2 = 1`
  with `(b^-1 a)^2 = 1`.
- **Case (3c), the pressure point.**
  - The single flip conflicts iff `a^2 = 1`, `b^2 = 1`, `ab = 1`, `b = a^2` or `a = b^2`.
  - For the double flip of `h, ha` with `a^2 = 1`, the reading sites are `h, ha, hb^-1, h a b^-1`.
    `mu(u,v,0) = [u = v]`.
  - The 0-sites are `hb, hab, hb^-1, h a b^-1` and the 1-sites are `h b^-1 a, h a b^-1 a`. Every
    coincidence gives `b^2 = a`, `aba = b^-1` or `ab = ba`. With `a^2 = 1`, `aba = b^-1` gives `(ab)^2 = 1`,
    which is dihedral.
  - None of the sites is `h` or `ha`. Correct.
- **Duplicate, now resolved.** The statement equals `three-address-binary-injective-rules-are-balanced`
  (w3-bal-design). The census lane deleted its own claim at 1346a8425d. Its route
  `binary-three-address-balance-census-proof` now targets w3-bal-design's claim, as a second, independent
  proof.

### 9.3 `avoidable-patches-of-affine-rules-inherit-linear-injectivity` (Proposition 5.2). Verdict: PASS.

- Take `d != 0` in the kernel of `tau_(lambda_0)`. For `q >= 3` choose `x(g)` outside `{s, s - d(g)}`. Then
  `x` and `x + d` avoid `s`, so `tau_mu = tau_lambda` on both, and `tau_lambda(x + d) = tau_lambda(x)`.
- A bijective linear automaton has a linear automaton inverse, and `tau_C tau_A = tau_(CA)` gives the unit
  dichotomy.
- **Unit example.** Over `Z x Z/3`, `(a(1 - c))^3 = a^3 (1 - c^3) = 0` in characteristic 3. Correct.
- Proposition 5.1 (common blind pair, `q >= 3`, Sidon) is Theorem 3.2 with `c -> d`. Correct.

## 10. Equal-alphabet sofic codes and non-enlarging cascades (w4-measurable-2, ee172a42df, 6cbc61470f)

Artifact: `research/artifacts/non-expanding-sofic-cascades-2026-09-12.md`.

### 10.1 `injective-same-alphabet-sofic-codes-preserve-uniform-measure` (Lemma 1). Verdict: PASS on all pressure points.

- **Step 1.** Lusin–Souslin gives a Borel decoder. Cylinder density applies for the pushforward measure.
  The union bound gives `< eps + |D| eps/(|D|+1) < 2 eps`, and invariance gives (1.2).
- **Step 2.** The uniform law is the unique entropy maximizer, and adding `1` to `F` does not decrease `c`.
  (2.1) is subadditivity of conditional entropy plus Fano, with `h_2` increasing on `[0, 1/2]`.
- **Laws at good points, (3.1) and (3.2).**
  - `y(v.d) = s_eps((x(v.(dw)))_w)` needs `d, w, dw` in `Q`.
  - The chart `q -> v.q` is a function on `Q` that is injective, so coincidences among `{1} ∪ DW`, and among
    `FW`, match those in `K`. With iid uniform `x` the joint laws agree.
- **Lower bound.** `H(x) <= H(y) + sum_v H(x(v) | y)`, with Fano at good points.
- **Shearer.**
  - `v -> v.f` is a permutation, so a bad point spoils at most `|F|` points, and `|V minus V'| <= |F| eta |V|`.
  - For `u` in `V'` the preimages `v_f` are distinct, because a good chart is injective on `F`. So the
    multiplicity is `|F|`.
  - The bookkeeping `sum over v of H(y|S_v) <= |V||F| log q - (1 - eta)|V| c + |V||F| delta'` is correct.
- **Final inequality.** `(1 - eta) c/|F| <= delta + delta' + (|F| + 1) eta log q`. `Q` is fixed for each
  `eps`, so `eta -> 0` first and then `eps -> 0` is legitimate.
- **Coset lifting.** `S(y)(gk) = S_K(z_g)(k)` with `z_g(k) = y(gk)`. Inputs on distinct cosets are
  independent. Correct.

### 10.2 `non-enlarging-sofic-window-cascades-cannot-compress` (Theorem G, Proposition H). Verdict: PASS.

- Step 0 is as in Theorem C (Section 2.1).
- **Step 1.** (R) uses Theorem A, and (P) holds by definition. (W) descends, then Part 1 applies, and at equal
  alphabets Part 2 plus coset lifting applies. Induction gives items 1–3.
- **Item 4.**
  - Intersect translates to make the injectivity set invariant.
  - A uniform output would make the Borel inverse on the image an a.e.-injective equivariant code into a
    smaller alphabet over the sofic window. Extend it equivariantly off the image, for example by a constant.
  - That contradicts Part 1.
- **Item 5** is as in Theorem C.
- **Proposition H.** `T_i(x)(g) = (x(g u_i ... u_1))` with `u_l` in `{1, w_l}`, and each `w_l` occurs. The last
  stage combines the square with `f`, so `m - 1` stages enlarge. Cyclic windows are sofic.
- **Continuous-decoder remark.** Full support plus continuity turns `sigma tau = id` a.e. into an identity
  everywhere. Composing with `B -> A` gives a strict automaton, by Curtis–Hedlund–Lyndon. Correct.

## 11. Invisible adjacency and saturated covers (w4-clifford-nonlinear, e4a8abdf92, 0ccfbb0f1e, 69189171a9, a7e5d049ae)

Artifact Sections 3–4. Transfer input: `strict-pairs-transfer-to-table-realizations`. It needs
`phi(sm) = phi(s) phi(m)`, `phi(wm) = phi(w) phi(m)`, and `phi(w) != phi(w')` whenever `p(w) != p(w')`, and
nothing more.

### 11.1 Coordinates

- **Group law.** Merging normal words gives `beta(u, gv)`, which counts cross pairs and `q` on overlaps.
  Reordering `c_(g y_1) ... c_(g y_l)` costs `gamma(v, g)`. So products read `b_S` only on `R(a,m)`.
- **Consequence 0.1.** Consequence 0.1 is correct. Including pairs inside `supp u_a` in `R` is harmless.

### 11.2 `clifford-cover-strict-pairs-read-invisible-adjacency` (Theorems B, B', B''). Verdict: PASS.

- **Cleanliness passes to smaller `K`.**
  - `K x != K y` implies `K' x != K' y`.
  - An orbit coincidence at `K'` maps to one at `K`, and the image pair stays proper because `g` permutes
    `K\X`.
- **Theorem B.**
  - `K` is the intersection of the `K_E`, and every read edge is `K`-clean.
  - `Sbar` is `G`-invariant, and its pullback `S'` is a finite pullback.
  - Read edges lie in `S'`, and a read non-edge is either inside a fibre or excluded by cleanliness. So
    `b_(S') = b_S` on `R`.
  - Corollary A.1 and Consequence 0.1 then let the transfer produce a strict pair on a surjunctive group.
- **Coset form.** `K Gamma g K Gamma = K Gamma g Gamma` for normal `K`. Each failing condition is downward
  closed in `K`, and there are finitely many, so one holds for all `K`.
- **Theorem B'.**
  - Two paths to one site differ by `Hol_i`, so the map is well defined.
  - Injectivity is the negated conclusion. Moves are equivariant, and the finite order extends.
  - In the complete graph `beta` and `gamma` see only order and equality.
  - `X'` has finitely many orbits and closed point stabilizers, so Theorem C applies, with `G` surjunctive.
- **Theorem B'', the pressure point.**
  - `lambda(w x_0) = psi(w) psi(Hol_i^U)` is well defined, since closed paths lie in `Hol_i^U`. It is injective
    because `w^-1 w'` lies outside `K_U Hol_i^U`, by the failure of (2) at finitely many pairs.
  - `phi(u, s, g_a) = (lambda u, s, psi[g_a])` is exact on the needed products, since the `U`-relators hold
    and the signs are order data.
  - Transfer only needs Omega pairs with different pattern values kept apart. Different lamp or sign
    coordinates stay apart through `lambda`. Equal ones stay apart through the failure of (1).
  - The target `Vtilde(X'') semidirect U/K_U` is finite, so no surjunctivity of `G` is used.
  - For residually finite `G`, (1) cannot hold, since `U -> G` separates. Correct.

### 11.3 `profinitely-saturated-clifford-covers-are-surjunctive` (Theorem C) and Remark 4.1. Verdict: PASS.

- **One `K`.** Saturation conditions 1 and 2 give, for each edge of `R_F`, a `K` separating its endpoints
  and splitting its orbit from each non-edge. Both properties pass to smaller `K`, so one `K` serves all of
  them.
- **Conclusion.** `S'` agrees with `S` on `R_F`, and Consequence 0.1 embeds the table of `F`. Corollary 1 of
  the transfer theorem (local embeddings) finishes.
- **Instance 3, `S_cross`.**
  - `D = G minus Gammabar` is `Gamma`-bi-invariant and symmetric, with no loops.
  - Condition 1 is Lemma 2.1. Condition 2 holds because a non-edge `g'` in `Gammabar` collapses to one point
    in every `K\X`.
  - Finite pullback iff `[G : Gammabar]` is finite. Finitely many subgroups lie above a finite-index `Gammabar`,
    so the directed family `K Gamma` attains `Gammabar`.
- **Instance 4.** `G/Gammabar` is infinite, and `G` is residually finite, hence surjunctive. Correct.
- **Remark 4.1.**
  - Some `t` in `P_Gamma` has `t Gamma t^-1 != Gamma`, so the chain `Gamma < t^-1 Gamma t < ...` is strictly
    increasing inside the normal `Gammabar`, and the index is infinite.
  - If `g` is not in `Gammabar`, `cl(Gamma g Gamma) ⊇ Gammabar g Gammabar = g Gammabar`, by continuity of
    multiplication and normality.
  - A non-edge in that closure lies in `K Gamma g Gamma` for every `K`, so its orbit is never split and
    saturation fails. Saturation would therefore force the infinitely many sites `g gammabar o` to be
    neighbours of `o`.

**Decision status.** Nothing decision-level. The Clifford root and `finite-normal-subgroups-do-not-affect-surjunctivity`
stay OPEN. Theorem C settles one instance of the latter's residue in the predicted direction.

## 12. Stable realization of Z_3-equivariant permutations (w4-z3-rotation, 14718661ef)

Claim `z3-equivariant-permutations-are-stably-realizable`. Artifact:
`research/artifacts/z3-rotation-stable-realization-2026-09-12.md`. Verdict: PASS.

- **Coordinates.**
  - `v = x + s(1,1,1)` has coordinate sum `4s = 0`, and 3 is odd, so `(s_1, v_1, s_2, v_2)` are linear coordinates.
  - `1 + R + R^2` kills `V`, so `F_2[R]` acts on `V` as `F_4`.
  - Boolean points number 64: four fixed, and 20 free orbits indexed by `F_2^2 x P^1(F_4)`.
- **(M1).** `e_12(s_1 c)` is triangular, because `s_1` is untouched, and it is its own inverse and equivariant.
  `SL_2(F_4) = E_2(F_4)`, so `Y_A` realizes `A` at level 1 only.
- **(M2), the pressure point.** On Boolean points, `p + p o R + p o R^2` restricts to `f + f o R + f o R^2 = 3f = f`
  for invariant `f`, and the averaged polynomial is invariant. `X_f` is an equivariant involution.
- **Lemma 1, the pressure point.** `A` preserves `l minus 0` and its complement, so `f_l(A^(±1) u) = f_l(u)`.
  - For `u` not on `l`, `Y_A Y_A^-1 = id` at a fixed level.
  - At level 1, `u -> omega^-1 u = omega^2 u`, then `X`, nothing, `X`.
  - At level 0, `X`, then `Y_A` gives `omega u`, then `X`.
  - `diag(omega, omega^2)` has determinant 1 and fixes `[1:0]` with eigenvalue `omega`, and transitivity
    gives every `l`.
- **Theorem 2, the pressure point.**
  - The `C_l` act on disjoint sets and commute. `Q = R o (prod C_l)^-1` acts by `omega · omega = omega^2`
    at level 1 and `omega · omega^2 = 1` at level 0.
  - `B = diag(omega^2, omega)` has determinant 1, and `B omega^2 = diag(omega, 1)`.
  - `u(Rx) = omega u(x)`. The weight-one orbit is `s_1 = 1, u_1 != 0`, and `111` has `u = 0`. So the shadow
    is `rho x id`.
- **Corollary 3.** `G_tri x id` realizes `K x id`. `[E : K] = 3`, and 24 does not divide 36, so
  `<K, rho> = E`.
- **Stable formalizability.** It follows from the verified stable form of
  `finite-group-formalizability-equals-equivariant-automorphism`.
- **Scope.** The `delta(T)` remark is correct, since `delta deltabar = 1` in `F_4[s]` forces a constant. It is
  not load-bearing. `z3-weight-one-rotation-is-not-an-automorphism-shadow` stays OPEN.

## 13. Ornstein–Weiss decoders have no measurable sections (w4-measurable-2, 2734d41a42)

Claim `ornstein-weiss-type-decoders-admit-no-measurable-section`. Artifact:
`research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md`. Verdict: PASS.

- **Lemma K0, finite order.** `(S^k x)(h) = x(a^k h)`. Every `S^k` preserves `mu_A`, so the identity holds at
  all `S^k x` at once. Telescoping gives `sum_(k<N) lambda(x(a^k)) = 0` a.e., but that sum is uniform on `Z/n`.
- **Lemma K0, infinite order.**
  - `p(Sx) = p(x) - f(x)` makes `F = omega^(eps + p)` invariant under `S_f`, and `F(x, eps+1) = omega F`.
  - The right cosets `<a>h` are `S`-invariant. `f` reads only coordinate `1`, so `S_f = (S_1)_f x S_rest`.
  - **Partial sums.** Equal fibres of `lambda` give `w_k <-> (lambda(w_k), r_k)`. `(w, eps) -> (s, r)` is a
    bijection carrying the measure to uniform, because `s_0` and the iid increments form a linear bijective
    image of a uniform product. It conjugates to the shift, since `s'_k = s_(k+1)`.
  - A product of mixing systems is mixing, so `S_f` is ergodic, a contradiction.
- **Theorem K.** `tau(x)(a) = tau(a^-1.x)(1)` gives `p(x) - p(a^-1.x) = lambda(x(1))`.
- **Corollary.** Ornstein–Weiss is the case `A = (Z/2)^2`, `B = Z/2`, `lambda` the first coordinate, `beta = id`.
  Only the row along `a` is used, so any second element may be used in place of `b`.
- **Kernel stages (Section 3).** If `L(y + m) = L(y)` and translation by `m` preserves `mu`, then
  `X_0 ∩ (X_0 - m)` is conull. So `L` is not a.e.-injective. The indicator of a left coset of `F_2` lies in
  the kernel of the ascended `phi`. Correct.

## 14. Formalizability on finitely generated simple hosts (w3-stable-simple, Sections 3–5)

w3-vf-positive passed this region (its artifact, Sections 13–13.5). This independent pass agrees on
everything except one route.

- **Theorem 5.**
  - `L_u L_v = L_(uv)` holds as polynomial substitutions, and `L_B(x ± L_A w) = L_B x` holds formally when
    `BA = 0`.
  - Odd characteristic: `(1 - s)^p = 1 - s^p = 0`.
- **Corollary 6.**
  - `S(hs) = S(h)`, so `L_N(Gamma(S))(h) = S(h)(S(hm) + S(hsm))`.
  - The six cells `h, hs, hm, hms, hsm, hsms` are pairwise distinct iff `sm != ms`, and I checked all 15 pairs.
  - A multilinear quadratic in distinct variables is not affine.
  - D-infinity case: `S(g^k s g) = S(k-1)`, giving `c(k) = S(k)(S(k-1) + S(k+1))` on both tracks.
- **Dihedral pair in `V`.** `sgs(0w) = 0 a^-1(w) = g^-1(0w)`, symmetrically on `1w`, and `s` is not in `<g>`.
- **Routes.**
  - `simple-host-formalization-reduces-surjunctivity-to-kaplansky` is valid and cannot fire.
  - `dihedral-marker-formalization-induces-to-thompson-v` is valid: a single representative over `D` is a
    single representative over `V`.
- **Finding, route invalid as stated:** `simple-host-formalizability-specializes-to-the-v-marker`.
  - The prerequisite `binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable` gives representatives
    `tau~` and `sigma~` of the pair `(tau_g, tau_g)`, which may be different polynomials, with
    `sigma~ o tau~ = id`.
  - The target `thompson-v-marker-involution-is-formalizable` asks for one representative with
    `tau~ o tau~ = id`.
  - Nothing converts one into the other without direct finiteness of `F_2[V]`, which is open.
  - So the route, and the sentence "a refutation of the V object refutes the target", overreach.
  - **Fix.** State the V-marker target, and if wanted the dihedral one, in pair form: some representatives
    `tau~`, `sigma~` of `tau_g` satisfy `sigma~ o tau~ = id` formally. The dihedral route stays valid, since
    single representatives give a pair.
  - Sent to w3-stable-simple and w3-vf-positive.

**Decision status.** Nothing decision-level.
