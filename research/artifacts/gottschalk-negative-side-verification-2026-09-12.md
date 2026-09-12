# Independent verification of the negative-side Gottschalk nodes

Date: 2026-09-12. Lane `gk-verify-neg`. Each item was re-derived from its
statement rather than by rereading the author's proof. Pen and paper only; no
computation was run. Inputs taken on trust are listed in Section 7.

## Verdicts

| Node | Verdict |
|---|---|
| `sofic-radical-localizes-garden-of-eden-windows` (Theorem A) | PASS after a constant correction, landed in the artifact |
| `invariant-output-injective-automata-need-invisible-symmetry` (Corollary B) | PASS |
| `linear-invariant-output-automata-fail-augmentation` (Proposition C) | PASS |
| `invariant-output-automata-have-only-nonlinear-decoders` | PASS; the proof also excludes affine decoders and any alphabet `F_(2^j)` |
| `strict-automaton-tables-present-an-invisible-window-difference` (Theorem F) | PASS |
| `leavitt-unit-group-has-only-trivial-sofic-morphisms` (Theorem D) | PASS, given its prerequisites |
| `certificate-linear-automata-have-local-linear-decoders` | PASS |
| `one-invertible-certificate-fiber-forces-global-invertibility` | PASS |
| `certificate-linear-counterexamples-compile-to-lamp-algebras` | PASS |
| `nonlinear-certificate-fibers-are-all-surjective-or-all-strict` | PASS |
| `stable-finiteness-failure-refutes-surjunctivity` | PASS |
| `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant` | PASS |
| `leavitt-unit-certificate-predicates-are-decidable`, checker conventions | PASS |
| `split-comparisons-balance-induced-brauer-characters` | PASS |
| `chart-comparison-must-fuse-torus-classes` | PASS, with the 09-08 module identifications re-derived |
| `sofic-support-cannot-install-half-corner-comparison` | PASS |
| route `non-linear-sofic-via-leavitt-kaplansky-failure` | PASS as a conditional route |
| transporter exterior screen, uniform-depth exclusion | conclusion PASS; justification corrected in the artifact |

## 1. Theorem A: localization of Garden-of-Eden windows

* `Rad(G)` is a normal subgroup by bi-invariance of the normalized Hamming
  distance, with `F` enlarged by the needed products.
* **Amplification.** A disjoint union of one model per element averages the
  defects and the moving fractions. The `r`-fold product adds defects and
  multiplies fixed fractions. So `r` is chosen once, independent of `delta`.
* **Good points.** `d((phi(a)phi(b))^-1, phi(ab)^-1) = d(phi(a)phi(b), phi(ab))`,
  so `(v.a).b = v.(ab)` fails on at most a `delta`-fraction per pair.
* **Charts.** At a good point, `v.k = v.k'` iff `v.k` is fixed by `phi(k^-1 k')`.
  For one ordered pair the count is `|Fix phi(k^-1 k')|`, since `v -> v.k` is a
  bijection. The union runs over pairs, and several pairs can share one
  difference. For `Omega = {1, g, ..., g^(n-1)}` with `g` of large order,
  `|D| = 2(n-1)` while there are `n(n-1)/2` pairs. So the printed condition
  `|D|(1-eps_0/|D|)^r <= 1/4` does not bound the non-injective charts once
  `n >= 5`. **Correction landed:** take `|Omega|^2 (1-eps_0/|D|)^r <= 1/4`. It
  is still independent of `delta`, and nothing else changes.
* **Decoding at good points.** `z(k) := x(v.k)` defines a function on the set
  `SM` of group elements, whatever collisions occur, so `sigma_V tau_V = id` on
  `W` and there are at least `|A|^|W|` outputs.
* **Count.** A maximal family of disjoint injective charts has at least
  `|U|/|Omega|^2` members, and every output avoids `p` on each of them. The
  inequality `(3/4 - beta)|A|^-|Omega| / (|Omega|^2 ln|A|) <= beta` then fails
  as `delta -> 0`.
* **Refinement to `K = <M>`.** The image is a product over left `K`-cosets. The
  restriction to one coset is an injective automaton over `K`. A `G`-model at a
  scale `F` inside `K` restricts to a `K`-model, so `Rad(K) <= Rad(G)`.

## 2. Invariant outputs and linear parts

* **Corollary B.** Equal functions have equal essential coordinate sets, so
  `h M_eff = M_eff`. The rule is nonconstant because the automaton is
  injective and `|A| >= 2`, so `h` lies in `M_eff M_eff^-1`, inside `K`. The
  pattern `1 -> a, h -> b` with `a != b` is never produced. Theorem A over `K`
  on the window `{1, h}` puts `h` or `h^-1`, hence `h`, in `Rad(K)`.
* **Proposition C.**
  * `ha = a` follows by testing single-site configurations.
  * An injective linear automaton over a finite field has a linear left
    inverse: the clopen-patching argument with a constant certificate.
    Hence `tau_a` is injective iff `ca = 1` for some `c`, using
    `tau_c tau_a = tau_(ca)`.
  * Augmentation kills the modular case.
  * In the coprime case, `a = ea` iff `ha = a` for all `h`, and `1` is not in
    `e k[G]` unless `H = 1`.
* **Nonlinear decoders.**
  * Algebraic normal forms are unique on finite cubes. Invariance under
    `x_m -> x_(hm)` gives `ha = a` for the degree-one coefficients.
  * In `sum_s d_s f_s`, a shifted monomial of degree at least two keeps its
    degree, because left translation is injective on indices. So the
    degree-one part of `sigma tau` is `da`, and `da = 1` contradicts augmentation.
  * Constant terms never reach degree one, so affine decoders are excluded too.
  * The same comparison works for reduced polynomial functions over `F_(2^j)`.

## 3. Table groups and full radical

* **Theorem F.**
  * `x_a -> a` defines `pi: U -> G`.
  * The imposed relators and `pi` make the coincidence patterns on `S x M` and
    `Omega x M` exact.
  * Transport preserves `sigma tau = id` and the orphan on `x_Omega`, whose
    cells are distinct because `pi` separates them.
  * Theorem A over `U` gives an invisible `x_w^-1 x_w'`, nontrivial since
    `pi(x_w^-1 x_w') = w^-1 w'`.
* **Theorem D.** `Rad` is normal, `R^x` is simple, and a trivial radical would
  make `R^x` sofic.

## 4. Certificate-linear families and fiber rigidity

* **Local linear decoders.** `T_c` is a homeomorphism onto a compact image, so
  `x(1)` reads finitely many output coordinates. The resulting functional is
  well defined and linear on the image; extend it linearly. Coefficients are
  locally constant on a clopen cover, and the shifted formula gives `D E = id`.
* **One invertible fiber.**
  * If `T = I + K` with `W = im K` finite-dimensional and `T` injective, then
    `T` restricts to a bijection of `W`, and `T(v - w) = v` for the `w` with
    `Tw = Kv`.
  * A finite certificate change alters outputs only on `E D^-1`, so `A_c` is a
    finite-rank perturbation of the invertible `A_(c_*)` and is bijective.
  * The coefficient functions of `AB - I` are locally constant and vanish on the
    dense finite-change class, so they vanish everywhere.
* **Compiler.** The representation `pi_c` is faithful. The Fourier isomorphism
  needs `|L|` invertible and the character values in `K`: `C_2^a` over odd `F_p`,
  `C_3^a` over `F_4`. `F_4 -> M_2(F_2)` is a unital injection.
* **Nonlinear dichotomy.** Let `S` be injective and `T` surjective, agreeing off
  a finite `F`. For each fiber `Y` over `y_out`, `|T^-1(Y)| >= |Y|` by
  surjectivity and `|T^-1(Y)| <= |Y|` by the injection through `S`. Finite
  modifications are dense, and compactness realizes every target.
* **Linear refutation lemma.** `tau_B tau_A = tau_(BA) = id` gives
  injectivity. A surjective `tau_A` with a left inverse would force
  `tau_(AB) = id`.
* **Constant maps into infinite-stabilizer coset shifts.** The base coordinate
  is invariant under the stabilizer. Some stabilizer element moves its finite
  window off itself, so the local rule is constant.

## 5. Checker conventions

* `ca.py` computes `tau(x)(g) = mu(x(g m_i))` with products `cell * m` and
  `n * m`. `compose_is_identity` enumerates all patterns on `N.M`.
  `garden_of_eden` backtracks over the variables `Omega.M` and verifies any
  preimage it finds.
* In the prefix-table path, `s_i` prepends and `t_i` strips. The operators
  compose in product order, so the boundary modules are left modules.
* **Robustness.** Were `*` the opposite product, a passing automaton
  certificate would transport through `g -> g^-1` to an ordinary one, and a
  passing direct-finiteness pair would swap its factors. No convention slip can
  manufacture a false refutation.

## 6. The half-corner comparison region

* **Balance theorem.** `E_H` is an `F_p[H]`-bimodule map, and `q = Zbar Lbar` is an
  idempotent below `ebar`. Equal dimensions force `q = ebar`; induce the Brauer
  characters.
* **(D0).** Over `F_2`, `(1+z+z^2)^2 = 1+z+z^2`. `chi_4` has 2-defect zero, so
  `(1/15)(4 + sum_ord3 - sum_ord5)` is 2-integral and reduces to the 44-term sum.
* **(D1).**
  * On `rho_St`, `H` is an idempotent of rank two, `D + T_D^2` has rank one, and
    `S_D^2 = H` on `im H` and `0` on `ker H`, so `H + S_D^4 = 0`.
  * Ranks on simple modules are the multiplicities of projective covers, and
    `12 + 4 = 8 + 8`.
* **Brauer difference.**
  * The mod-2 decomposition matrix of `A_5` gives the characters
    `Phi_1 = (12,0,2,2)`, `Phi_V = (8,-1,a,b)`, `Phi_V2 = (8,-1,b,a)`,
    `Phi_St = (4,1,-1,-1)`, so `Delta_A = (0,3,0,0)`.
  * Frobenius-stable modules give the factor `w^k + w^(2k)`, and centralizers
    have order 9. The weights are `+2/3, -1/3, -1/3`, and fusion is forced.
* **Fusion in `Q`.** Swapping two children conjugates `G` to `G^2`. Swapping the
  second and third letters under the cone `0` turns `diag(G,G)` into `G` on the
  children of `0`. Prefix permutations move cones.
* **Sofic support.**
  * A sofic approximation gives a faithful rank that is regular on `K`, by free
    orbits at density one.
  * With `D = Z L'`, Sylvester's inequalities give `rho(D) = rho(f)`. Then
    `rho(P - D) = 0` forces `D = P`, and evaluation refutes the equivalence.
* **Screen correction.** The printed uniform-depth exclusion cited Corollary 2
  with the actor group itself as the finite image, but `<K, h>` need not be
  finite. The correct argument conjugates to `P_0^h f_0` inside the finite group
  `<K, h^-1 K h>`, and compares ranks of equivalent idempotents on the depth-`D`
  point module. It is landed in the screen artifact; the conclusion stands.
* **Kaplansky route to non-linear soficity.** If `alpha beta = 1` with `alpha` in
  `F_2[H]`, decompose `beta` over right `H`-cosets. The identity coset gives a
  right inverse `beta_1` in `F_2[H]`, and `beta_1 alpha = 1` would give
  `beta = beta_1`. The symmetric argument handles `beta`.

## 7. Inputs taken on trust

* `openai-leavitt-unit-nonsofic`, `binary-leavitt-elementary-group-is-simple`,
  `leavitt-gl-equals-el-and-perfect-unit-group` (Theorem D).
* Arzhantseva--Paunescu Theorem 7.4, statement level. Proposition 2.8's rank
  identity was re-derived.
* Machine data:
  * supports 30, 70, 132, 56 and 72;
  * the literal isomorphism `f_+ E ~= P E` through `b`;
  * `ev(E) = 0`;
  * the screen counts 359, 48 and 144.

## 8. Remarks recorded here only

* `leavitt-units-carry-injective-invariant-output-automaton`, bullet
  "Symmetrize a bijective automaton". The collision uses `w` of order two. For
  larger `H`, write `Sym(z)(g) = s((z(gh))_(h in H))` with `s` invariant under
  right translation of `H`; the conclusion is unchanged.
* `sofic-radical-localizes-garden-of-eden-windows-proof`, step 2 ("fix at most a
  quarter of the points in total") should be read with the per-pair correction
  of Section 1.
