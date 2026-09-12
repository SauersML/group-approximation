# Family N verification record

Lane `gk-vf-nonlinear`, 2026-09-12. Independent re-derivation of nonlinear-design landings
of the Gottschalk region. Each result was proved again from its statement and prerequisites,
not by rereading the author's argument. Nothing was run.

## Verdicts

| landing | claims | verdict |
|---|---|---|
| `4660e1411` (gk-invariant-output) | `normalizing-invariant-output-descends-to-quotient`, `invariant-output-rules-need-odd-invariant-monomials`, `right-symmetric-sensitivity-profile-admits-no-decoder` | PASS; the third is strengthened in Section 1.3 |
| `6be1b3b31` (gk-design-group) | `strict-automata-live-on-canonical-table-groups`, `triangular-forward-tables-force-surjectivity` | PASS |
| `a1b4a47cc` (gk-three-factor) | `table-groups-are-memory-holonomy-groups`, `amenable-decoder-memory-forces-surjectivity`, `unicyclic-strict-designs-present-nonsofic-one-relator-groups` | PASS |
| `de231f8c9` (gk-n-ff) | `invariant-output-injective-ca-need-torsion`, `leavitt-tower-does-not-embed-in-torsion-free-hosts`, `torsion-free-scalar-df-failure-gives-exotic-idempotents` | PASS (Section 5) |
| `2fdd8cc75` (gk-free-neg) | `formal-polynomial-strict-pairs-need-unstable-linearization` and its corollaries | PASS (Section 7) |
| `54ab1d134` (gk-n-twocycle) | `bijective-designs-force-every-finite-presentation` | PASS (Section 8) |
| `5b6ac9c99` (gk-n-klein) | `ternary-adjoint-image-is-balanced`, `klein-level-one-splitting-is-outside-adjoint-image`, `klein-expectation-splits-in-balanced-algebra`, route `level-two-klein-fullness-gives-klein-fullness` | PASS (Section 9) |
| `3c67b7dbd` (gk-n-klein, Section 7 as claims) | `klein-corner-contains-unital-copy-of-projective-group-algebra`, `adjoint-image-is-stable-under-klein-doubling` | PASS (Section 9) |
| `222a8b610`, `8b69514ac` (gk-n-highalpha) | `low-degree-strict-pairs-have-one-sided-linear-parts`, `low-degree-invariant-output-reduces-to-corner-fullness`, `unipotent-automata-over-finite-fields-are-surjective`, `low-degree-strict-automata-force-matrix-kaplansky-failure` | PASS (Section 10) |
| `f9bca65d4` (gk-n-boolean) | `boolean-core-is-uniform-single-demand-network-coding`, `strict-rule-pairs-pass-to-product-alphabets`, `smallest-boolean-strict-core-is-a-one-sided-inverse`, and the Section 6 classification claims | PASS (Section 12) |
| `8ef1f79d9` (gk-n-thompson-v) | `v-self-similar-rewrites-preserve-strict-pairs`; `thompson-v-is-sofic` confirmed OPEN with no route into it | PASS (Section 13) |
| `bfe4d46e8` (gk-n-twocycle) | `free-memory-injectivity-forces-universal-bijectivity` | PASS (Section 14) |
| `4aa38fd07` (gk-n-ae-decoder) | `bernoulli-codes-descend-to-window-subgroup`, `strict-kazhdan-compression-gives-no-bernoulli-deficit` | PASS (Section 15) |
| `16cc6319c` (gk-free-wild) | `mixed-bigon-difference-graphs-present-vh-square-complexes`, `cubulated-hyperbolic-table-cores-carry-no-strict-pair`, Lemma D | PASS (Section 16) |
| `ad664ec25`, `9baaf4657` (gk-n-defect) | `table-hosts-have-a-cell-count-betti-lower-bound`, `two-cell-window-differences-die-in-host-abelianization`, Corollary 3.2 free factor | PASS (Section 17) |
| `b7fef0670` (gk-n-defect) | `garden-of-eden-windows-fold-modulo-every-hinge-closure`, `transposed-hinges-are-conjugated-commutators` | PASS (Section 20) |
| `746491973` (gk-n-thompson-v) | routes `thompson-v-direct-finiteness-failure-from-swap-fullness`, `thompson-v-nonsurjunctive-from-direct-finiteness-failure`; Propositions 2.1–2.3, Lemma 3.1, Corollary 3.2, Proposition 9.1 | PASS (Section 21) |
| `fe7e9bf0c` (gk-n-ae-decoder) | `rokhlin-maximality-closed-under-local-embeddings`, `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers` | PASS (Section 22) |
| `86a10e7e9` (gk-n-thompson-v) | routes `thompson-v-df-failure-from-order-three-averaging-fullness`, `thompson-v-binary-df-failure-ascends-to-leavitt-units` | PASS (Section 18) |
| `02e8d9a28`, `73e17dbd7` (gk-n-ae-decoder) | `measurable-certificate-routing-preserves-bernoulli-measure`, `bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial`, `homomorphic-codes-cannot-compress-bernoulli-shifts`, route `leavitt-zero-supremum-via-measurable-compression` | PASS (Section 6) |

Section 6 of `invariant-output-descent-and-sensitivity-2026-09-12.md` (the ternary form) was
already covered by Sections 23–24 of `gk-verify-pos-permanence-chain-2026-09-12.md`, including
correction 7.4(e). It is not re-verified here.

Conventions throughout: `tau(x)(g) = f((x(g m))_(m in M))`, with left shifts
`(k.x)(g) = x(k^-1 g)`.

## 1. Invariant-output automata (`4660e1411`)

### 1.1 Descent through normalizing memory: PASS

**Setup.** `tau` is injective, and its output is invariant under a finite `H != 1`.
- By `invariant-output-injective-automata-need-invisible-symmetry`, `hM = M` and `f` is
  invariant under the relabeling `m -> hm`.
  - Re-derived: `f((x(ghm))_m) = f((x(gm))_m)` for every `x`.
  - The coordinates `gm` are distinct and `x` is arbitrary, so every input tuple occurs.
- Then `h = (hm) m^-1` lies in `K = <M>`.
- If `M` normalizes `H`, then `H` is normal in `K`.

**Proof check.**
- Injectivity passes to the copy over `K`. Configurations that differ on one left coset and
  agree elsewhere have distinct images.
- The fixed set `Fix_K` of right-`H`-invariant configurations is identified with `A^(K/H)`,
  equivariantly, and `kmH = (kH)(mH)`.
- The output lies in `Fix_K`, and `Fix_K` is proper because `H != 1` and `|A| >= 2`. So
  `tau(Fix_K)`, which is `bar-tau(A^Q)` under the identification, is a proper subset of
  `tau(A^K)`, which lies inside `Fix_K`. Hence `bar-tau` is injective and not surjective.
- Repeated memory cosets (`mH = m'H` with `m != m'`) only feed one cell to `f` twice. That is
  still a cellular automaton.

**Leavitt reading.**
- In `M_2(R)`, `w = [[0,1],[1,0]]`, and `C(w)` consists of the units of `R[x]/(x^2 - 1)`.
- In characteristic 2 that ring is `R[eps]/(eps^2)` with `eps = 1 + x`. So
  `C(w) = R^x ⋉ (R,+)`, with `w <-> 1` central, and `C(w)/<w> = R^x ⋉ (R/F_2)`.
- `N(<w>) = C(w)`, since `<w>` has order two.

**Correction to this record (gk-vf-nonlinear, after gk-invariant-output's report).** The implication
passes, but its hypothesis is never met. I missed this. If `M` normalizes `H`, then `H` is normal
in `K`.
- For `n` in `H` and `k` in `K`, `tau(n^-1 . x)(k) = tau(x)(n k) = tau(x)(k (k^-1 n k)) = tau(x)(k)`,
  because `k^-1 n k` lies in `H`.
- Translation by `n` therefore does not change the output on the `K`-copy, and injectivity forces
  `n = 1`.

So Proposition 2 holds only vacuously, and the Leavitt reading above constrains no design
(`invariant-output-symmetry-must-be-core-free`, landed by gk-p-simple-direct). The author corrected
the claim at `40131c7208`.

### 1.2 Odd invariant monomials: PASS

1. **Linear part.**
   - `tau(e_1) != tau(0)` forces some `g` with `g^-1 in M` and `f(e_(g^-1)) != f(0)`.
   - In algebraic normal form, `f(e_m) - f(0) = a_m`.
   - Relabeling invariance gives `a_(hm) = a_m`, and `m -> hm` is fixed-point free. So
     `supp a` is a nonempty union of pairs.
2. **Invariant monomials.**
   - An injective automaton permutes the constant configurations, so `f(1,...,1) != f(0,...,0)`.
     The difference is the number of nonconstant monomials mod 2.
   - Uniqueness of the normal form makes the monomial set `h`-stable, and non-invariant
     monomials pair up. So the invariant ones are odd in number.
   - Single variables are not invariant, so each invariant monomial has degree at least 2.
3. **Norm rules** have `a = 0`, which contradicts item 1.

### 1.3 Sensitivity profiles: PASS, and the hypothesis is stronger than needed

**The formula.** `tau(b e_k)(g) = f(b e_(g^-1 k)) = f(0) + p_b(g^-1 k)`, where
`p_b(m) = f(b e_m) - f(0)`. This is re-derived and correct, and so is the decoder count in
Theorem 4.

**Strengthening.** If `p_b(mc) = p_b(m)` for all `m`, with `c != 1` of ANY order, then
`P_(kc) = P_k`. So `tau(b e_(kc)) = tau(b e_k)` while `b e_(kc) != b e_k`, and `tau` is not
injective. No decoder and no condition on `ord(c)` is needed.

**Consequences.**
- The consequence in the claim holds, and is stronger than stated. Over `F_2`,
  `p_1 = supp a`, and an encoder whose linear support is right-invariant under any
  nontrivial element is not injective at all.
- For an invariant-output encoder with linear part `k + hk`, `c = k^-1 h k`.

Recorded as the established claim `sensitivity-profile-right-symmetry-forces-noninjectivity`
(route `sensitivity-right-symmetry-noninjective-proof`).

**Where the decoder count still adds something.** It is the right-symmetry analogue of the
augmentation argument, and its mechanism is not needed for the stated conclusion. Nothing
downstream relied on the order hypothesis.

## 2. Canonical table groups (`6be1b3b31`): PASS

**Lemmas 1–4.**
- **Lemma 1.** The points `g rho(s) rho(m)` coincide exactly by `E_rho`, and every assignment
  on distinct points extends to a configuration.
- **Lemma 2.** Composing with the quotient of classes preserves the projection to the marked class.
- **Lemma 3.** `sigma tau = id` plus surjectivity gives `sigma = tau^-1`.
- **Lemma 4.** Left inverses exist: a continuous inverse on the compact image depends on a
  finite window, which is extended arbitrarily.

**Lemma 5.** Class containment `E <= E_rho` makes the relators of `U_E` hold in `G`. The induced
map sends `x_m x_s` to `rho(m)rho(s)`, so reverse coincidences in `U_E` persist in `G`.

**Theorem A and Corollary B.** Choose a minimal `E` below `E_rho`. Lemma 5 then gives
`F_rho >= F_(rho_E)`. If `F_(rho_E)` lay in `𝓡_D`, Lemma 2 would put `F_rho` there.

**Proposition C.** `F_rho >= F` iff every spanning-tree hinge word of `F` dies. The marked class
reads `x_m x_s = 1` along tree edges from the base point. The sofic half is Gromov–Weiss.

**Lemma 6 and Theorem D.**
- Downward elimination works because `x_i` does not occur in later relators. After
  substitution each earlier `x_i` still occurs once in `r_i`.
- A free `U_E` is residually finite, hence surjunctive, and Lemmas 2, 3 and 5 carry
  bijectivity to every realization.

**Examples, checked.**
- **Single relator.** It is triangular: formal letters are distinct unless `s = s'` or `m = m'`,
  and then free reduction leaves `x_m = x_m'` or `x_s = x_s'`.
- **Hilbert hotel.** `x_c x_p = 1` in a group forces `x_p x_c = 1`.
- **`C_7` example.** `(1+g+g^2)(1+g^2+g^3+g^5+g^6) = 1` in `F_2[C_7]`, multiplied out: every
  `g^i` with `i != 0` appears twice, and `1` three times.

## 3. Holonomy normal form and design filters (`a1b4a47cc`): PASS

**Theorem H (Tietze normal form).**
- A pair `(s,m) ~ (s',m')` gives `x_s = x_s' x_m' x_m^-1`.
- Tree elimination expresses `x_s = x_(r_j) w_s`.
- A non-tree edge becomes `w_s = w_s' delta` after cancelling the root letter on the left.
- Roots of the other components occur in no relator and split off as free factors.
- The marked-class relators are the pairs with `(1_S, 1_M)`, so they are covered.
- **Example.** `<b | b^2>` from the edges `b` and `b^-1` checks.

**Proposition C (identity component).**
- Classes never straddle components, so the rule `nu_1` obtained by freezing the other block
  is well defined.
- `Phi_(E_1) = Phi_E` on assignments extended by the frozen block, and the marked class lies in
  the identity block.
- Both designs share the encoder, so strictness means non-surjectivity of the same `tau` in
  both.

**Corollary C'.**
- `U_(E_1) = Hol_M(E_1)` surjects onto the memory subgroup of `U_E`. It omits the other
  components' cycle relators.
- Over `U_E` the restricted decoder is still a left inverse. If `tau sigma' = id` held over
  `U_(E_1)`, coarsening would give it over `U_E`. So strictness passes down.
- Minimizing keeps strictness by Theorem A. `|S| + #edges` strictly decreases, so the process
  terminates.

**Theorem Am (amenable decoder memory).**
- `sigma` is surjective, and so is its copy over `H = <S>`.
- The Garden of Eden theorem makes that copy pre-injective, and coset restriction makes
  `sigma` pre-injective over `G`.
- **The final step** is `split-decoders-have-generic-cantor-fibers`, re-derived directly over
  every group. Suppose `tau` is strict, `z` is in the image and `y` is a Garden-of-Eden
  modification of `z` on a finite set. Put `psi = tau sigma`.
  - `psi(y)` is asymptotic to `psi(z) = z`, hence to `y`;
  - `psi(y) != y`, because `y` is not in the image;
  - `sigma(psi(y)) = sigma(y)`.

  So `sigma` is not pre-injective.
- **The design filter** follows because `U_E -> G` maps the decoder-letter subgroup onto the
  decoder memory group, and quotients of amenable groups are amenable.

**Corollary U.** A connected graph with `b_1 <= 1` gives a free or one-relator `Hol_M(E) = U_E`.
Strictness makes `U_E` non-surjunctive, hence nonsofic.
- **Trust surface:** the primitivity-rank remark leans on the landed one-relator region, which
  is not re-verified here.

## 4. Wiring audit (tip 7a6f30fee7)

- The three `4660e1411` claims and the two canonical-table claims carry `-proof` routes with
  the dependencies their proofs use.
- `amenable-decoder-memory-surjectivity-proof` requires the Garden of Eden citation, the split
  decoder claim and the holonomy claim.
- `unicyclic-strict-design-one-relator-proof` requires the holonomy claim and
  `sofic-groups-are-surjunctive`.
- `triangular-forward-tables-force-surjectivity-proof` requires Theorem A's claim and
  `residually-finite-groups-are-surjunctive`.
- No missing prerequisite was found. Nothing here establishes the goal or a Leavitt root.

## 5. Torsion-free host constraints (`de231f8c9`, gk-n-ff): PASS

**Proposition 2.1: invariant output forces a finite symmetry.**
- `F(x)(gH) = tau(x)(g)` is well defined by invariance and continuous.
- It is equivariant: `F(g'.x)(gH) = tau(x)(g'^-1 g) = (g'.F(x))(gH)`.
- For infinite `H` the verified constancy lemma
  (`full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`, negative-side record)
  makes `F`, and so `tau`, constant. That contradicts injectivity on `A^G` with `|A| >= 2`.
- The torsion-free consequence follows because nontrivial subgroups of torsion-free groups are
  infinite.

**The Leavitt tower does not embed in torsion-free hosts.**
- `u = 1 + s_0 t_1` has `u^2 = 1 + 2 s_0 t_1 + s_0 (t_1 s_0) t_1 = 1` over `F_2`.
- `s_0 t_1 = S[0]T[1]` is a basis monomial of the normal form, since `0` and `1` do not both end
  in `1`. So `u != 1`.
- Every member of the tower contains `R^x` or finite symmetric groups.

**Proposition 3.1: a one-sided pair gives a nontrivial idempotent.**
- `e = alpha beta` has `e^2 = alpha (beta alpha) beta = e`.
- `beta e alpha = 1` gives `e != 0`, and `e(1 - e) = 0` exhibits zero divisors.
- Trust surface: the tester transfer through `kaplansky-three-properties-fixed-fp-torsion-free-tester`
  is quoted, not re-derived.

Sections 4–5 of that artifact are status prose, and no established claim rests on them.
- Trust surfaces: clause (W8) and the solvable word problem of `S wr Z`.

## 6. Measurable compression (`02e8d9a28`, `73e17dbd7`, gk-n-ae-decoder): PASS

**Proposition 1.**
- The translates of `beta = {tau(x)(1) = b}` read every coordinate of `tau`.
- Lusin–Souslin makes the restriction of `tau` to the conull `X_0` a Borel isomorphism onto its
  image. So `beta` generates modulo null sets, and `h^Rok <= log |B|`.

**Corollary 2 / the route.**
- Seward's per-group formula gives `h_sup(U) < log |A|`.
- The zero-or-infinity dichotomy then gives `0`, and infinite-entropy actions are excluded through
  POS = INF.
- Both prerequisites were passed earlier (gk-verify-pos Sections 13 and 24). The route needs the
  open compression claim, so it establishes nothing.

**Theorem A: routing preserves the measure.**
1. *Transport.*
   - Equivariance with `h = g^-1` gives `rho_c(g) = 1` iff `rho_(g^-1.c)(1) = g^-1`.
   - Shift invariance of `mu_C` gives `E N = sum_g P(rho_c(1) = g^-1) = 1`.
2. *Every site is read.*
   - For almost every `c` the section `X_0^c` is conull.
   - A fixed-point-free symbol flip at an unread coordinate `h` preserves `mu_D` and does not
     change `tau(c, .)`. Injectivity on a conull set therefore forces every `h` to be read.
   - Measurability is fine, because the bad set of `c` is a countable union over `h`.
3. *In-degree one.* `N` is a nonnegative integer with `N >= 1` almost surely and `E N = 1`, so
   `N = 1` almost surely. Equivariance, `#rho_c^-1(h) = N(h^-1.c)`, plus countability gives
   bijectivity.
4. *Measure.* A coordinate bijection followed by coordinatewise symbol permutations preserves the
   uniform product measure. Fubini finishes.

**Theorem B: Bernoulli factors to infinite-stabilizer coset shifts are trivial.**
- `f = F(.)(K)` is `K`-invariant.
- `K` acts mixingly: `kP` misses `Q` outside the finite set `Q P^-1 ∩ K`. So `f` is almost
  everywhere constant.
- Equivariance, invariance of `mu` and countably many cosets extend the constant to every coset.

**Proposition 5: homomorphic codes cannot compress.**
- `tau` of a constant configuration is shift-fixed, hence constant. So `tau` restricts to a
  homomorphism `A -> B`, which has a nontrivial kernel element `a` because `|B| < |A|`.
- `tau(x c_a) = tau(x)` while `x c_a != x`.
- Multiplication by `c_a` preserves the measure, so no conull set of injectivity exists. Target
  translations change nothing.

**Sections 5–6 of that artifact.**
- *Continuous codes that are injective almost everywhere are pre-injective.* A finite collision is
  decided on a finite window, so swapping the pattern gives a positive-measure family of collisions.
- *Ascent along subgroups.* Coset-wise extension is well defined by equivariance, and Fubini keeps
  injectivity almost everywhere.
- The Bartholdi–Kielak calibration is quoted.

## 7. Formal polynomial strict pairs (`2fdd8cc75`, gk-free-neg): PASS

**Step 0: translation.**
- `T_(-d) o tau` and `sigma o T_d` compose to `sigma o tau`, formally, because formal composition
  is associative.
- `tau o sigma = id` is equivalent before and after the translation.
- `sigma(0) = sigma(tau(0))` gives `0` under the formal identity evaluated at `0`.

**Step 1: linear parts compose.**
- With the convention `L_a(x)(g) = sum_m a_m x(gm)`,
  `L_b o L_a (x)(g) = sum_(s,m) b_s a_m x(gsm) = L_(ba)(x)`, since `delta_s delta_m = delta_(sm)`.
- In `sigma o tau = L_sigma o (L_tau + N_tau) + N_sigma(tau)`, both correction terms lie in `I^2`.
- So `J_sigma(0) J_tau(0) = 1`, and `L_a = id` iff `a = 1`.

**Step 2: direct finiteness.** It gives the two-sided inverse `J_tau(0)^-1`, with finite support.

**Step 3: the monoid `P`.**
- *Composition is well defined.* The degree-`j` part of `phi o psi` uses only parts of degree at
  most `j` of both maps, because `psi` has no constant term. That is finitely many terms, each
  with finite memory.
- *Tangent-to-identity form.* `phi = L_a o (id + Q)` with `Q = L_(a^-1) o N_phi` of order at
  least 2. This uses linearity of `L_a`.
- *Right inverse.* `psi = id - Q o psi` is solved degree by degree. The degree-`j` part of
  `Q o psi` reads only degrees below `j` of `psi`.
- *Two-sided.* Build `chi` with `psi o chi = id`. Then `id + Q = (id + Q) o psi o chi = chi`.

**Step 4: uniqueness.**
- `sigma = sigma o (tau o psi) = (sigma o tau) o psi = psi`, so `tau o sigma = id` in `P`.
- Both sides are polynomial, so the identity is formal.

**Corollaries.**
- *Infinite fields.* A polynomial vanishing on all `k`-points is zero.
- *Characteristic `p`.* Use the prime-field reduction of stable finiteness.
- *Characteristic 0.* Use Kaplansky.
- *Specialization.* A formal identity over a finitely generated coefficient ring specializes.

**Section 4 (collapse defect).** `d(X^2 - X)/dX = 2c - 1 = 1` at `c in F_2`, so
`J_sigma(tau(c)) J_tau(c) = 1 + D(c)`. It is stated as an open direction and not wired as
established.

## 8. Bijective forcing of table cores (`54ab1d134`, gk-n-twocycle): PASS

**Lemma 1: holonomy shape.**
- `x 1^-1 = 1 xbar^-1` gives `xbar = x^-1`.
- The prefix letters `p_i` follow the word, and `p_n = 1` closes it.
- Eliminating the new letters is a Tietze move back to `P`.

**The composite reads exactly these cells.**
- Key tracks at `(abar_r, v_r)` and `(bbar_r, z_r)`.
- The data track at `(1_S,1_M)`.
- The key tracks inside the data term at `(1_S,u_r)`, `(1_S,w_r)`, `(h_r,v_r)` and `(h_r,z_r)`.
  - For example, `sigma_d` reads `y_(a_r)(g h_r) = x_(a_r)(g h_r v_r)`.

**Lemma 2.**
- *Sufficiency.* The two products for relator `r` coincide on `E_P` and cancel over `F_2`.
- *Domination, key tracks.* Distinct classes receive distinct key symbols.
- *Domination, data track.* The assignment `a_r = 1/0` on the two classes and `b_r = 1` on both
  `b`-classes adds `1` to the data output.
  - Assignments on different tracks never conflict.
  - Other relators' tracks are set to `0`.
  - This holds even when `(1_S,u_r)` is the marked class.

**Lemma 3.** The private letters `x_(abar_r)`, `x_(bbar_r)` and `x_(h_r) = x_(u_r) x_(v_r)^-1`
eliminate. The last relator then becomes `u_r v_r^-1 z_r = w_r`.

**Lemma 4.** `tau = gamma o beta` in every group.
- `beta` translates the key tracks.
- `gamma`, over the translated tracks `y = beta(x)`, adds
  `y_(a_r)(g u_r v_r^-1) y_(b_r)(g w_r z_r^-1) = x_(a_r)(g u_r) x_(b_r)(g w_r)`.
  It is an involution over `F_2`.

**Corollary 3.** Composing with a bijective automaton preserves injectivity and non-surjectivity.

## 9. The balanced invariant of the ternary adjoint image (`5b6ac9c99`, gk-n-klein): PASS

**Setup.** In `Q = R (x) R^op` with `(a (x) b)(a' (x) b') = aa' (x) (b'b)`:
- `rho(g) = g (x) g^-1` is multiplicative and unital;
- `(-g) (x) (-g)^-1 = g (x) g^-1`.

**Theorem 1 and Lemma 2.**
- `mu(rho(g)) = mu'(rho(g)) = 1` and both maps are linear.
- For `T = sum a_i (x) b_i` and `T'`:
  - `mu(TT') = sum_i a_i mu(T') b_i`, which is `mu(T')mu(T)` when `mu(T')` is scalar;
  - `mu'(TT') = sum_j b'_j mu'(T) a'_j`, which is `mu'(T)mu'(T')` when `mu'(T)` is scalar.
- So `N` is a unital subalgebra with character `mu`.

**Proposition 3.**
- *The group K.* `wd = e_10 - e_01` and `dw = -wd`, so `K ~= C_2 x C_2` in `PG`. Also `w^2 = d^2 = 1`.
- *Expansion.* `rho(e_K) = 1 (x) 1 + w (x) w + d (x) d - wd (x) wd`. In the 16 basis tensors the
  coefficients are:
  - `2` on `e_00 (x) e_00`, `e_11 (x) e_11`, `e_01 (x) e_10` and `e_10 (x) e_01`;
  - `0` on `e_00 (x) e_11`, `e_11 (x) e_00`, `e_01 (x) e_01` and `e_10 (x) e_10`;
  - no term at all on the other eight.
- *Factorization.* `delta Psi = 2 sum_(i,j) e_ij (x) e_ji` matches, and `Psi delta = 2 sum_i 1 (x) 1 = 1`.

**Proposition 4.**
- Completeness gives `mu(delta_C) = 1`, and `T[alpha] S[alpha] = 1` gives `mu'(delta_C) = |C|`.
- The same for `Psi_C` with `|C|^-1`.
- The prefix-code property gives `Psi_C delta_C = 1`.
- For `C = {0,1}`, `mu' = 2 != 1`, so `delta` and `Psi` lie outside `N`, which contains the image.

**Proposition 5.**
- `delta^2 = sum s_i s_j (x) t_j t_i = delta_(C_2)`, and `Psi^2 = 4 sum T (x) S = Psi_(C_2)`.
- `|C_2| = 4 = 1`, so both lie in `N`.
- `Psi^2 rho(e_K) delta^2 = Psi^2 delta^2 = Psi (Psi delta) delta = 1`.

**Proposition 6.**
- *The group K_4.*
  - `D ~= C_2^4` contains `-1`, so `|Dbar| = 8`.
  - `V_4` permutes the level-two prefixes regularly, normalizes `D`, and meets `±D` only in `1`.
  - So `|K_4| = 32`, and `32 = 2` is invertible.
- *Containment.* `w = u_(10)` flips the first bit, and `d` has signs `(+,+,-,-)` at level two.
- *The D-average.* `rho(d_eps) = d_eps (x) d_eps`, and averaging `eps_alpha eps_gamma` gives
  `delta_(alpha gamma)`. So the average is `sum_alpha e_(alpha alpha) (x) e_(alpha alpha)`.
- *The V_4-average.* Multiplying by `rho(u_x) = u_x (x) u_x`, with `u_x^-1 = u_x`, gives
  `e_(alpha, alpha xor x) (x) e_(alpha xor x, alpha)`, and the sum is `sum e_(alpha beta) (x) e_(beta alpha)`.
- *Normalization.* `2 . 32 = 1` in `F_3`, and the result equals `delta^2 Psi^2`.
- *Level-two transfer.* `c e_(K_4) b = 1` gives `(c e_(K_4)) e_K (e_(K_4) b) = 1`.

**Section 6 remark.** `GL_2(F_3)` has order 48, which gives 24 classes in `PG`. Their images lie in
a 16-dimensional span, so `rho` has a nontrivial kernel.

**Section 7.**
- *Proposition 7.*
  - `delta(g) w = s_0 g t_1 + s_1 g t_0 = w delta(g)` and `delta(g) d = d delta(g)`.
  - For injectivity, `delta(h)` is in `K` exactly when `diag(h,h) = ±1`, because
    `±d = diag(±1, ∓1)` would force `1 = -1`.
- *Proposition 8.*
  - `delta rho(g) = sum s_i g (x) g^-1 t_i = rho(delta(g)) delta`, using `delta(g) s_i = s_i g`.
  - `Psi rho(delta(g)) = rho(g) Psi`.
- *Corollary 9.* The flip is an anti-automorphism with `sigma(rho(g)) = rho(g^-1)` and
  `sigma(delta^2) = Psi^2`. That closes the three-way equivalence.

## 10. Low-degree strict pairs over finite fields (`222a8b610`, `8b69514ac`, gk-n-highalpha): PASS

**Theorem 1: linear parts.**
- Substituting components of degree at most `deg tau`, with no constant term, into a monomial of
  degree `D <= deg sigma` gives monomials of total degree at most `deg sigma deg tau < q`.
- Identifying variables through product coincidences raises exponents but never beyond the total
  degree. So the substituted polynomial is already reduced.
- Reduced representatives are unique, so the functional identity is coefficientwise.
- The degree-one part comes only from `D = 1`, and it reads `C A = I`.

**Corollary 2.**
- (a) Left inverse plus surjectivity would give `tau_C = tau_A^-1` and `AC = I`.
- (b) `tau_C o tau` has linear part `tau_(CA) = id` and decoder `sigma o tau_A`. Linear
  substitution raises no degree.

**Corollary 3: invariant output.**
- *Linear part.* Invariance holds as functions, hence for reduced polynomials over the union of
  both variable sets. Comparing the coefficient of `x_u` gives `A_u = A_(h^-1 u)`, that is `hA = A`.
- *(i)* When `p` divides `|H|`, orbit constancy gives `eps(A) = 0`, which contradicts
  `eps(C) eps(A) = I`.
- *(ii)* `eA = A`, and the converse design `tau_(eB)` has invariant output.
- *Always case (a).* `AC = I` with `A = eA` would force `e = e(AC) = (eA)C = AC = I`.
- Restriction of scalars keeps `e` in `F_p[G]`.

**Example 4.** On `F_8`, `x^15 = x` and `15 >= 8`. The linear parts are 0, so the bound is needed.

**Theorem 7: unipotent case.**
- *The formal endomorphisms.* `phi^*` maps `x_u` to the local rule at `u`. Then
  `(psi phi)^* = phi^* psi^*`, by expanding `F_psi((F_phi((x_(uts))_s))_t)` both ways.
- *Step 1.* The exponent bound makes `sigma tau = id` formal, so `tau^* sigma^* = id_P`.
- *Step 2.*
  - For a homogeneous `f` of degree `j`, the degree-`j` part of `tau^*(f)` is `tau_A^*(f)`.
  - `tau_A^*` is a degree-preserving automorphism, since `CA = AC = I`.
  - The lowest part of `tau^*(f)` is `tau_A^*(f_j) != 0`, so `tau^*` is injective.
- *Step 3.* `sigma^* = (tau^*)^-1`, so `tau sigma = id` formally, and therefore as functions.
- Items (ii) and (iii) follow.

**Proposition 8: words.** This is downward induction on the suffixes `S_j`.
- Injectivity of `tau` makes each `S_j` injective, so `W_j` is injective on the image of `S_(j+1)`.
- A bijective factor preserves surjectivity. A square linear factor is either surjective or the
  witness.
- Trust surface: the linear left inverse cites `certificate-linear-automata-have-local-linear-decoders`.

## 11. Level-two membership equations (`24d073e3c`, gk-n-klein Section 8): PASS

**Lemma 10.** The level-two code is complete, so the two families act as dual bases:
- `(T[b] (x) S[c])(S[b'] (x) T[c']) = delta_(bb') delta_(cc') 1 (x) 1`;
- `sum_(b,c) (S[b] (x) T[c])(T[b] (x) S[c]) = 1 (x) 1`.

Right multiplication by `S[b'] (x) T[c']` extracts the coefficients uniquely.

**Proposition 11.**
- `T[a] g = sum_b g_(ab) T[b]` and `g^-1 S[a] = sum_c S[c] h_(ca)`, both from completeness.
- So `Psi^2 rho(g) = sum_(b,c) (sum_a g_(ab) (x) h_(ca)^op)(T[b] (x) S[c]^op)`. The op-order of the
  second factor is `(S[c] h_(ca))^op`.
- Coefficient comparison gives the sixteen equations.

**Corollary 12.**
- The Z-grading `deg s_i = 1`, `deg t_i = -1` is compatible with the relations, which are
  homogeneous of degree 0.
- `S[b] (x) T[c]^op` has bidegree `(2,-2)`, while degree-zero entries give bidegree `(0,0)`.
- Examples: the entries of `K_4`, the level-two sign and permutation units, are scalars.

## 12. The Boolean core (`f9bca65d4`, gk-n-boolean): PASS

**Proposition 1.** Source assignments are exactly the class-constant `p`, and the relay and sink
computation is the left side of `Dec`.

**Theorem 2: product alphabets.**
- Relay `s` outputs `(mu(p_A(s,.)), p_B(s,1))`, so the sink returns `(p_A(1,1), p_B(1,1))`.
- A failing `q_A` with constant `q_B` fails in the first coordinate.
- Corollary 2.3: every `k` divides some `n!`, and surjunctivity descends from `kl` to `k`.

**Proposition 3: discrete forward table.**
- Cells are independent. Two rows `w`, `w'` with `mu(w) = mu(w')` and `w_1 != w'_1`, with equal
  other rows, give the sink one input but two demands.
- So `mu = f o pi_1` and `nu = f^-1 o pi_1`.

**Proposition 4.**
- *`S = {1}`.* `nu` is onto, hence a permutation.
- *`T_r` containing `T_f^t`.* A `T_r`-constant `q` is `T_f^t`-constant.
- *`M = {1}`.* Changing the symbol of the class of `(1,1)` keeps every relay output when
  `mu(c) = mu(c')`, but changes the demand.

**Theorem 5.**
- The column copy returns `p(a,b) = p(1,1)` forward and `q(b,a)` in reverse.
- In additive `Z`, `x_a = 1` and `x_b = -1` give forward values `0,-1,1,0` and reverse values
  `0,1,-1,0`. So `Z` realizes exactly `T_f` and `T_0`, and surjunctivity of `Z` forces `Enc(T_0)`.

**Theorem 6.2, re-derived row by row.**
- *`O ~ B`.* `g(c) = mu(c,c)` is a bijection, `nu(y,r) = g^-1(y)`, and the reverse sink returns `d`.
- *`O ~ A` and `A ~ X`.* The images `I_c` are disjoint, nonempty and |A| in number, so they are
  singletons.
- *`B ~ X`.* Each `h_w` is a bijection with `nu(y,z) = h_w^-1(y)` for all `z`, so all `h_w` agree.
- *`B ~ A`.*
  - Over two symbols, disjoint `J_0` and `J_1` would make `mu(w,.)` constant, which forces `h_0 = h_1`.
  - Over three or more symbols, the block code `g_P = id`, `g_Q = (0 1)` decodes forward.
  - Reverse, case `O' ~ B'`: `e = 2`, `e' = d = 0` gives output `g_P(g_Q(0)) = 1`.
  - Reverse, otherwise: `e = d = 0`, `e' = 2` gives output `g_Q(0) = 1`.
  - Both choices are consistent with `T_r`, and `X'` enters only through the block of relay `b`.
- *Example 6.4.*
  - `h_1 = (0 2)` fixes 1, and `h_2 = (0 1)` fixes 2.
  - The reverse relays give `h_0(0) = 0` and `h_2(0) = 1`, and the sink gives `h_1(0) = 2`.
  - The converse uses injectivity of `w -> h_w(w)`: equal `h_w(w)` gives equal `nu(., z)`, hence
    equal `h_w`.
  - Over two symbols this forces `h_0 = h_1`.

## 13. Thompson V self-similar rewrites (`8ef1f79d9`, gk-n-thompson-v): PASS

**The rewrite claim.**
- An injective homomorphism `phi` preserves and reflects every product coincidence, so both
  tables are unchanged. By Theorem A of the canonical-table record, strictness is unchanged.
- For the product pair, `tau_1 x tau_2` with left inverse `sigma_1 x sigma_2` is surjective iff both
  factors are.
- So the descent route correctly carries `invalidates:`, and its prerequisite is refuted.

**Decision check.**
- `thompson-v-is-sofic` is OPEN with no route targeting it.
- Its consequence routes (`thompson-v-surjunctive-from-soficity`,
  `thompson-v-stable-finiteness-from-soficity`) cannot complete.
- `thompson-v-nonsurjunctivity-ascends-to-leavitt-units` and `thompson-v-not-sofic-from-nonsurjunctivity`
  are valid. Each needs the open root `thompson-v-nonsurjunctive`.

## 14. Injectivity over a surjunctive cover (`bfe4d46e8`, gk-n-twocycle): PASS

**Theorem G.**
- *Step 1.* Over surjunctive `H`, injective implies bijective, and Curtis–Hedlund–Lyndon gives a
  cellular inverse.
- *Step 2.*
  - `tau_H` is the product over left `K_H`-cosets of copies of `tau_(K_H)`, so each copy is
    bijective.
  - The inverse of the copy is continuous and equivariant on `A^(K_H)`, hence a cellular automaton
    over `K_H`, with memory `S_H` inside `K_H`.
  - Extending coset-wise gives `tau_H^-1`.
- *Step 3.*
  - For `s` in `S_H` and `m` in `M`, `g phi(s) rho_G(m) = g phi(s rho_H(m))`, because both factors
    lie in `K_H`.
  - So `phi` preserves equalities and products equal to `1`. The realized forward table over `G`
    is coarser than the one over `H`, which is forward sufficient.
  - Lemma 2 of the canonical-table record gives `sigma_G tau_G = id`, and the reverse composite
    is symmetric.
  - Address collisions in `G` are handled by Lemma 1.
- *Corollary G1.* Free groups are residually finite, and every assignment of letters extends to a
  homomorphism.
- *Corollary G2.* This is the contrapositive, with compatibility meaning `phi o rho_H = rho_G` on the
  memory group.

## 15. Window descent and the Kun–Thom calibration (`4aa38fd07`, gk-n-ae-decoder): PASS

**Lemma 7.2 (descent to the window subgroup).**
- `((gk)^-1 . x)(k') = x(g k k')`, so the output on `gK` reads only `gK`.
- With `z(k) = x(gk)`, `(k^-1 . z)(k') = x(g k k')`, so the output on `gK` is `tau_K(z)`.
- *(<=)* A countable product of conull sets is conull, and the product map is injective on it.
- *(=>)* Inputs that differ only on one coset have outputs that differ only there. So for almost
  every exterior configuration, injectivity on the conull section is injectivity of `tau_K` on a
  conull set.

**Proposition 7.4 (the Kun–Thom actor has no deficit).**
- A residually finite `G` is sofic, and by the localization theorem (gk-verify-pos Section 21) it
  is Rokhlin-maximal.
- Proposition 1 then excludes compression.
- The strict compressor is contextual, not used in the proof. Existence re-derived: take `A` in
  `SL_d(Z)` with `A N^d` a proper subset of `N^d`, such as `[[1,1],[0,1]] (+) I`.
  - It induces an automorphism of `F_q[x^±]` that maps `F_q[x]` onto a proper subring `S`.
  - `EL_r(S)` is proper in `EL_r(F_q[x])`, since `e_12(a)` with `a` outside `S` is not in it.
- So the prose-only citation of part 2 of `surjunctive-groups-carry-invisible-rigid-defects` is not
  load-bearing, and the route's `requires:` are complete.

Sections 7.3 and 7.5 of that artifact are heuristic prose with no claim attached.

## 16. VH square-complex table cores (`16cc6319c`, gk-free-wild): PASS

**Theorem B.**
- *Parallel same-orientation edge.* The tree gives `w_s = w_s' delta_t`, and the relator
  `w_s = w_s' delta_e` becomes `delta_t = delta_e`.
  - With `delta_t = x_h x_v^-1` and `delta_e = x_v' x_h'^-1`, this is `x_h x_v^-1 x_h' x_v'^-1 = 1`.
- *Reversed edge.* `w_s' = w_s delta_e` gives `delta_t delta_e = 1`, which is the HV word
  `x_h x_v^-1 x_h'' x_v''^-1`.
- Theorem H, with one component, keeps all of `M'` as generators.
- *Converse.* `(s_q, v_q) ~ (1, h_q)` is the edge `1 -> s_q` with label `x_(h_q) x_(v_q)^-1`, and
  `(s_q, h'_q) ~ (1, v'_q)` is the parallel edge with label `x_(v'_q) x_(h'_q)^-1`. The relator is
  the square `q`.

**Proposition C.**
- Trust surface: Agol plus Haglund–Wise gives residual finiteness, hence soficity.
- It then contradicts `forward-relations-of-a-counterexample-have-a-nonsofic-core`.

**Lemma D.**
- In `F_2[G]`, `s m_1 + s m_2 + s' m_1 + s' m_2 = 0`, with `s m_1 != s m_2` and `s m_1 != s' m_1`. So
  `s m_1 = s' m_2` and `s m_2 = s' m_1`.
- Hence `m_2 m_1^-1 = s'^-1 s = m_1 m_2^-1`, which is a nontrivial involution.

**Remarks.**
- The Wise and Burger–Mozes properties in Section 3 are quoted.
- `strict-automaton-on-lattice-in-product-of-trees` stays OPEN.

## 17. The abelian layer of table hosts (`ad664ec25`, `9baaf4657`, gk-n-defect): PASS

**Lemma 1.1.** The relators are the cycle holonomies. Labels abelianize to
`v_e = e_m' - e_m`, with `e_1 = 0`, and a cycle basis generates `L`.

**Theorem 2.1.**
- Spanning trees of the classes give `|S||M| - |P|` edges, so `b_1(Gamma_E) = |S||M| - |P| - |S| + 1`.
- `L` has rank at most `b_1(Gamma_E)`, so `rank H^ab >= |P| - [(|S|-1)(|M|-1) + 1]`.
  - The algebra checks: `(|S|-1)(|M|-1) + 1 = |S||M| - |S| - |M| + 2`.
- *Scope note.* In the 2 x 2 sanity check with a discrete table the difference graph is
  disconnected, so the displayed connected bound does not literally apply. This is not a
  claim-level issue.
  - The author corrected the disconnected remark at `a2a813c847`, and the corrected counts
    re-derive.
  - With `c` components, `b_1(Gamma_E) = |S||M| - |P| - |S| + c`, so
    `rank Hol_M(E)^ab >= |P| - (|S|-1)(|M|-1) - c`.
  - Since `U_E = Hol_M(E) * F_(c-1)`, the bound `b_1(U_E) >= |P| - (|S|-1)(|M|-1) - 1` holds
    verbatim.
  - In the discrete 2 x 2 case (`c = 2`) this gives `b_1(U_E) >= 2` and `b_1(Hol) >= 1`, which
    matches `Z * Z` and `Z`. The earlier text, "`|S| - c` in place of `|S| - 1`", overstated it.

**Proposition 3.1.**
- Zero anchor charge on every cycle gives `psi(L) = 0`, so `psi` descends onto `Z`.
- Subgroups with finite abelianization map to `0`.

**Corollary 3.2.**
- `x_m' x_m^-1 = d_m' d_m^-1` with `d_m = x_m x_(m_0)^-1`, and `{t} ∪ {d_m}` is a free basis
  (Nielsen). So the relators avoid `t`, and `Hol = Z * Q`.
- A group with (T) has FA, so it is conjugate into a factor, and infinite subgroups of `Z` are not
  Kazhdan.

**Theorem 4.1.**
- `Omega^-1 Omega = {1, d, d^-1}` meets the sofic radical, and the radical is a subgroup. So `d` lies
  in `Rad_sof(H)`, which is inside `[H,H]`, since `H^ab` is sofic.
- The image of `m_1 m_2^-1` is `e_(m_1) - e_(m_2) + L`.
- *Corollary 4.2.* `psi(e_d) = 1`.

## 18. Binary averaging target over Thompson V (`86a10e7e9`, gk-n-thompson-v): PASS

**The element `h`.** It cyclically permutes the cylinders `00 -> 01 -> 1 -> 00` and has order
three. `e_h = 1 + h + h^2` is idempotent over `F_2`, since `3 = 1`.

**Both routes.**
- *DF failure.* `a = e_h b` and `d = c e_h` give `d a = c e_h b = 1`. If `a d = 1`, then `1` lies in
  `e_h F_2[V]`, which forces `e_h = 1`, but `h != 1`.
- *Ascent.* `F_2[V]` is a unital subalgebra of `F_2[R^x]`.
- The target claim `thompson-v-order-three-averaging-idempotent-is-full` is OPEN.

## 19. Disjoint footprints, the multilinear defect and formalizability (`260815a21`, gk-free-neg): PASS

**Theorem 5 (DF).**
- A decoder monomial `c prod Y_(s,j)` becomes `c prod mu_j((X_(gsm))_(m in F_j))`.
- (DF) makes the cell sets `g s F_j` of distinct variables in one monomial pairwise disjoint, and
  multilinearity in `Y` forbids repeating a factor. A product of reduced polynomials in disjoint
  variable sets is reduced, and so is a sum of reduced terms.
- The composite equals `X_(g,i)` on `F_q`-points, so it is `X_(g,i)` formally, by uniqueness of
  reduced representatives. Theorem 1 finishes.
- Affine decoders satisfy (DF).
- Restriction of scalars along `F_q -> M_k(F_p)`, as in Section 10.

**6.1 calibration, recomputed.**
- *Multilinear representatives.*
  - `tau = T_2 T_1` gives `(a + b(c+ab), b, c+ab)`, which reduces to `(a + ab + bc, b, c + ab)`.
  - `sigma = T_1 T_2` gives `(a + bc, b, c + (a+bc)b)`, which reduces to `(a + bc, b, c + ab + bc)`.
- *The formal composite.*
  - First coordinate: `a + ab + bc + b(c + ab) = a + ab + ab^2`.
  - Third coordinate: `c + ab + (a + ab + bc)b + b(c + ab) = c + bc + b^2 c`.
- *Jacobians at `(1,0,0)`.*
  - Row 1 of `J_tau` is `(1+b, a+c, b) = (1,1,0)`, and row 3 is `(b, a, 1) = (0,1,1)`.
  - Row 3 of `J_sigma` is `(b, a+c, 1+b) = (0,1,1)`.
  - `J_sigma J_tau = I + e_12`, with row 3 `(0, 0, 1)` because `1 + 1 = 0`.
- *Unreduced representatives compose formally.*
  - First coordinate: `a + bc + ab^2 + b(c + ab) = a`.
  - Third coordinate: `c + ab + (a + bc + ab^2)b + b^2(c + ab) = c`.

**6.2.**
- Adding `(X_h^2 - X_h)P` changes the linearization at a Boolean point by `P(c)`, since
  `2c - 1 = 1` in characteristic 2.
- A shear `x_i -> x_i + f(x_(-i))` is a formal involution in characteristic 2.
- With `f` the indicator of a point, it swaps the two endpoints of one hypercube edge.
- Transpositions along the edges of a connected graph generate the symmetric group on its vertices.

**6.3 Bennett form.**
- `V(x,0) = (tau(x), x + sigma(tau(x)))`.
- `J_(S o T) = [[1,b],[0,1]] [[1,0],[a,1]] = [[1+ba, b],[a,1]] = [[D, b],[a,1]]` in characteristic 2.

`binary-left-inverse-pairs-are-formalizable` and `stable-finiteness-forces-binary-surjunctivity`
stay OPEN, and nothing here establishes them.

## 20. Hinge closures and transposed hinges (`b7fef0670`, gk-n-defect): PASS

**Inputs.**
- `T_r(H/N)` dominates `P` iff every hinge word of `P` lies in `N`, that is, iff
  `N ⊇ N_P(H)`.
- (Q) `tau_H(z o q)(g) = mu((z(q(g) q(m)))_m)`.

**Theorem 1.1.**
- Over `Q = H/N_P(H)` the forward table is coarser, hence sufficient, and the reverse table
  dominates `P`. So `tau_Q` is surjective.
- If `q` separated every `p`-distinguished pair, then `z(q(w)) = p(w)` would be well defined, and
  lifting a preimage along (Q) would place `p` in the image over `H`.
- `q(w) = q(w')` iff `w^-1 w'` lies in `N`.

**Remark 1.2.** A homomorphism into a surjunctive `K` coarsens the forward table, so the
realization over `K` is bijective, and all hinge words of some minimal `P` die in `K`.

**Corollary 1.3.**
- `𝓡_D` is nonempty: over the trivial group `tau` is a bijection of `A`, so the coarsest
  partition is reverse sufficient.
- A two-cell window has one pair, so `p(1) != p(d)` and `d` lies in every `N_P(H)`.
- The containments `⊆ Rad_surj ⊆ Rad_sof` follow from Remark 1.2 and Gromov–Weiss.

**Corollary 1.4.**
- By Zorn there is a maximal normal `K` avoiding `d`, and every larger normal subgroup contains `d`.
- The forward table over `H/K` is coarser, and (Q) transports the Garden of Eden from `H/K` to `H`.
- The normal closure of `dK` is the monolith.

**Lemma 2.1.** With `c = sm = s'm'`, `c^-1 s' = m'^-1` and `c m^-1 = s` give
`s'^-1 m'^-1 m c m^-1 m' c^-1 s' = s'^-1 m'^-1 m s`.

**Corollary 2.2.**
- *Rooted identifications.* `c = m'`, so the hinge is `[m'^-1, m] = m'^-1 m m' m^-1`.
- *Marked class.* `c = 1`, so the hinge is `1`.

**Example 2.3.** `s = u c^-1 u^-1 l^-1` gives `s l = u c^-1 u^-1 = m'`, and the hinge is
`[u c u^-1, l] = d`.

Section 3 of that artifact is a design target, recorded as prose.

## 21. Thompson V linear targets, first batch (`746491973`, gk-n-thompson-v): PASS

**Proposition 2.1.**
- `e^2 = 4(1 + 2w + w^2) = 4(2 + 2w) = 8(1+w) = 2(1+w)` mod 3.
- `e_h^2 = 1 + h^2 + h^4 + 2(h + h^2 + h^3) = 1 + h + h^2` mod 2.

**Proposition 2.2.** `(1-e)a = 0`, so `ad = 1` would force `1 - e = 0`.

**Proposition 2.3.**
- `w e = 2(w + 1) = e`.
- Conversely `e a = 2(a + wa) = 4a = a`.
- A unit `a` with `wa = a` forces `w = 1`.

**No single permutation term.** `d(1+w) = g^-1`, and multiplying by `1 - w` on the right gives
`g^-1(1-w) = d(1 - w^2) = 0`.

**Lemma 3.1 and Corollary 3.2.**
- On `M = F_3[Omega]`, with `Omega` the one-sided sequences, `s_i delta_x = delta_(ix)` and
  `t_i delta_(jx) = delta_(ij) delta_x` satisfy the Leavitt relations.
- Elements of `V` act by permutation matrices, so every element of the image has equal row and
  column sums.
- `s0 + s1` has column sums `2` and row sums `1`. `2(t0 + t1)` has column sums `2` and row sums
  `2 + 2 = 1`.
- Unequal actions on `M` mean unequal elements of `R`. Faithfulness is not needed.

**Proposition 9.1.**
- `h e_h = e_h` since `h^3 = 1`, and `e_h a = 3a = a` over `F_2`.
- The trace-zero idempotent `h + h^2 = 1 - e_h` checks.

**Routes.** `thompson-v-direct-finiteness-failure-from-swap-fullness` uses Proposition 2.2 with the
involution `w` of `V`, and `thompson-v-nonsurjunctive-from-direct-finiteness-failure` uses the
verified stable-finiteness criterion. Both are valid, and every target claim stays OPEN.

## 22. Rokhlin maximality under local embeddings; Kun–Thom wreath witnesses (`fe7e9bf0c`, gk-n-ae-decoder): PASS

**Theorem 2.1 (local embeddings).**
- The joint law of `x(1)`, `x|_E` and `(x(fe))_(f,e)` under the product measure is determined by the
  coincidence pattern among `1`, `E` and `FE`. So `Φ` depends only on that pattern.
- On `S = {1} ∪ E ∪ F ∪ FE`, `eta(fe) = eta(f) eta(e)`, and `eta(1)^2 = eta(1)` forces `eta(1) = 1`.
- Injectivity preserves every equality among those points in both directions.
- The finitary-witness claim turns a deficit into a configuration with `Φ < log q`.

**Theorem 4.1 (Kun–Thom wreath witnesses).**
- *Step 1.* Products and inverses keep lamp supports inside the `π(K)`-orbits of the generators'
  sites.
- *Step 2.* A locally finite kernel under an amenable `π(K)` makes `K` amenable, hence sofic.
- *Step 3: residual finiteness when every stabilizer is closed.*
  - For `h o_i != h' o_i`, `h^-1 h'` lies outside `S_i`. Closedness gives a finite-index normal `Δ`
    with `h^-1 h'` outside `S_i Δ`, and `S_i Δ` is a subgroup because `Δ` is normal.
  - The map `h o_i -> h S_i Δ` is well defined, equivariant and injective on the finite support `T`.
  - `Δ` acts trivially on `π(K)/(S_i Δ)`, since `Δ S_i Δ = S_i Δ`.
  - Summing lamps over fibres (`B` is abelian) gives the homomorphism
    `V -> B^(Ō) ⋊ π(K)/Δ`. Because each fibre meets `T` at most once, it keeps `n != 0`.
  - The actor part is detected by residual finiteness of `π(K) <= G`.
- *Step 4.* `K` is residually finite, hence sofic, and carries no witness.

**Remarks.**
- The profinite topology of `π(K)` is finer than the topology inherited from `G`. So a closed
  `gΓg^-1` in `G` gives a closed stabilizer in `π(K)`, and non-closedness propagates up to `Γ`.
- `Rad(W) <= N_0` is prose-level, supported by Step 3 applied to `Γ̂`.
- Section 1's absences in Seward's papers were read from ar5iv extractions and are not verified
  here, as the author notes.
