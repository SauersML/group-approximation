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
