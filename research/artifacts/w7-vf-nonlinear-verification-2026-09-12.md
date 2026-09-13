# Wave-7 nonlinear-side verification (lane w7-vf-nonlinear)

Lane `w7-vf-nonlinear`, 2026-09-12. This lane takes over from `w3-vf-nonlinear`, whose verdicts are Sections 1–30 of
`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`.
- **Content.** Independent re-derivations of landings from `w7-two-patch-rigid` and `w7-marker-nonlinear`.
- **Format.** Each section states the claims checked, the verdict, and any scope correction.
- **Routes.** A verdict line citing this artifact is added to each proof route checked.
- **Tools.** Everything was done by hand. The lane scripts were read and matched byte for byte against the landed
  copies, but not run.

**Already verified.** RULES queue line 115 is `ternary-two-patch-seed-rule-is-never-injective`. It passed in w3
Section 28 (73bc73756f), and its route was restored at efd28946a. Nothing further is needed.

## 1. The rigid two-patch seed, uniform filters and the class II lifting (w7-two-patch-rigid, cba91f8d1, bdc652fc1)

**Claim `rigid-two-patch-seed-rule-is-never-injective` (OPEN, held for this verdict). PASS with notes. The
candidate proof in artifact Sections 1–4 is correct, and the claim is established by the new route
`rigid-two-patch-seed-never-injective-proof`.**

The rule is `mu_3(y) = y_1 + y_a - y_b + [y = p] + [y = q]` over `F_3`, with `p = (0,0,2)` and `q = (1,2,0)`.

**Values.** `lambda = y_1 + y_a - y_b` is balanced.
- **Patch `p`.** `lambda(p) = 1` becomes `mu_3(p) = 2`.
- **Patch `q`.** `lambda(q) = 0` becomes `mu_3(q) = 1`.
- **Counts.** So the counts are `8, 9, 10`.
- **Diagonal.** The diagonal is the identity.

**Blind pairs.** Each context contains at most one patch, since `p` and `q` differ at every coordinate. Recomputed
columns:
- **Coordinate `1`.**
  - Context `(0,2)` gives values `2, 2, 0`, so `{0,1}` is blind.
  - Context `(2,0)` gives values `2, 1, 1`, so `{1,2}` is blind.
- **Coordinate `a`.**
  - Context `(0,2)` gives `2, 2, 0`, so `{0,1}` is blind.
  - Context `(1,0)` gives `1, 2, 1`, so `{0,2}` is blind.
- **Coordinate `b`.**
  - Context `(0,0)` gives `0, 2, 2`, so `{1,2}` is blind.
  - Context `(1,2)` gives `1, 2, 1`, so `{0,2}` is blind.
- **Rigid.** Every pair is blind at exactly two coordinates.

**Window tables (Section 1). Correct.**
- **Touched windows.** The touched windows are `S M^-1` with `M = {1, a, b}`, which gives the five listed windows
  for each move. The eleven words of each move are the sites of those windows.
- **Recomputed.** All 15 rows were recomputed. Patched entries:
  - **`T_ab`.** `q` before at `a`. `p` after at `ab^-1`, and before at `b` and `ba^-1`.
  - **`T_1a`.** `q` after at `a^-1`, and before at `b^-1` and `a`. `p` after at `ab^-1`.
  - **`T_1b`.** `q` after at `a^-1`, and before at `b^-1`. `p` after at `b` and `ba^-1`.
- **Unpatched entries.** No other entry is a patch. In particular the window at `1` reads `(*, 1, 0) -> (*, 2, 1)`,
  `(0, 1, *) -> (2, 2, *)` and `(0, *, 1) -> (2, *, 0)`, and none of these can equal `p` or `q`.

**Realization.** A move realizes in `H` exactly when no conflicting coincidence holds.
- **Conflicts.** A conflict is a changed word coinciding with any other word, or two unchanged words with different
  values coinciding.
- **Star words.** A `*` word conflicts only with changed words: if it coincides with unchanged words, give it their
  common value.
- **Consistency.** Without a conflict, `x` and `x'` are well defined on `H`. The touched windows in `H` are images of
  the listed windows, and the untouched windows read equal values.

**Coincidence tables (Section 2). Correct, and complete.** All 55 pairs of each move were enumerated.
- **`T_ab`: 34 conflicting pairs.** 19 involve a changed site, and 15 are value-2 words `a^2, b^2, ba^-1 b` against
  value-0 words `ab, ab^-1, ab^-1 a, ba, ba^-1`.
- **`T_1a`: 39 conflicting pairs.** 19 involve a changed site. The unchanged pairs are 8 of value 1 against 0, 4 of
  1 against 2, and 8 of 0 against 2.
- **`T_1b`: 40 conflicting pairs.** 19 involve a changed site. The unchanged pairs are 6 of value 1 against 0, 6 of
  1 against 2, and 9 of 0 against 2.
- **Relators.** After cyclic reduction and inversion, the relator sets are exactly the artifact's lists, including
  the sources of the nonamenable relators:
  - `c^2` from `a = ba^-1 b` and `b = ab^-1 a`, and `c^3` from `ab^-1 a = ba^-1 b`;
  - `a^2` from `1 = a^2` and `a = a^-1`, and `a^3` from `a^-1 = a^2`;
  - `b^2` from `1 = b^2`, `b = b^-1` and `ba = b^-1 a`, and `b^3` from `b^-1 = b^2`;
  - `c^2` in `T_1a` and `T_1b` from `a^-1 b = b^-1 a`.
- **Classification.**
  - **`ab^-2 ab^-1`.** With `x = ab^-1` the relation reads `x b^-1 x = 1`, so `b = x^2` and `a = x^3`.
  - **`ba^-1 ba^-1 b`.** With `x = ba^-1` it gives `b = x^-2` and `a = x^-3`.
  - **Klein bottle, twisted form.** `bab^-1 a`, `a^-1 bab` and `aba^-1 b` each have the form `s t s^-1 = t^-1`.
  - **Klein bottle, square form.** `a^2 b^-2` gives `<a, b | a^2 = b^2>`, the fundamental group of
    `RP^2 # RP^2`, which is the Klein bottle group.
  - **Nonamenable relators.** They give `Z * Z/2` or `Z * Z/3`.

**Move `C` (Section 3). Correct.**
- **Windows.** With `c^2 = 1`: `b = ac`, `w = ab^-1 = ba^-1 = aca^-1`, `wa = ac = b` and `wb = acac·c = a`. So the
  window at `w` reads `(w, b, a)`.
- **Eight words.** Their normal forms in `Z * Z/2` are distinct.
- **Recomputed windows.**
  - `a`: `p -> (1,0,2)`, value 2.
  - `b`: `q -> (2,2,0)`, value 1.
  - `1`: `* - 1`.
  - `w`: `* + 1`.
- **Conflicts.** There are 17 conflicting pairs: 7 at `a`, 6 at `b`, and 4 between `{a^2, b^2}` and `{ab, ba}`.
  - Each one reduces, using `c^2 = 1`, to `a = 1`, `c = 1` or `a = c`.
  - The four unchanged pairs all force `c = 1`.
  - `a = c` gives `b = c^2 = 1`.

**Theorem 4.1. Correct.**
- **Coset extension.** A collision over `H` extends to `G` by the zero configuration off `H`. So injectivity over
  `G` restricts to `H`.
- **Amenable `H`.** Injective, then pre-injective, then surjective by the Garden of Eden theorem, then bijective,
  then measure preserving. `bijective-ca-preserve-uniform-bernoulli-measure` holds over every group. The marginal at
  `1` is `mu_3` of a uniform triple, because `1, a, b` are distinct, and `8, 9, 10` is not uniform.
- **Nonamenable `H`.** Only the nonamenable relators can hold.
  - **`T_ab`.** It forces `c^2` or `c^3`.
  - **`T_1a`.** It forces `a^2`, `a^3` or `c^2`.
  - **`T_1b`.** It forces `b^2`, `b^3` or `c^2`.
  - **Split.** Either `c^2 = 1` and Move `C` realizes, or `a^k = b^m = c^3 = 1`.
- **Von Dyck step.** Put `x = a^-1` and `y = b`, so `xy = c`. The order of `D(k, m, 3)` is
  `2 / (1/k + 1/m + 1/3 - 1)`, which gives 6 for `(2,2)` and 12 for `(2,3)` and `(3,2)`. `(3,3,3)` is Euclidean.
  All are amenable, so `H` is amenable, a contradiction.

**Lemma 5.1 and Corollaries 5.2–5.3. Correct.**
- **Intertwining.** `tau_H(x∘pi)(h) = mu(x(pi h), x(pi(h) pi(a)), x(pi(h) pi(b))) = tau_Q(x)(pi h)`, and `x -> x∘pi`
  is injective.
- **Restrictions of `mu_3`.** `mu_3(y,y,z) = 2y - z + [(y,z) = (0,2)]`, while `mu_3(y,z,y) = z` and `mu_3(y,z,z) = y`.
- **`mu' = x_1 + x_a - x_b + [(0,1,0)] - [(1,2,2)]`.**
  - **Counts.** `10, 7, 10`.
  - **Restrictions.** `mu'(y,y,z) = 2y - z`, `mu'(y,z,y) = z + [(y,z) = (0,1)]` and
    `mu'(y,z,z) = y - [(y,z) = (1,2)]`.
  - **Filter.** The only allowed patterns in an amenable quotient are `pi(a) = 1` and the diagonal. So `a` dies there.
  - **Blind pairs.** Recomputed from both contexts of each coordinate: `{0,1}` at `1` (contexts `(1,0)` and
    `(2,2)`), `{1,2}` at `a` (`(0,0)` and `(1,2)`), and `{0,2}` at `b` (`(0,1)` and `(1,2)`).
- **Unit step.** Restrict the inverse to its `H`-component. In `F_3[t]/(t^n - 1)`, `2 - t = -(1 + t)` is a unit iff
  `t + 1` does not divide `t^n - 1`, iff `n` is odd (`n = 1` included). `2 - t` is not a unit of `F_3[t, t^-1]`.

**Section 6. Lifting and scale bounds correct; census counts not re-counted.**
- **Lifting.** Suppose `pi` is injective on the ball `B_R` of `F(a, b)`. Changed sites in `B_(R-2)` then have unique
  lifts, their touched windows lie in `B_(R-1)`, and window sites in `B_R`. So the outputs pull back, and a finite
  collision over free memory results.
- **Scale.** An inverse supported in `B_r` lifts to `F_3[F(a, b)]` with product supported in `B_(r+1)`. If `pi` is
  injective on `B_(r+1)`, the coefficients do not merge, and a one-sided inverse of `1 + a - b` would exist in a
  domain with trivial units. Non-injectivity on `B_(r+1)` gives a relator of length at most `2r + 2`.
- **Class II equals the Proposition 10 hypothesis, on paper.** Take a coefficient class `(1,1,-1)` and a rule with
  no pair blind at two coordinates.
  - **One patch.** A patch alone in a context makes that column a bijection shifted at one entry, so exactly one
    pair is identified there.
  - **Patches differing at two or more coordinates.** At every coordinate `p` and `q` lie in different contexts,
    so every coordinate has a blind pair.
  - **Patches differing at exactly one coordinate `m`.**
    - If `t_p != t_q`, each of the other two coordinates carries two distinct pairs. Four pairs out of three force a
      double.
    - If `t_p = t_q = t != 0`, the shared column at `m` has entries `c_m p_m + t`, `c_m q_m + t` and `c_m r`. These
      collide, and they are not constant.
  - **Conclusion.** So each coordinate has at least one blind pair, hence exactly one, all distinct. Each insensitive
    context identifies exactly that pair and is injective otherwise.
  - **Class `(1,1,0)`.** Coordinate `b` is blind for all pairs, so no class II rule arises.
  - **Converse.** It is immediate.
- **Not re-counted.** The counts 855, 126, 42 and 30 and the `I_3`, `I_1`, `I_0` splits are from the scripts, which
  were not run. No decision uses them.

**Notes (no change to any statement).**
1. The artifact (Sections 0 and 7) names w3-vf-nonlinear as the verifier. This lane took over the item.
2. "Why two sites" in Section 1 is motivation. Theorem 4.1 does not use it.

**Subsumption scan.**
- **Scope.** ESTABLISHED claims whose content matches Garden of Eden or pre-injectivity together with ternary or
  patch vocabulary.
- **Hits.** Five hits, none subsuming:
  - `single-patch-…`, `distinct-symbol-patch-…` and `constant-background-kills-…` are one-patch results;
  - `pair-distinct-…` needs no pair blind twice;
  - `ternary-two-patch-seed-…` is `mu_2`, which is not rigid. Rigidity is invariant under the census symmetries, so
    `mu_3` is not an image of `mu_2`.
- **Literal scans.** Scans for `0,0,2`, "von Dyck", "triangle group", "blind at" and "two-site move" hit no
  ESTABLISHED node.

**Nodes updated.**
- **Claim.** The header is ESTABLISHED by `rigid-two-patch-seed-never-injective-proof`, which is new, and its
  Attempts verification line is updated.
- **Parent.** In `two-patch-ternary-rules-reduce-to-linear-strictness`, "awaiting re-derivation" and "If verified"
  are replaced.
- **Unit case.** `unit-case-pair-distinct-two-patch-rules-are-not-injective` stays OPEN, with a verification note
  on its host-filter entry.

## 2. Nonlinear ancilla words for the integer marker (w7-marker-nonlinear, 890beaaf0)

**Claims `data-exact-read-ancilla-words-realize-only-translations` and
`marker-realizations-reduce-to-two-linear-data-writes` (OPEN, held for this verdict). PASS with notes. Both are
established by their landed routes, to which the verdict lines are added.**
- **Re-derived.** Artifact Proposition 2.1, Theorem 3.1, Corollary 3.2, Lemma 4.1 and Lemma 6.1.
- **Not re-derived.** The periodic sign and gyration table of Section 5 (partial).

**Proposition 2.1. Correct.** Track pair `(x-track, y_1)`:
- the first `X` gives `(x + y_1, y_1)`;
- the next gate gives `(x + y_1, x)`;
- `V'` gives `(x + y_1, tau x)`;
- the next gate gives `(x + y_1, y_1 + m(x))`, since `tau x + x = m(x)`;
- the second `X` gives `(tau x, y_1 + m(x))`;
- the last gate gives `(tau x, y_1)`, using `m(tau x) = m(x)` (Corollary 1.2 of the residue artifact).

The last gate is the shear `y_1 <- y_1 + m(x-track)`, which is in `𝒢`. The only data writes are the two `X`.

**Theorem 3.1. Correct.**
- **Step 1.** Induction. Data writes fix `a`. Ancilla-only writes are fixed bijections. A `d`-reading write at an
  exact time is, for fixed `x`, the shear `a_T <- a_T + H(phi(x), ·)`.
- **Step 2.** `G(a_(t-1)(x, ·))` is `x`-only and its argument is onto, so `G` is constant.
- **Step 3.**
  - **First gate.** `g_s` must be a data write, because an ancilla write keeps `d` exact.
  - **Ancilla evolution.** `g_(s+1), …, g_e` read dirty states, so none reads `d`, and `a_t = V_t(u)` with
    `u = a_(s-1)(x, y)`.
  - **Constant change.** `Λ(u) = d_e - d_(s-1)` is `x`-only with `u` onto, so `Λ` is constant.
  - **Its value.** A constant `Z`-equivariant value is `0^Z` or `1^Z`.
- **Step 4.** `d_0 = x` and `d_n = F(x)` are exact, so every data write is an exact-phase write or lies in one dirty
  interval.
- **"`tau x id` is not such a word."** This needs only that `tau` is not a translation. `tau` is not affine, as
  already used by `linearly-dirty-ancilla-words-realize-only-affine-data-maps` (w3 Section 30).

**Corollary 3.2. Correct.** The first item is the contrapositive of Theorem 3.1. The second is the linear-dirt
theorem: if every nonlinear read value is `x`-only, the data map is affine.

**Lemma 4.1. Correct.**
- **Before `t`.** The data is exact, so Step 1 holds to `t - 1`.
- **Non-constant `G`.** `G` is not constant, and equivariance moves a differing cell to cell `i`.
- **Pull back.** Since `a_(t-1)(x, ·)` is onto, the differing ancilla states pull back to `y` and `y'`.

**Lemma 6.1. Correct.**
- **Measure.** The state map is a bijective automaton over `Z`, so it preserves the uniform Bernoulli measure
  (`bijective-ca-preserve-uniform-bernoulli-measure`).
- **Independence.** Disjoint track sets are independent.
- **Conclusion.** A function of two independent coordinates is almost surely constant, but `x` is uniform.

**Notes.**
1. **Data-track degree.** Proposition 2.1's second consequence says the data track "is `x` or `x + y_1`". It is
   also `tau x` after the second `X`. The degree bound of at most 1 is unaffected.
2. **Sitewise permutations.** The claim node lists sitewise permutations among the gates. They are words in
   shears, because Hamming-adjacent transpositions are shears with indicator `G` and generate the symmetric group.
   The hypothesis of Theorem 3.1 applies to the expanded word.
3. **Routes.** Both routes have `requires: []`.
   - Theorem 3.1 is self-contained.
   - Proposition 2.1 uses Corollary 1.2 of `marker-stable-formalization-residue-2026-09-12.md`, revised after w3
     Section 27. That is an artifact-level input.

**Subsumption scan.**
- **Scope.** ESTABLISHED claims containing "ancilla" or "track shear".
- **Hits.** 13 hits. Three concern marker or ancilla words, and none subsumes these claims:
  - `linearly-dirty-…` is an incomparable class, already in `distinct_from`;
  - `marker-flip-cells-avoid-all-marker-control-windows` is flip-cell geometry;
  - `z3-equivariant-permutations-are-stably-realizable` is a finite permutation, not the marker.
- **Others.** The remaining hits are tracial and BCS nodes.

**Nodes updated.** Both claim headers are set to ESTABLISHED by their routes, and both routes carry the verdict
line. Hub `injective-binary-automata-are-stably-formalizable` stays OPEN.

## 3. Queue status at the wrap-up (origin/main 39971c4c)

- **w7-radu-gadget-b4 (86e9c2b3e).** `radu-lattice-radius-two-pairs-force-the-mark-into-the-radical` is held OPEN,
  with route `radu-lattice-radius-two-mark-forcing-proof` held in artifact Section 7. **Not re-derived here;
  pending.**
- **w7-2v-mixed-support (77aed2b4f, afb6eb112, 9a375e7cd).** The 2V obstruction-state profile was verified by
  w3-vf-nonlinear (83970f525, 90e7a86f9). This lane did not duplicate it.
- **w7-two-patch-census (6b0ad0644).** `rigid-unbalanced-two-patch-rules-beyond-class-ii-not-injective` is held
  OPEN, and verification was requested from this lane. It is pending at this landing.
- **w7-two-patch-unit.** No landing on main as of 39971c4c.
