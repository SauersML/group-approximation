# Consistency sweep: Liu's nonhyperlinearity claim against the graph (2026-09-20)

Lane nh-record. This artifact supports `kun-thom-lamp-wreath-is-not-hyperlinear`.

**Question.** Does any node on main contradict either of these claims?
- **Liu's Theorem 1.2 / 6.7.** For every homomorphism π of a finitely generated Kazhdan group
  into a tracial matrix ultraproduct `M = prod_omega M_(d_n)`, the commutant
  `π(H)' ∩ M = [A_n]_omega` is internal.
- **Liu's Theorem 8.3.** Every homomorphism of the binary Kun--Thom wreath `W` into `M` kills
  `b = a_(gamma_0 t Gamma) a_(t Gamma)`.

This is a lane reading of statements. No proof here was re-checked.

**Method.** Grep `research/` on origin/main for ids containing `kt-`, `kun-thom-`, `thom-`,
`coset-wreath`, `hs-compression`, `kazhdan-commutant`, `hyperlin` and `internal`, plus
"not internal" and "non-internal". For each hit, read the opening statement and status. Take
the status markers from `research/FRONTIER.md`.

**Verdict: no contradiction found.** No established node claims either of these:
- a homomorphism of `W` into a tracial matrix ultraproduct that does not kill `b`;
- a homomorphism of a finitely generated Kazhdan group into such an ultraproduct with a
  non-internal commutant.

The nearest nodes fall into the six classes below.

## 1. Established conditionals and equivalences (consistent; Liu's claim decides them)

- **`kt-wreath-hyperlinear-iff-double-hyperlinear` (✓).** `W` hyperlinear ⇔ `G *_Gamma G`
  hyperlinear ⇔ RE/C of `L(Gamma) <= L(G)`. It is stated for every Theorem E pair, so it
  covers q = 2, r = d = 3. Liu's claim therefore settles all three negatively.
- **Further equivalences of the same kind:**
  - `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` (✓);
  - `kt-free-action-hyperlinear-iff-wreath-hyperlinear` (✓);
  - `kt-q2-double-hyperlinear-iff-relative-embeddable` (✓);
  - `kt-double-hyperlinear-iff-mixed-word-trace-selection` (✓);
  - `coset-wreath` equivalences (✓).
- **`coset-bernoulli-ce-refutes-relative-commutant-collapse` (✓).** CE of the crossed product
  implies no collapse. Liu proves collapse, so the crossed product is not CE: this is the
  contrapositive direction, with no conflict.
- **`kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`,
  `kt-wreath-hyperlinearity-forces-strong-one-boundedness`,
  `coset-wreath-hyperlinearity-forces-strong-one-boundedness`,
  `kt-double-hyperlinearity-requires-function-field-hecke-re` (all ✓).** Each has the form
  "hyperlinear ⇒ …". They become vacuous; no conflict.
- **`kazhdan-commutant-compression-stability-is-finitary` (✓).** Normalization in
  ultraproducts is equivalent to a dimension-uniform inequality. With Liu's Theorems 6.7 and
  7.4 this gives the finitary inequality.

## 2. Established statements about the canonical factor L(W) or crossed products (consistent)

These live in `L(W)`, `R ⋊ P_A`, or other tracial algebras that are not matrix ultraproducts.
There the Gamma-commutant is not normalized, which is exactly why those algebras do not embed.
- `kun-thom-wreath-factor-is-exact-nonnormalized-commutant`;
- `kt-full-actor-cocycle-loops-admit-exact-wreath-wall` ("CONNES EMBEDDABILITY IS NOT
  CLAIMED");
- `kt-canonical-afp-seam-has-no-internal-gauge-correction` and
  `kt-internal-c-seam-has-a-kazhdan-gap`. "Internal" there means inside `L(N)`, not Liu's
  internality.
- `kt-order-three-average-does-not-kill-the-pointed-martingale-wall` ("MATRIX APPROXIMABILITY
  REMAINS OPEN").

## 3. Established finite-window or partial-relation countermodels (consistent)

Each countermodel satisfies only a restricted relator set: one stabilizer row, a payload
annihilator orientation, finite quotients, or Heisenberg packets. None is a homomorphism of all
of `W`. Liu's Step 4 compactness uses the full presentation. Several nodes say so themselves;
e.g. the single-root node: "A positive transfer must use a finite family of Gamma-stabilizer
rows".
- `kt-single-root-mixed-return-has-exact-finite-countermodels`;
- `kt-payload-annihilator-mixed-return-has-profinite-countermodels`;
- `kt-two-compressor-irrep-flow-has-profinite-stationary-points`;
- `kt-a2-heisenberg-flat-wall-survives-one-more-compressor`;
- `kt-double-canonical-vertex-marginals-admit-large-amalgam-twists`. These are exact
  finite-dimensional representations of the double. They put no constraint on hyperlinearity
  of the double, because the D-characters need not converge to the regular one.
- `kt-steinberg-deleted-line-embeddings-have-scalar-commutants`. It exhibits scalar
  commutants, which are internal.
- `kun-thom-compression-survives-amenable-near-model`. It uses Kahl--Schneider charge models
  on `ell^2`, not tracial matrix ultraproducts.
- `agent-aggregate-escape-thom-countermodel-proof`. It concerns Thom's LEF Kazhdan central
  extension, a different group; its approximations are LEF regular representations.

## 4. Established statements about commutants (consistent with internality)

- **`leavitt-kazhdan-commutant-is-nonseparable` (✓).** It gives the nonseparable Kazhdan
  commutant and the dichotomy "`S' ∩ N` is separable iff purely atomic". An ultraproduct
  `[A_n]_omega` of finite-dimensional algebras is finite-dimensional or nonseparable, so
  internality agrees with both.
- **`kt-centralizer-normalization-hs` (OPEN).** Its recorded obstacle is that the commutant
  need not be atomic, so there are no component sizes. Internal commutants can be diffuse or
  factorial (e.g. `1 ⊗ M_(k_n)` for `σ ⊗ 1`), which is compatible. Liu's §6 supplies the
  missing finite structure.
- **`factorial-leavitt-models-have-external-corner-commutants` (✓, conditional).** If a
  canonical model of `H = L_(F_2)(1,2)^x` has a factorial global commutant, then its native
  corner commutant is not internal. This is not a contradiction. With Liu's Theorem 6.7, and
  since the corner `L = EL_3(R)` is finitely generated Kazhdan, it instead says: **no canonical
  model of H has a factorial global commutant.**

## 5. OPEN nodes Liu's claim would decide

The harvest of these consequences belongs to nh-harvest.
- **Refuted:**
  - `kt-canonical-hs-normalization-fails`: normalization in `prod_omega M_(d_n)` restricts to
    any separable Connes-embeddable `M` inside it;
  - `hs-compression-stability-fails-at-the-theorem-e-pair`;
  - `hyperlinear-wreath-model`;
  - `kt-double-reduced-cstar-is-mf`: reduced MF plus the established unique trace
    (`kt-q2-double-reduced-algebra-has-unique-trace`) gives a hyperlinear double, as in route
    `hyperlinear-nonsofic-from-kt-reduced-cstar-mf`;
  - `kun-thom-finitary-action-lifts-to-normalizer`: its route
    `kun-thom-finitary-normalizer-lift-proves-hyperlinear-wreath` yields a hyperlinear `W`.
- **Established:**
  - `hs-uniform-compression-stability-at-the-theorem-e-pair`;
  - the canonical instance of `kt-centralizer-normalization-hs`.
- **Routes into `non-hyperlinear-group`.** Several are superseded as the path to the root,
  though each may still carry value of its own:
  - `kt-pair-non-hyperlinear-commutant`;
  - `kt-pair-non-hyperlinear-rigidity`;
  - `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`;
  - `kt-wreath-from-relative-actor-exactification`;
  - `nonhyperlinear-from-kun-thom-finitary-normalizer-obstruction`.
- **Headline downstream item: the Leavitt unit group.**
  - `leavitt-channel-rounding-forces-nonhyperlinearity` (✓, conditional) says: "a positive
    answer to Alekseev--Thom Open Problem 6.2(a) for every canonical embedding of `H`
    supplies `(R)`". Its proof then runs two rounding uses: global H-heat component selection
    and native corner heat.
  - Liu's Proposition 3.1 shows that internality is equivalent to
    `||Phi_n - E_(A_n)||_(infinity->2) -> 0` for any maps `Phi_n` inducing `E_C` that are
    contractions in both norms. The heat maps `exp(-t_n A_n)` qualify (heat identification,
    (8b)).
  - So Theorem 6.7 appears to supply `(R)` for `H` and its corner `L`. Both are finitely
    generated Kazhdan (`leavitt-pair-vertex-rounding-is-nonhyperlinearity`: `Gamma ~= EL_3(R)
    ~= H` has a Kazhdan pair).
  - **Consequence if this holds:** `H` is not hyperlinear. By
    `boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el` (✓, unreviewed), neither is
    the boundary simple Kazhdan group `S_∂(d,k)` with char k = 2.
  - **To check directly:** that the artifact's (R) is exactly the ω-limit statement, with no
    extra uniformity over microstate sequences. Also check the component-selection step.
  - The status of these nodes is unchanged here.

## 6. A caution for the §5 referee (not a conflict)

**`kazhdan-group-rank-models-admit-no-expander-decomposition` (✓).** For irreducible
`F_2`-representations of `EL_3(F_2[t])` in the rank metric:
- there is no rounding modulus, and
- expander decompositions leak linearly.

Liu's §5 builds scalar-expanding decompositions for unitary normalized-HS models. The unitary
case has the Kazhdan spectral gap `a = κ²/(4h)` (Proposition 3.1), which has no rank-metric
analogue, so the categories differ. The §5 review should still confirm that every step uses
the unitary gap and not only the combinatorics.
