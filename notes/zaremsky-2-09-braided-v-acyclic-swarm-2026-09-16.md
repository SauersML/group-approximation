# Zaremsky 2.9 (is braided V acyclic?): swarm attack, 2026-09-16

- **Lane:** swarm-zaremsky-2-09-braided-v-acycli.
- **Target:** `zaremsky-2-09-braided-v-acyclic`.
- **Hole locked and worked:** `cantor-power-function-modules-are-v-acyclic`, which says
  `H_p(V; C(C^j, Z)) = 0` for all `p >= 0` and `j >= 1`.

**Outcome.** I found a proof of the hole, through a germ groupoid comparison. With the
existing reduction route `braided-thompson-group-bv-is-acyclic-from-cantor-modules`,
it makes `bV` integrally acyclic, so the graph computes the answer YES to Zaremsky 2.9.
Nothing has been reviewed.

The full proof is in
`research/artifacts/cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16.md`.

## 1. Setup

- `C = {0,1}^N`, and `V` acts diagonally on `C^m`.
- `Conf_m(C) ⊆ C^m` is the open set of tuples of distinct points. `C_c(X, Z)` is the
  group of compactly supported locally constant integer functions.
- The earlier lane `z2-09-bv-acyclic` (2026-09-13) proved the following, over `Q`, in
  parts 1–3 of `zp-braided-v-rational-acyclicity-2026-09-13`:
  - for `K = ker(bV → V)` and `q >= 1`,
    `H_q(K) ≅ ⊕_{m=q+1}^{2q} C_c(Conf_m(C)) ⊗_{Σ_m} W_{m,q}`;
  - these modules are V-acyclic.
- Every step of that argument is integral except Lemma C3, that `C(C^j)` is
  V-acyclic. Over `Q`, C3 came from Palmer–Wu acyclicity of the labelled Thompson
  groups and a splitting of the Lyndon–Hochschild–Serre spectral sequence.

## 2. What was proved

**Theorem 1.** `H_p(V; C_c(Conf_m(C), Z)) = 0` for all `p >= 0` and `m >= 1`.

Proof in five steps. Put `X = Conf_m(C)`.

1. **Group to groupoid.** `H_*(V; C_c(X)) = H_*(X ⋊ V)` (Matui 2012). I checked this at
   chain level: the nerve of `X ⋊ V` is `Γ^n × X`, and the faces reproduce the
   inhomogeneous bar complex.
2. **Germ groupoid.** The germ groupoid `𝒱` of `V` on `C` is isomorphic to the full
   2-shift groupoid `G_2`. For `m >= 2`, `X` is an open `𝒱^m`-full subset of `C^m`.
   So Matui's reduction theorem (2012, Theorem 3.6(2) with Proposition 3.5(2)) gives
   `H_*(𝒱^m|X) = H_*(G_2^m)`. That group is `0` by Künneth (Matui 2016) and
   `H_*(G_2) = 0`.
3. **Comparison homomorphism.** `φ : X ⋊ V → 𝒱^m|X`, `(g, x) ↦ ([g]_{x_i})_i`, is an
   étale homomorphism. Its Crainic–Moerdijk comma groupoids `x/φ` behave as follows.
   - They are discrete (source fibres of an étale groupoid).
   - They are connected: `V` realizes any tuple of germs between two configurations,
     because `V` has no order constraints.
   - Their isotropy is `K_x = {h : h = id near each x_i}`. This is a directed union of
     subgroups isomorphic to `V`, so it is acyclic by Szymik–Wahl.
4. **Collapse.** In the Crainic–Moerdijk spectral sequence
   `H_p(𝒢; L_qφ_!Z) ⇒ H_{p+q}(X ⋊ V)`:
   - `L_qφ_!Z = 0` for `q >= 1`, by stalks;
   - `L_0φ_!Z = Z`, by augmentation and connectedness.
   It collapses, so `H_*(X ⋊ V) = H_*(𝒱^m|X) = 0`.
5. **Corollary 2** (the hole). `C(C^j, Z)` is V-acyclic, by strong induction on `j`:
   - `0 → C_c(Conf_j) → C(C^j) → C(D) → 0`, where `D` is the fat diagonal;
   - `D` is assembled from strata `≅ C^i` with `i < j`, using the Mayer–Vietoris
     Lemmas C1, C2 and C4 of part 3.

**Consequence.** Take the existing route `braided-thompson-group-bv-is-acyclic-from-cantor-modules`,
which requires the hole and `thompson-v-is-integrally-acyclic`. Then
`braided-thompson-group-bv-is-acyclic`, and so `zaremsky-2-09-by-yes`. Theorem 1 feeds
the configuration modules directly, and the hole is only the graph's bookkeeping.

**Graph nodes written.**
- Claims:
  - `crainic-moerdijk-groupoid-leray-spectral-sequence` (import);
  - `matui-groupoid-homology-transformation-and-reduction` (import);
  - `cantor-configuration-function-modules-are-v-acyclic`.
- Routes:
  - `crainic-moerdijk-leray-spectral-sequence-citation`, `requires: []`, with TeX
    quotes;
  - `matui-transformation-and-reduction-citation`, `requires: []`, with TeX quotes and
    the chain-level check;
  - `cantor-configuration-modules-v-acyclic-germ-proof`;
  - `cantor-power-modules-v-acyclic-from-configurations`, into the hole.

## 3. Approaches tried, and where each dies

1. **Splitting the LHS spectral sequence of `V(Z^j) = C(C, Z^j) ⋊ V`** (the route of
   part 2). `C(C^j, Z)` is the multilinear summand of row `j`. Only integer scalings
   of `Z^j` are available to separate summands. A differential from a summand `ν` to
   a summand `μ` is killed only up to the gcd of `x^ν − x^μ` over `x ∈ Z`, and that
   gcd can be 2 (`x^2 − x`). So this route cannot decide 2-torsion without a
   chain-level formality statement. Dead as a direct method.
2. **Mod-ℓ coefficients.** The units of `F_ℓ` separate degrees only modulo `ℓ − 1`, and
   do nothing for `ℓ = 2`, which is exactly the crux. Dead.
3. **Xin Li's topological full group theorem** (arXiv:2209.08087), applied to
   `C^j ⋊ V`. It needs a full group, not group homology with a module of functions on
   a non-minimal space, so it does not apply directly.
4. **Germ groupoid comparison (this note).** It works. The key observation: once a
   configuration is fixed, the only information the transformation groupoid carries
   beyond the germ groupoid is the germ-trivial stabilizer `K_x`, and `K_x` is a
   directed union of copies of `V`. Section 6 of the artifact records a toy example
   where the stabilizer is not acyclic and the collapse fails, so the argument uses
   the acyclicity.

## 4. Points a referee should attack first

1. **Proposition 3.4(iii) of the artifact.** `L_0φ_!Z ≅ Z` as a `𝒢`-sheaf.
   - The argument: `B_0(φ; Z) = s_!Z`, summation along `s` is a sheaf map, it kills
     `d_0 − d_1`, and on stalks it is the augmentation `Z[π_0(x/φ)] → Z`, which is
     bijective by connectedness.
   - Equivariance: `γ^*` maps basis elements to basis elements.
2. **Discreteness of `x/φ`**, including its arrow and nerve spaces with the fibred
   product topology. This is what lets Crainic–Moerdijk 3.5(2) turn stalk homology into
   `H_*(K_x)`.
3. **Crainic–Moerdijk homology with constant coefficients `Z` equals Matui's.** Every
   sheaf on a zero-dimensional locally compact Hausdorff space is c-soft, and 3.1
   gives the same bar complex `C_c(G^(n), Z)`.
4. **Integrality of Step A** (part 1 of the 2026-09-13 lane). It uses torsion-freeness
   of `H_*(Conf_n(R^2); Z)` and the support decomposition. It was written by an earlier
   lane and not re-derived here.

## 5. Sanity checks done

- **Degree 0, `m = 1`.** Coinvariants of `C(C, Z)` vanish (`f = 2f`), which agrees with
  Theorem 1.
- **Palmer–Wu.** `V(Z)` is acyclic, and its LHS terms `E²_{0,1}` and `E²_{1,1}` are
  untouched by differentials. So `H_0` and `H_1` of `V` with coefficients `C(C, Z)`
  vanish, which agrees with Theorem 1.
- **Rational case.** Theorem 1 tensored with `Q` is Lemma C5 of part 3, which an
  earlier lane proved by a different route.

## 6. Literature (dated)

**Answer search.** No paper or preprint was found that answers Zaremsky 2.9 or
computes `H_*(bV; Z)` beyond degree 1.
- arXiv API searches on 2026-09-16, sorted by submission date:
  - `all:"braided Thompson" AND all:acyclic`: no hits;
  - `all:"braided Thompson"`: latest hit 2503.11594 (2025-03-14), none about homology;
  - `all:acyclic AND all:Thompson AND all:groups`: latest hits 2603.24687 (2026-03-25)
    and 2510.16879 (2025-10-19);
  - `all:"groupoid homology" AND all:Thompson`;
  - `all:"topological full group" AND all:homology`: latest hit 2607.00577
    (2026-07-01).
- Web searches on the same day.
- X. Wu's paper list (wuxiaolei.org/papers, fetched 2026-09-16).

**Sources read.**
- **Zaremsky, open problems list.** Version of July 12, 2026, as recorded in the root
  node. The PDF fetch on 2026-09-16 returned binary content, so the version was not
  re-verified.
- **M. Crainic, I. Moerdijk,** *A homology theory for étale groupoids*, J. reine angew.
  Math. 521 (2000). arXiv:math/9905011v1 (1999-05-03). TeX source read 2026-09-16:
  1.8, 3.1, 3.4, 3.5, 3.7, 4.1–4.6.
- **H. Matui,** *Homology and topological full groups of étale groupoids on totally
  disconnected spaces*, Proc. LMS 104 (2012). arXiv:0909.1624 (2009-09-09). TeX read
  2026-09-16: Definitions 2.1 and 3.1, the paragraph after Remark 3.2, Proposition 3.5,
  Theorem 3.6.
- **H. Matui,** *Étale groupoids arising from products of shifts of finite type*, Adv.
  Math. 303 (2016). arXiv:1512.01724 (2015-12-06), Theorem `Kunneth`. Already
  imported in the graph.
- **H. Matui,** J. reine angew. Math. 705 (2015). arXiv:1210.5800. `H_*(G_2) = 0`,
  already imported in the graph.
- **M. Szymik, N. Wahl,** arXiv:1411.5035 (2014-11-18). `V` is acyclic, already
  imported.
- **M. Palmer, X. Wu,** *Embedding groups into acyclic groups*, arXiv:2510.16879v1
  (2025-10-19). Labelled Thompson groups are acyclic, via Li's theorem and Matui's
  Künneth formula. It does not treat braided groups or non-trivial coefficients.
- **F. Fournier-Facio, X. Wu, M. Zaremsky,** *Abstract twisted Brin–Thompson groups*,
  arXiv:2603.24687 (2026-03-25). Abstract read; it concerns bounded acyclicity, not
  braided V.
- **A. Miller, B. Steinberg,** *Homology and K-theory for self-similar actions of groups
  and groupoids*, arXiv:2409.02359 (2024-09-04). Title and metadata only; not used.
- **X. Li,** *Ample groupoids, topological full groups, algebraic K-theory spectra and
  infinite loop spaces*, arXiv:2209.08087 (2022-09-16). Abstract only; not used in the
  proof.
- **R. Skipper, X. Wu,** *Homological stability for the ribbon Higman–Thompson groups*,
  arXiv:2106.08751, Algebr. Geom. Topol. 25 (2025). Search listing only. It hopes to
  shed light on whether braided V is acyclic, and gives no stable computation.

## Referee (2026-09-16)

**Scope.** One adversarial referee (an agent, not a human expert) read all nine solver
files in full, plus these nodes:
- the root, `zaremsky-2-09-by-yes` and the hole;
- `braided-thompson-group-bv-is-acyclic-from-cantor-modules`;
- `thompson-v-is-integrally-acyclic`;
- the Matui Künneth import;
- parts 1 and 3 of `zp-braided-v-rational-acyclicity-2026-09-13`.

`git status` shows no unlisted solver files. `bin/cairn search --similar` found no
duplicates. Two nodes overlap in theme but prove different results:
`li-derived-full-group-homology-is-k-theory-cover` and
`matui-sft-groupoid-homology-is-k-theory`. No `requires: []` route points into the root.

**Citations checked against independently fetched TeX.**
- **Crainic–Moerdijk.** arXiv:math/9905011v1 e-print. Every quote in
  `crainic-moerdijk-leray-spectral-sequence-citation` matches the source verbatim:
  3.1, 3.5(2), 3.7(2), 4.1, 4.2 (including the stalk formula for `B_n`), Proposition 4.3,
  Theorem 4.4 and 4.5(2). I also read the proof of Corollary 4.6, which uses
  `L_0φ_! φ^* A ≅ A` in the same way the artifact does.
- **Matui 2012.** arXiv:0909.1624 e-print, `htfgeg.tex`. The quotes and the cited line
  numbers 221, 229, 266, 421, 433, 443, 569, 588 and 626 match: the étale convention,
  fullness and reduction, Definitions 2.1 and 3.1, the paragraph after Remark 3.2,
  Definition 3.4, Proposition 3.5 and Theorem 3.6(2). Theorem 3.6(2) needs only an étale
  `G`, an open `G`-full `F`, and a σ-compact totally disconnected `G^(0)`.
- **Problem status.** The Zaremsky PDF (fetched 2026-09-16, text extracted by stream
  decompression) is dated July 12, 2026. It still lists "9. Is braided V acyclic?" with
  no update. An arXiv API recheck found no resolution. That search was bounded: web
  search was unavailable to the referee.

**Mathematics checked.**
1. **Lemma 1.1, `𝒱 ≅ G_2`.** Germs of `V` are locally prefix replacements, and the map
   `(g(y), |v| − |u|, y)` is well defined and bijective. Surjectivity holds after
   shrinking to proper cones.
2. **Lemma 2.1, fullness.** For `m >= 2`, prefix the coordinates of any tuple with
   distinct equal-length words. For `m = 1` fullness is trivial.
3. **`φ` is étale.** `φ_0 = id` and `s∘φ_1 = s`, so `φ_1` is a local homeomorphism.
   `β_0 = s` is étale, and `B_0 = s_!Z`.
4. **Lemma 3.3, the comma groupoids.**
   - Objects of `x/φ` are `𝒢`-arrows with source `x`, which form a discrete fibre.
     Arrows are elements `(h, y)` with fixed `y`, which form a discrete set because `V` is
     discrete. So the nerve is discrete, and Crainic–Moerdijk 3.5(2) applies.
   - Connectedness is Lemma 3.1. A tuple of germs between two configurations is realized
     on small disjoint cones and extended to an element of `V`, after shrinking so that
     both complements are nonempty.
   - The isotropy is `K_x`. It is the directed union of the groups `V_U` of elements
     supported off a proper clopen neighbourhood `U` of the `x_i`. Each `V_U ≅ V`, so it
     is acyclic. Homology commutes with directed colimits.
5. **Proposition 3.4, collapse.**
   - The stalks of `L_q` vanish for `q >= 1`.
   - The counit `s_!Z → Z` kills the image of `B_1`. It is equivariant, because
     `γ ∈ 𝒢` permutes basis elements `(y, g) ↦ (y, gγ^{-1})`. It is bijective on stalks
     by connectedness. So `L_0φ_!Z ≅ Z` as a `𝒢`-sheaf.
   - The spectral sequence is concentrated on the row `q = 0`, so
     `H_*(X ⋊ V) ≅ H_*(𝒢; Z) = 0`.
   - Toy check: for discrete `X` the argument reduces to Shapiro's lemma.
6. **Corollary 2.** The strong induction over the fat-diagonal strata is correct
   integrally. C1, C2 and C4 of part 3 are exact-sequence arguments, and the strata
   `Δ_E ≅ C^i` have `i < j`.
7. **Composition to the root.** Step A of part 1 is integral: Cohen's torsion-free
   `e_2` basis, the support decomposition, and a free `Σ_m` action on injections.
   C6 is integral once C3 is. With the hole, the committed route
   `braided-thompson-group-bv-is-acyclic-from-cantor-modules` gives integral acyclicity
   of `bV`, hence `zaremsky-2-09-by-yes`.

No gap, circularity or misread definition was found.

**Changes made.** In `research/matui-transformation-and-reduction-citation.md`:
- recorded that the e-print filename is `htfgeg.tex`, and that the referee confirmed the
  quotes and line numbers;
- replaced "needs neither countability of Γ" with an accurate statement. The chain-level
  check does not use countability, but Matui's Definition 2.1 assumes a countable
  discrete group, and `V` is countable.

No mathematical content was changed.

**Verdict: sound; landed with minor fixes.** The certificate still depends on imports:
- Crainic–Moerdijk Theorem 4.4 and Proposition 4.3;
- Matui 2012 Theorem 3.6(2);
- Matui 2016 Künneth;
- `H_*(G_2) = 0`;
- Szymik–Wahl;
- Step A from the 2026-09-13 lane.

This result answers a listed open problem. Only one agent referee checked it, so it
should get human expert review before anyone announces it.

## Independent referee panel (2026-09-16)

Three independent agent referees each examined the certificate through one lens.
An adjudicator then checked every reported gap against the proof text and the
source TeX and PDFs. The sources are stored under
`experiments/bv-acyclic-panel-2026-09-16/`.

**Lens verdicts.**

1. **Crainic–Moerdijk comparison** (Lemma 3.3, Proposition 3.4). *Sound with
   minor gaps.* The use of the Leray spectral sequence and the stalk formula
   was accepted. The citations and side-conditions needed tightening.
2. **Germ groupoid** (the identification of the germ groupoid with `G_2`, and
   the imports). *Sound with minor gaps.*
3. **Step A reduction** (part 1 Step A, the part 3 assembly, the route to
   `zaremsky-2-09-by-yes`). *Serious gap*, confirmed and repaired.

**Confirmed serious gap (lens 3), repaired.** Part 1, A3–A5, claimed two things:

- cabling acts on the Gerstenhaber basis by
  `w[i → i'] · x_{i''} + x_{i'} · w[i → i'']`;
- `H_q(K) ≅ ⊕_m C_c(Conf_m(C)) ⊗_{Σ_m} W_{m,q}` as `V`-modules.

Both are false for blocks of size `≥ 3`. Cabling a class supported on a block
`B ∋ i` also produces classes supported on splittings of
`B[i → i', i'']` into two blocks of size `≥ 2`, whose support is one larger.

*Witness.* In `Conf_3(C)`, let `T` be the torus with `z_1 = 0`, `z_2 = e^{iθ}`
and `z_3 = 2e^{iφ}`. Cabling strand 1 gives
`⟨c_*T, w_{1''2} w_{1'3}⟩ = ⟨T, w_{12} w_{13}⟩ = 1`. The form
`w_{1''2} w_{1'3}` lies in the Brieskorn summand of the partition
`{1'',2}{1',3}`, which has support 4. The old formula only produces support 3.

*Repair* (part 1, A2–A6, checked by the adjudicator, over `Z`):

- `H^*(Conf_n(C); Z)` is the Orlik–Solomon algebra, graded by partitions
  (Arnold 1969; Orlik–Solomon 1980; Brieskorn 1973).
- Cabling kills `w_{i'i''}` and relabels the other generators.
- Dually, a class of support size `m` goes to classes of support size `m` and
  `m + 1`. So `F_{≥m}` (support size `≥ m`) is stable under cabling and
  relabelling.
- On the graded pieces the transition maps are exactly the relabelling sums
  that the old A4 described.
- Passing to the colimit, `H_q(K; Z)` has a finite `V`-filtration with
  `gr_m ≅ C_c(Conf_m(C), Z) ⊗_{Z[Σ_m]} W_{m,q}` for `q + 1 ≤ m ≤ 2q`.
- V-acyclicity (`H_p(V; −) = 0` for all `p ≥ 0`) passes to extensions by the
  long exact sequence. So the rows `q ≥ 1` of the Lyndon–Hochschild–Serre
  spectral sequence still vanish, rationally and integrally.
- The downstream steps (C6 averaging over `Q`; the free `Z[Σ_m]`-module argument
  over `Z`; Theorem 1 of the germ artifact) apply to the graded pieces unchanged.

No other step used the direct sum.

**Confirmed minor gaps, fixed in place.**

- Lens 1:
  - Proposition 3.4(iii) cited "CM 3.7(2)" for summation along fibres. Now it
    cites the counit `Σ_f : f_!f^*A → A` from the CM Appendix (label `lset`).
  - Lemma 3.3 argued discreteness by hand. Now it uses `(x/φ)^(n) = β_n^{-1}(x)`
    (CM 4.1, 4.2) and that `β_n` is étale for étale `φ` (CM 4.5(2)).
  - Proposition 3.4(iii) now states why `ε d_0 = ε d_1` holds with no twist: `Z`
    has trivial action, so `k_1` acts as the identity on stalks.
  - Proposition 3.4(i) now argues that every sheaf on these spaces is c-soft
    (extension by zero through a compact open), not only the constant sheaf.
    It also names all the nerve spaces covered by CM 1.8.
- Lens 2:
  - Lemma 1.1, well-definedness: the inference `vw = v'w ⇒ |v| = |v'|` was false
    (`0·0^∞ = 00·0^∞`). It now uses agreement on a whole cone.
  - The topology of `G_2` was attributed to "Matui's basis" with injectivity
    conditions that the source does not contain. It is now quoted verbatim
    from Matui 2016 (arXiv:1512.01724, groupoid `G_A` of a one-sided SFT; open
    `P, Q` and `k, l ∈ N`), with both inclusions of topologies proved.
  - `thompson-v-is-integrally-acyclic-citation` quoted only the abstract. It now
    quotes Szymik–Wahl Theorem `thm:Vacyclic` verbatim from the e-print source.
- Lens 3:
  - Step A cited Cohen and Sinha for an operadic basis. It now cites Arnold,
    Orlik–Solomon and Brieskorn for the integral cohomology ring and its
    lattice grading, with no theorem numbers claimed.
  - The "Unreviewed" headers of part 1, part 3 and the germ artifact were
    updated.
  - The problem wording was re-extracted from the Zaremsky PDF stream: "9.Is
    braided V acyclic?", followed by "10.Is braided V Hopfian?". No change was
    needed.

**Rejected gaps.** None. Every reported gap was real. All except the Step A
decomposition were presentation or citation issues.

**Decision: stands with fixes.** The routes
`braided-thompson-group-bv-is-acyclic-from-cantor-modules` and
`braided-thompson-group-bv-is-rationally-acyclic-proof` keep their `requires:`
lists, and no new open claim was created. Their Step 1 and assembly now use the
filtration and extension closure. Files changed:

- part 1 and part 3 of `zp-braided-v-rational-acyclicity-2026-09-13`;
- `cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16`;
- the two routes;
- `thompson-v-is-integrally-acyclic-citation`;
- this note.

**Human expert review is still recommended.** The panel consists of agent
referees only. The certificate still rests on imported results:

- Crainic–Moerdijk 4.3 and 4.4;
- Matui 2012 and 2016;
- `H_*(G_2) = 0`;
- Szymik–Wahl;
- Palmer–Wu, for the rational route;
- the Orlik–Solomon grading.

The repaired Step A is new text and has been checked only by the adjudicator.
Nobody should announce the answer to Zaremsky Problem 2.9 before a human
specialist has reviewed it.
