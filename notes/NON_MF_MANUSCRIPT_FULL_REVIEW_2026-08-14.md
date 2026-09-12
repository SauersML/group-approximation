# Full review and redesign of non_mf_groups_exist.tex (2026-08-14)

> **Historical audit snapshot.**  This records the defects found in the first
> full pass and is retained as the detailed audit trail.  Several operational
> statements and implementation statuses below describe commit `c4babb17`, not
> the final revision.  The current verdict, resolved status, MSI-only
> verification record, and remaining open mathematics are in
> `NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md`.

Scope: complete independent line-by-line read of the current 2,060-line
manuscript (post-rewrite, HEAD `c4babb17`), independent re-derivation of every
printed proof, direct inspection of the Lean statement surface (endpoints,
trust roster, badge resolution), a local compile probe, and an arXiv-API
citation sweep.  Supporting notes/ records were deliberately NOT trusted; every
claim below was re-checked against the tex, the Lean, or a primary source.

## Part I — Mathematical verification (all proofs re-derived)

**No mathematical errors were found.**  Every proof in the manuscript was
re-derived independently.  Details of the load-bearing checks:

1. **Theorem 1.2 (Kazhdan transport), ultraproduct proof — correct.**
   The subtle step is `P = VPV*` from `P ≤ VPV*` in the finite norm
   ultraproduct `B_ω`.  This is genuinely valid: in ANY unital finite
   C*-algebra every projection is finite, by the complement-isometry trick
   (if `w*w = q`, `ww* = p ≤ q`, then `s = w + (1−q)` satisfies `s*s = 1`,
   `ss* = p + 1 − q`; finiteness of 1 forces `p = q`).  The manuscript's
   one-line justification is right, and the triptych display
   (`p ≤ q, p ∼ q` in a finite C*-algebra ⟹ `p = q`) is a true statement —
   but the two-line complement-isometry argument appears nowhere.  Reviewers
   may know it; including it (or a reference) costs two lines and closes the
   only "known fact" gap in the crown-jewel proof.
   Also verified: finiteness of `B_ω` (square matrices: polar correction turns
   one-sided into two-sided inverses), faithfulness of the action on `K_ω`,
   `p_Γ` acting as the fixed-space projection, and the contradiction-per-γ₀
   subsequence structure that upgrades ultrafilter to ordinary convergence.

2. **Theorem 1.4 (central-sign criterion) — correct.**  Corner cut
   `q = (1−Θ(z))/2` is a projection because `Θ(z)` is a self-adjoint unitary;
   the central-corner reduction to a positive-rank corona is correct
   (spectral cut, discard rank-0 coordinates, `J` infinite because `q ≠ 0`).

3. **Theorem 1.5 (Kazhdan–Clifford construction) — correct.**  The
   redundancy of `w² = 1` (`dwd⁻¹ = w⁻¹` vs centrality), the telescope
   embedding of Γ, the coset-distinctness ⟺ `a ∉ α(Γ)` equivalence, and the
   Clifford witness relations were all checked.  `[c_x, c_y] = (c_xc_y)² = −1`
   for distinct anticommuting involutions — correct.

4. **Theorem 1.6/Prop 1.1 (MF equivalences) — correct** including the two
   nonobvious devices: the uniform power bound `M(δ)` (arc-stepping argument
   on the circle: some power of any spectral point `|1−λ| ≥ δ` lands at
   distance > 1 from 1, with `M` uniform by compactness) and the tensor-power
   amplification with telescoping defect bound `mε/M`.

5. **Lemma 6.4 (coordinate finite-normal corner) — correct** (Reynolds
   average, spectral rounding `‖P−H‖ ≤ 2‖H²−H‖`, principal-block compression,
   dimension-free polar repair `‖V−C‖ ≤ 2‖C*C−1‖`).

6. **Lemma 6.5 (Kazhdan fixed-space transport, finite stages) — correct.**
   Re-derived: the eigenvector-ultraproduct spectral-gap argument (eigenvalue
   in `[θ, 1−δ]` contradicts the Kazhdan bound `1 − κ²/(2|S|)`; the printed
   `4|S|` gives safe slack); the exact identity
   `Σ_S ((AdV−1)P)*((AdV−1)P) = 2|S| P(1−H)P`; positivity `1−H ≥ 0`; the
   root-capture estimate; the operator spectral-cut inequality
   `(1−θ)‖(1−P)X‖² ≤ ‖(1−H)X‖` (per-vector then sup); equal coordinate ranks
   for `R_n = T_nP_nT_n*`; and the equal-rank flip `η ↦ η/√(1−η²)`.

7. **Theorem 6.2 (finite-normal criterion) — correct** (exact Reynolds
   identity (∗) in the quotient, corner corona identification, per-element
   lifts, normality of `K₂`, and the `|F|·1` vs `0` HS contradiction).

8. **Theorem B, Prop C, witness section, Lemma 7.1, radical section,
   Theorem D, quotient corollary — all correct.**  The matrix checks in
   Lemma 4.2 were spot-recomputed (dets, `z² = 1`, all nine conjugation
   columns match `xv₁x⁻¹ = v₃`, …, `zv₃z⁻¹ = v₃⁻¹`); `D⁻¹v̄₁D ∉ GL₄(ℤ)` via
   the `1/2` entry is correct and elegant.

9. **Lean trust surface (checked directly, not from docs).**
   `LiteralNonMFEndpoint.manuscriptTheoremA` is hypothesis-free at the type
   level; `literatureInputNames = []` in `scripts/Audit.lean`; property (T)
   of the literal twenty-relator base is proved premise-free
   (`LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT` via the P13
   Hodge certificate), including a complex-unitary textbook form.  The
   manuscript's Theorem 1.2 badge (`manuscriptKazhdanTransport`) matches the
   printed statement faithfully (it is in fact slightly more general — no
   countability needed).

## Part II — Defects found (ranked)

### Critical / operational

C1. **Most Lean links in the shipped PDF are dead.**  Every badge links to
    `blob/verified/GroupApproximation/<file>.lean`, but remote branch
    `verified` (at `37c9f7ee`, Aug 13) predates the rewrite: of the badge
    files sampled, only `Monsters/LiteralCyclicCalibration` exists on
    `verified`; `Sofic/ManuscriptExactWrappers`, `Sofic/KazhdanSignCriterion`,
    `Sofic/KazhdanCliffordConstruction`, `Sofic/LiteralNonMFEndpoint`,
    `Analysis/MaximalGroupCStar` do not.  They exist on `main`.  Fix: after CI
    is green, fast-forward `verified` to the audited commit (or pin badges to
    a commit hash).

C2. **The badge convention is never explained.**  32 gray `[Lean: …]` tags
    appear with zero explanatory text: no sentence says what they mean, what
    was verified, what the repository is, or that unlabeled statements have no
    formal counterpart.  A referee cannot interpret a third of the paper's
    visual surface.  Needs a short "Formal verification" paragraph (intro or
    §2): the repository, the pinned branch, kernel-checking, the
    statement-correspondence caveat, and the remarkable fact (currently
    absent from the paper!) that the formalization is SELF-CONTAINED — even
    property (T) of the presented base is machine-checked from an explicit
    rational spectral certificate, so the formal theorem depends on NO
    literature input, while the printed proof cites [CRW] and [BHV].

C3. **Anonymity is broken.**  `\paperauthor` is "Anonymous" but every badge
    links to `github.com/SauersML/...`.  Either de-anonymize or use an
    anonymized mirror for submission.

### Structural (readability/beauty — the big ones)

S1. **The paper proves its analytic core twice, and Theorem A is routed
    through the heavy copy.**  The intro proves transport (Thm 1.2) and the
    sign criterion (Thm 1.4) completely — and these already suffice for
    Theorem A with `F = {1,w}` (via Lemma 7.1 and the witness).  Yet §7
    instead derives Theorem A from the §6 finite-normal criterion, whose
    proof needs the 4-page quantitative machinery (Lemmas 6.4–6.5).  So the
    reader must absorb both an ultraproduct proof and a finite-stage proof to
    reach the main theorem, though either one suffices.  Recommended
    architecture: make transport → sign criterion → Theorem A the ONE main
    path (≈3 pages of analysis total); present the finite-normal criterion
    and the quantitative lemmas as a clearly-labeled second layer
    ("Effective form and the general finite-normal obstruction" — also the
    layer that matches the Lean formalization) or an appendix.

S2. **The first proof a reader meets is the most boring one.**  The 2.5-page
    routine amplification proof of Prop 1.1 (MF equivalences) sits at the top
    of the introduction, before any idea appears.  Move the proof to the
    corona section or an appendix; keep the statement (one paragraph) in §2.
    The introduction currently is ~30% of the paper and contains four full
    proofs; two (1.2 and 1.4) are the beautiful ones and belong there or in
    an immediately following short section — the other two do not.

S3. **No motivation paragraph.**  The paper opens with a definition.  One
    paragraph is missing: what MF groups are the operator-norm analogue of,
    which groups were known to be MF (residually finite, amenable — via
    quasidiagonality, LEF [CDE]), that the existence of a non-MF group was
    open, and the Blackadar–Kirchberg stable-finiteness context for
    Theorem D.  This is the single cheapest impact improvement.

S4. **Theorem lettering is incoherent.**  Only A and D are `mainthm`s;
    "Theorem B" (`thm:B`, finite-dimensional shadow) is a section-numbered
    theorem and "Theorem C" (`thm:C`) is a Proposition — yet the labels say
    B/C, and lines 611 and 1847 call the Proposition "Theorem C" in prose.
    Readers of "Theorem A … Theorem D" will hunt for B and C.  Make the
    quartet honest: promote both to `mainthm` B and C (they deserve it), or
    stop lettering them.

S5. **Orphaned lemma.**  Lemma 6.4 (`lem:corner`) is proved but invoked by no
    proof; Theorem 6.2's proof re-does its own corner extraction inline, and
    the two remarks that cite `lem:corner` (lines 1637, 1878) attribute to it
    work actually done inline in Theorem 6.2.  Either have Theorem 6.2's
    proof genuinely use it, or fold it in.  Relatedly, the corner
    construction appears three times (intro "central-corner reduction"
    paragraph, Theorem 6.2's proof, Lemma 6.4): state it once as a lemma and
    use it twice.

S6. **Theorem 1.3 (compression radical) is a labeled theorem proved only by
    an "Indeed…" sketch paragraph** (after Theorem 1.3 / eq. 1.9), while its
    weaker special case gets the full §6 proof.  Referees will ask where the
    stronger statement is proved.  Either give it a real (short) proof in the
    general-criterion layer, or demote it to a remark with the sketch.

S7. **Universe-relative `C*_max` leaks Lean plumbing into the main theorem.**
    Theorem A's statement ends "Here C*max(E) denotes the universe-relative
    bounded-product model specified in Proposition 2.1", and §2 opens a
    set-theoretic-universe digression.  For a countable discrete group the
    standard `C*_max` (enveloping C*-algebra of ℓ¹(E)) is classical; use it
    in the paper, and confine the universe-relative model to the Lean
    paragraph as the formalization's equivalent substitute.  As written, the
    first thing an operator algebraist meets in §2 is "Fix a set-theoretic
    universe 𝔘" — in a paper about matrix approximations.

### Notation and terminology

N1. **`z` collision.**  Theorem 1.4 names its central sign `z` while `z` is
    also the third rotation generator (used everywhere from §3 on).  Worse,
    the adjacent conceptual display eq. (1.7) calls the SAME element `ε`.
    Rename the sign in Theorem 1.4 to `ε` (matching (1.7)); the Clifford sign
    is already `ζ` — good.

N2. **"operator-norm asymptotic representation" is never defined** (used in
    Thm 1.2 and Lemma 6.5).  One displayed line fixes it.  Same for
    "local models with separation constant 1" (Prop 1.1, and used again in
    Prop 7.4's proof) and "detects" (= maps to ≠ 1; first use line 348).

N3. **Commutator convention `[x,y] = xyx⁻¹y⁻¹` is declared at the end of §2**
    (line 793) but used from Theorem 1.4 (line 337) on.  Move to first use.
    (The convention matters: with the other convention `w` is a different
    element.)

N4. `d = tct⁻¹` vs dimension sequence `(d_n)` — live with it or rename
    dimensions to `(k_n)`; low priority.

N5. "norm matrix corona" is house terminology; fine since defined
    immediately, but consider flagging it as such ("which we call…" is
    present — OK).

### Minor

M1. Line 611 and line 1847: "Theorem \ref{thm:C}" → Proposition (see S4).
M2. §8 proves Prop C in bare prose with no `proof` environment.
M3. Unused macros: `\Fix`, `\End` (used once?), `\Cl` (superseded by
    `\ClLamp`).  Harmless.
M4. Prop 2.1's justification is a floating paragraph, not a proof
    environment.
M5. The bibliography's [OAI] entry is handled with correct priority care
    (original + updated versions listed).  Keep.
M6. Compile probe: clean under texlive-2025 conventions (tectonic chokes
    only on `\DocumentMetadata`, expected for its older kernel; no undefined
    references, no overfull reports in the probe log).
M7. In Def. 3.2 the relator count is worth stating: 8 generators, 41
    relators (20 base + 6 stable + 1 involution + 6 lamp + 8 centrality).
    "Eight generators and forty-one explicitly displayed relators" is a
    sentence referees and readers will quote.

## Part III — Mathematics available but not in the paper

These are proved (in Lean, or two-line consequences of printed results) and
were dropped or never included; each strengthens the paper at near-zero cost.

A1. **The scaling family `E_m` (and `E_{n,m}`).**
    `Monsters/AffineSL3Scaling.scaling_package` proves: for every `m ≥ 2`,
    `α_m(v, A) = (mv, A)` is an injective endomorphism of `ℤ³ ⋊ SL₃(ℤ)` with
    `(e₁, I)` outside its image.  With Theorem 1.5 this yields an infinite
    explicit family of finitely presented non-MF groups (`E = E₂`).  The
    Lean docstring still points at a manuscript label `thm:family` that the
    rewrite deleted.  Restore as a two-line corollary of Theorem 1.5.

A2. **Necessity of property (T) — the missing calibration.**  Prop C
    currently shows only that finite-dimensional invisibility does not force
    `w = 1`.  The stronger true statement: in `E_BS` the marked word is
    CORONA-VISIBLE.  Proof: the realized Clifford quotient `Q_BS` lives in
    `ClLamp(X) ⋊ (ℤ[1/2] ⋊ ℤ)`, an extension of a locally finite group by a
    metabelian group, hence amenable; amenable countable groups are MF
    (Tikuisis–White–Winter quasidiagonality + Blackadar–Kirchberg QD ⟹ MF);
    composing an injective corona representation of `Q_BS` with
    `E_BS ↠ Q_BS` exhibits a corona representation of `E_BS` with
    `w_BS ↦ −1 ≠ 1`.  Hence the (T) hypothesis in Theorem 1.4/6.2 cannot be
    dropped: the identical marked pattern over the cyclic base has a
    surviving sign.  This bounds the theorem sharply from both sides and
    turns §8 from a footnote into a genuine calibration.  Requires adding
    the TWW citation (Ann. of Math. 185 (2017)) as a disclosed,
    not-formalized input (consistent with the trust-surface doctrine if
    tagged; the Lean already proves the quotient realization and
    `quotientMap_mark_ne_one` — only amenable ⟹ MF is cited).

A3. **MF is subgroup-hereditary; consequences.**  One line (restrict an
    injective corona representation).  Not stated anywhere, though used
    implicitly.  Two free corollaries:
    (i) no MF group contains `E` — every group containing `E` is non-MF;
    (ii) embedding `E` into a 2-generator finitely presented group
    (classical embedding theorem) yields a **2-generator finitely presented
    non-MF group**.
    (The Lean `Monsters/UniversalMFEventHorizon` proves a version of (i)
    for a universal f.p.-containing group.)

A4. **MF groups are not closed under extensions.**  The witness group — the
    subgroup `W₀ ≤ ClLamp(X) ⋊ V` generated by the image of `E` — is not MF
    (portability, Lemma 7.2: the image of `w` is `ζ ≠ 1`), yet it is
    (locally finite)-by-(f.g. linear over ℚ, hence residually finite):
    an extension of two MF groups.  Combined with `F₈ ↠ E`: MF groups are
    closed under subgroups, but under neither quotients nor extensions.
    Currently only the quotient half is in the paper.

A5. **Theorem D's framing.**  `C*_red(E)` is (to our knowledge, and pending
    the literature check) the first separable stably finite C*-algebra
    proved not to be MF, and the first reduced group C*-algebra proved
    non-MF; this speaks directly to the Blackadar–Kirchberg stable-finiteness
    question.  The paper states the theorem with no context sentence.  Add
    the context (with the BK question quoted precisely — nuclear vs general —
    per the citation report below).

A6. **The self-contained formal (T) certificate** (see C2): the paper's
    "External inputs" section lists [CRW] + [BHV] as inputs without saying
    that the machine-checked track discharges both.  Saying so converts an
    apparent weakness (two literature inputs) into a headline strength.

## Part IV — Ideal design (target ≈ 60% of current length on the main path)

The sentence to optimize (it is already the right one, and the paper should
keep engineering everything around it):

> Kazhdan rigidity forces `u →₂ 1`; a Clifford model forces `u² = −1`.

Proposed order:

1. **§1 Introduction (≈3 pages, ONE proof).**  Motivation paragraph (S3);
   definitions of corona and MF in ≤ half a page (statement of equivalences,
   proof deferred); the triptych display; Theorem 1.2 (transport) STATEMENT;
   the five-line proof of the sign criterion assuming transport — this is
   the one proof that belongs in the introduction; statements of Theorems A,
   B, C, D (all four as lettered main theorems, per S4) and the general
   construction; the family `E_m`; consequences list; formal-verification
   paragraph (C2); related work; organization.
2. **§2 The rigidity theorem.**  The ultraproduct proof of transport,
   with the two-line finiteness-of-projections argument included.  ≤2 pages.
3. **§3 The construction.**  Conceptual presentation with the redundant
   central `ε` (eq. 1.7 style), Theorem 1.5 and its proof, the telescope +
   Clifford witness, family corollary (A1).
4. **§4 The explicit group.**  Presentation `E` (with the 41-relator count),
   identification of the base, Lemma 4.2 matrices, `w ≠ 1`, proof of
   Theorem A via §1's criterion + Lemma 7.1 (defect square).  Short.
5. **§5 Finite-dimensional shadow and calibration.**  Theorem B (unchanged),
   Proposition/Theorem C strengthened by A2 (necessity of (T)).
6. **§6 The general finite-normal obstruction, effectively.**  Marked
   patterns, compression radical (with a real proof, S6), the finite-stage
   Lemmas 6.4–6.5 presented as the effective/ultrafilter-free layer that the
   Lean formalization checks end-to-end.  This is where "quantitative
   realization" lives; a reader who trusts §2 can skip it losslessly.
7. **§7 Consequences.**  Radical, universal MF quotient, Theorem D with BK
   framing (A5), subgroup-heredity + 2-generator corollary (A3), quotient
   AND extension nonclosure (A4).
8. **§8 Boundaries and questions.**  Operator-norm boundary (current §9)
   plus a short open-questions list: is `E/⟨w⟩` MF (equivalently is the MF
   radical exactly `{1,w}`)?  torsion-free non-MF groups?  is `E` sofic or
   hyperlinear?  effective bounds.
9. **Appendix A.**  Proof of the MF equivalences (moved from the intro).

Editorial rules that the current draft already half-follows and should follow
fully: a constant appears in the main text only if changing it changes the
phenomenon; the reader meets `u` before the expanded word for `u²`; the
concrete presentation is visibly an optimization of the conceptual one; the
first non-MF proof is the two-point sign corner, Reynolds averaging comes
later.

## Part V — Citation verification (arXiv-API sweep, completed)

All 11 arXiv entries and all 15 DOIs in the bibliography verified clean
(titles, authors, volumes, pages; the future-dated BDL J. Algebra 702 entry
matches Crossref exactly; both OAI CDN URLs resolve with content-lengths and
Aug-6-2026 timestamps consistent with the citation).  One cosmetic defect:
[GKEMP] was out of alphabetical order (fixed).  Landscape facts established
from primary sources: Shulman (arXiv:2603.13564v2, §1) names "the MF
conjecture states that every countable group is MF"; Schafhauser
(arXiv:2306.02498, §1): "there are no known examples of groups which are not
MF"; Rainone (arXiv:1404.4389) quotes Blackadar–Kirchberg's remark that no
stably finite separable C*-algebra was known not to be MF, with candidate
C*_red(F_r) later proved MF by Haagerup–Thorbjørnsen (math/0212265,
Cor. 8.4); CDE (arXiv:1210.4050, intro) states the general stably-finite ⟹
MF question open; Magee–de la Salle state the MF property of
C*_red(SL₃(ℤ)), C*_red(SL₄(ℤ)) is not known.  The explicitly *posed*
Blackadar–Kirchberg question was the nuclear/quasidiagonal form; the general
separable form is sourced as a BK remark plus folklore-open status — the
manuscript's framing now matches this record exactly.

## Part VI — Implementation status (this session, commits 0eb8ca35..f3b9b7e9)

Implemented in the tex: sign renamed to ε; Theorems A–D lettered; conventions
and asymptotic-representation/local-model/"detects" definitions added;
41-relator count; motivation opening with MF-conjecture and BK framing;
equivalences proof moved to Appendix A; formal-verification paragraph
(self-contained trust surface); classical C*_max with formalization remark;
Theorem A rerouted through the sign criterion (proof now in §5); corona
lemmas merged into §2; compression radical moved to §7 with a complete proof
via a both-directions transport corollary (a concurrent session upgraded the
corollary to the Lean-anchored `compressionGroup_transport_both` — kept);
ultrafilter corner lemma's role marked; permanence subsection with
badge-anchored subgroup/RF/locally-finite lemmas; questions subsection;
organization updated; TWW+HT bib entries; overfull fixed.  Repo gates green
(35 verified references resolve; zero-tolerance scan clean).

Gated on the background Lean agent (zero-conditional rule): scaling family
E_m; necessity of (T) via LEF of the realized cyclic quotient; extension
nonclosure for the witness subgroup.  Manuscript claims for these are
deliberately withheld until the premise-free Lean endpoints land.
Dead badge links self-heal when CI promotes `verified` past the rewrite.
