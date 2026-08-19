# Credit and priority audit for the non-MF manuscript

Date: 2026-08-14.  This began from an adversarial literature review and was
then checked against the cited primary papers, including theorem-level checks
of every attribution added to the manuscript.  The adjacent sofic
breakthrough is eight days old, so the audit remains time-sensitive.  These
are paper-facing facts and directives.  Nothing here enters Lean as a premise;
the Lean development remains zero-premise and claims correctness, not novelty.

## 2026-08-14 submission-day sweep

A fresh search of the 2026 arXiv record found no independent operator-norm
non-MF group theorem.  The closest current primary sources remain sharply
separated from the paper's claim:

* Shulman, arXiv:2603.13564v2 (22 March), studies positive MF permanence and
  uses the same operator-norm definition;
* Fournier--Facio, arXiv:2608.02025 (3 August), constructs a torsion-free
  nonsofic group;
* Alekseev--Thom, arXiv:2608.05362 (5 August), proves a centralizer theorem
  for sofic embeddings of Kazhdan groups; and
* Kun--Thom, arXiv:2608.06222 (6 August), constructs nonsofic generalized
  wreath products with ordinary abelian lamps.

None of the three August papers claims a non-MF group or an operator-norm
matrix-corona obstruction.  This supports the manuscript's narrow priority
language as of the date above; it does not justify a claim to the first
stably finite non-MF C-star algebra, which remains expressly disallowed
below.  Because the area is moving on a scale of days, this sweep must still
be repeated at actual submission.

## Verdict summary

* No prior theorem found from which Theorem A (existence of a non-MF group
  in the Carrión–Dadarlat–Eckhardt/Shulman operator-norm sense) is a
  corollary; no independent non-MF counterexample found through 2026-08-12.
  Shulman (arXiv:2603.13564, March 2026) uses exactly this definition and
  still calls the MF conjecture open; Bachner–Dogon–Lubotzky
  (arXiv:2508.17392) likewise.
* The defensible novelty claim is NARROW: the stable-finite Kazhdan pinning
  of the conjugation representation in a norm matrix corona, plus the
  central-corner/marked-word device converting the pinning into a group
  element killed by every MF representation.  The surrounding
  compression/lamp architecture is NOT ours to claim.
* **Correction to the C*-algebra consequence:** Theorem D is not the first
  counterexample to ``stably finite implies MF'' for arbitrary separable
  C*-algebras.  The negative Connes embedding result from MIP*=RE already
  refutes the general MF problem; Goldbring, Corollary 5.2, gives the direct
  deduction.  What is new here is the explicit reduced group C*-algebra
  realization.  Shulman still recorded in March 2026 that no full or
  reduced group C*-algebra was known not to be MF.

## Manuscript corrections implemented

1. PROBLEM AGE: distinguish the 1997 Blackadar--Kirchberg/Kirchberg MF
   problem lineage from the exact CDE group definition, first posted in
   October 2012 and published in 2013.  CDE Definition 2.7 verifies the
   definition attribution, but the paper does not literally formulate
   "is every countable group MF?"; later sources explicitly state that
   universal question and attribute it to Kirchberg.  At the August 2026
   result date the two ages were about 29 years and nearly 14 years.
2. HISTORY/PRIORITY: the first nonsofic
   group is OpenAI's; Kun–Thom (arXiv:2608.06222, posted 2026-08-06)
   explicitly build on it and extract/generalize the mechanism.  Do not say
   the sofic case "was solved negatively by Kun and Thom" without the
   OpenAI attribution.
3. METRIC FIX: sofic approximation is the normalized HAMMING/permutation
   metric, not "rank metric".  Shulman states the three metrics: operator
   norm (MF), normalized Hilbert–Schmidt (hyperlinear), Hamming on
   symmetric groups (sofic).
4. Add a serious paragraph on OpenAI + Kun–Thom as the closest conceptual
   analogue (one-sided compression tΓt⁻¹ < Γ + property (T) + lamp
   centralizing Γ), and explain why the operator-norm argument is distinct:
   the decisive step P ≤ β(t)Pβ(t)* ⟹ equality holds because the
   conjugation representation lands in a stably finite norm matrix corona —
   a mechanism with no analogue in the permutation/Hamming setting.
5. Add Ozawa–Thom (via Dadarlat, Prop 3.19, S0001870821001602) as prior art
   for the operator-norm-lifts → Ad U on L²(Mₙ) → property-(T) fixed
   vectors maneuver.  It does not prove our theorem (E is not (T); Γ is
   residually finite; their output is quotient information, not a universal
   kernel element), but the analytic vocabulary is ancestral.  Cite
   prominently, not just Akemann–Walter/BHV.
6. Reframe Theorem C: "amenable MF but non-RFD/non-MAP" as a broad
   phenomenon is already covered by CDE's treatment of Abels' group
   (S0022123613001201).  Present C only as a sharp calibration: the same
   marked-sign compression pattern becomes MF once property (T) is removed.
7. Soften "genuinely a property-(T) phenomenon" to "property (T), or a
   substitute furnishing a uniform fixed-space projection, is essential to
   this argument."
8. Page 1 must say MF in the CDE–Shulman sense (embedding in the unitary
   group of a norm matrix corona); Shulman warns a stronger property has
   also been called MF.
9. Fix the CDE attribution for the "C*max fails stable finiteness under
   Kazhdan compression" remark: no precise CDE source verified.  Either
   locate a precise reference or state it as a short folklore observation
   and prove it in place.

## What to claim vs not claim

CLAIM (no predecessor found): non-MF group existence (CDE–Shulman sense);
explicit finitely presented example; the fixed marked element w ≠ 1 killed
by every matrix-corona representation ("MF radical" element); non-MF of both
C*max(E) and C*r(E) as a new corollary (Shulman explicitly noted no such
examples were known); the central-corner rank-renormalization tactic.

DO NOT CLAIM: the first stably finite non-MF separable C*-algebra (known
after MIP*=RE); property (T)/Kazhdan projections (classical); conjugation on
L²(Mₙ) + (T) (Ozawa–Thom); stable finiteness of matrix coronas (standard);
Clifford/extraspecial anticommutation (classical); one-sided subgroup
compression + lamp normalization architecture (OpenAI/Kun–Thom); simple- or
(T)-envelope embedding theorems (Goryushkin–Schupp; SQ-universality —
external, cite when used, tex-only).

## 2026-08-13 second-pass attribution map (user-supplied deep audit)

Non-negotiable additions before circulation (none subsumes Theorem A):

1. **Slofstra–Vidick (arXiv:1711.10676), Prop. 2.7** — the central-involution
   → exact involution → (−1)-eigenspace compression predates us.  Our
   distinctive refinement: the norm-corona corner change renormalizes the
   trace, so NO lower bound on relative rank/density is needed (their HS
   setting requires positive relative dimension).  Highest-priority missing
   citation.
2. **Slofstra 2018 (arXiv:1806.05267)** — Clifford groups with distinguished
   central sign + shift on Clifford generators + semidirect product + HNN
   doubling, in approximate-representation theory, INCLUDING an
   operator-norm variant.  Never claim "the operator-norm realization" as
   the novelty; the defensible claim is the stable-finite Kazhdan
   fixed-space pinning in a norm corona producing a universal marked
   kernel.
3. **Slofstra 2017 (arXiv:1703.08618)** — G^fin/G^fa: quotients by elements
   invisible to exact vs approximate finite-dimensional representations.
   Cite around Theorems B/C and the "MF radical" (the
   universal-invisibility-quotient idea has this predecessor; the MF
   instance and terminology may be new).
4. **OpenAI Prop. 2.3 + Kun–Thom, precisely** — cite the compression
   semigroup P_Γ = {g : gΓg⁻¹ ≤ Γ}, "infranormal", the sofic Mautner
   envelope / fixed-algebra invariance, AND their explicit finite-quotient
   observation that tΓt⁻¹ ≤ Γ becomes equality by cardinality.  Present
   the trichotomy: finite group (cardinality) / finite-dimensional algebra
   (dimension, Theorem B) / finite C*-algebra (Murray–von Neumann
   finiteness, Theorem A) — all forcing one-sided self-compression to
   equality.  Chronology: Kun–Thom 2026-08-06, Alekseev–Thom 2026-08-05;
   state contemporaneity/independence exactly, never implied derivation.
   Foundational lineage: Kun (arXiv:1606.04471) expander decomposition;
   Kun–Thom (arXiv:1901.03963).
5. **Dadarlat anatomy correction** — Lemma 3.18 (almost-commuting
   finite-rank projections → almost-invariant normalized HS vectors; cites
   Rosenberg, Andreas Thom's MathOverflow observation, Schneider) is
   distinct from Prop. 3.19 ("Ozawa–Thom", + property (T) → infinite RF
   quotient).  Cite both separately; the MathOverflow provenance is part
   of the lineage.
6. **Alekseev–Thom (arXiv:2608.05362), Open Problem 6.2** — commutant
   structure of Kazhdan representations into tracial matrix ultraproducts:
   cite in the limitations section; our tracial-side failure is exactly
   adjacent to their live question.
7. **DGLT (arXiv:1711.10238)** — credit the ARCHITECTURE (stability +
   non-RF central extension → marked central obstruction to approximation),
   not only the unnormalized-Frobenius result.
8. **Fritz BS(2,3)** (via Slofstra–Vidick) — early explicit
   exact-vs-approximate quantitative example; one sentence near the
   BS(1,2) calibration.
9. **Bader via Dogon–Vigdorovich** (+ Ozawa's sum-of-squares (T)
   characterization; generalizing Manuilov–You) — operator-norm almost
   representations of Kazhdan groups have a robust spectral gap.  THIS
   BELONGS TO THE FORMAL COMPANION: our finite-stage Kazhdan spectral
   projector layer (hermitianAverage gap for OpAlmostRepresentation) is
   independently derived in-repo but is parallel machinery; cite in the
   formalization remarks/README, and it becomes essential if the paper
   ever adopts the finite-stage proof.

Novelty claim, final narrowed form: the individual architectural pieces
have substantial ancestry (Clifford signs, HNN doubling, negative-corner
compression, one-sided Kazhdan compression, exact-vs-approximate marked
elements); the new content is the chain norm-corona representation →
adjoint norm-corona → Kazhdan projection inclusion → stable-finite
equality → universal marked MF kernel, with the rank-density-free corner
renormalization, and no prior explicit (finitely presented) group with a
fixed w ≠ 1 killed by every norm-corona homomorphism.

## 2026-08-13 third-pass audit: INHERITANCE (machinery/strategy lineage)

User-supplied; two open items resolved by the coordinator against primary
sources the audit could not reach:

* **RESOLVED — Clifford-lamp provenance is clean.**  (a) The OpenAI
  nonsofic chapter (full source in `official/`) contains ZERO
  anticommutation/central-sign/Clifford/extraspecial machinery; its
  commuting object is a Thompson-type subgroup J.  (b) Kun–Thom
  arXiv:2608.06222 (checked against the full HTML): lamps are PLAIN
  ABELIAN ⊕_{G/Γ} ℤ/2 — no central extension, no marked/sign element;
  nonsoficity is proved via the normalizer obstruction (centralizer of
  σ(Γ) normalized by σ(G)), and NO operator-norm/MF/corona notion appears.
  Consequence: the marked-central-kernel strategy and the Clifford sign
  are NOT an adaptation of either; state the contrast explicitly.  Still
  required: identify ClLamp(X) as the classical Clifford/CAR central-sign
  extension of ⊕ℤ/2, with classical references; its multiplication uses
  the ordered-inversion cocycle, while the associated commutator form is
  the parity expression recorded in the fourth-pass correction below.
  See also Chifan–Ioana–Osin–Sun for a modern (T)-on-lamps toolbox.
* **Base-group machinery (mandatory adds):** Γ = ℤ³⋊SL₃(ℤ) with
  α(v,A) = (2v,A) is the simplest instance of the Cornulier–Abels
  non-(co-)Hopfian Kazhdan machine; Thom 2010 ("Examples of hyperlinear
  groups without factorization property") runs the same
  scaling-endomorphism play and — verify against its §2 before citing for
  this — may already exhibit (T)-flavored groups with a central element
  invisible to finite-dimensional reps while hyperlinear (the Theorem
  B/Cor 4.5 phenomenon).  Cite Cornulier 2007, Abels 1979, Thom 2010.
* **Strategy credit:** the "(RF)-by-finite central sign carries the
  obstruction" program was published AS a program: Glebsky–Rivera 2008,
  Glebsky 2019 (with the DGLT example noted there as
  RF-by-finite).  Theorem A executes it in operator norm; say so.
* **Two-norm engine:** beyond Ozawa–Thom/Dadarlat, credit Kun 2016 and
  Kun–Thom 2019 for the (T)-rigidity-of-approximations engine
  (almost-invariant vector for the conjugation action, upgraded and
  propagated) in the Hamming metric.
* **Obligation:** read Alekseev–Thom arXiv:2608.05362 (19 pp) line by
  line and delimit overlap with the manuscript's Lemmas 6.4–6.6
  explicitly (their title IS Step 1's object).
* **Folklore anchors:** Lemma 5.4 = Blackadar–Kirchberg stable finiteness
  of MF; Lemma 5.2 = Loring's perturbation/lifting book; "MF radical" →
  anchor to Nikolov–Schneider–Thom approximation kernels (in addition to
  the Slofstra G^fin/G^fa anchor from pass two).
* **Borisov–Sapir** (already landed in prop:ambient): ascending HNN
  extensions of f.g. linear groups are residually finite ⟹ G is RF hence
  MF ⟹ the lamp generator is provably necessary — keep as a stated
  proposition, not a hand-wave.

## Checked non-collisions

* Theorem B (finite-dimensional sterility) does not trivialize A: no
  "finitely presented + MF ⟹ RFD/MAP" implication exists (CDE's Abels
  example blocks it).
* No hidden C*-algebra corollary: only the one-way implication
  "C*(G) or C*r(G) MF ⟹ G MF" is on record (Shulman); the group-level
  theorem is strictly stronger content.
* GitHub search surfaced only this repository, no external predecessor.

## Third pass (2026-08-12/13 night, citation-audit session): source-level verification

Deep-web verification with PDFs in hand (CDE, Dadarlat, Shulman v2, TWW,
CRW via Wayback, both OpenAI PDF versions).  Fixes marked APPLIED are in the
tex working copy as of this note.

### Errors found and APPLIED to the tex

1. TWW pinpoint was WRONG: amenable⇒quasidiagonal is **Corollary C**, not
   Corollary B (Cor. B is the UCT/faithful-trace statement).  Fixed at
   `fact:tww`.  (Cor. C says "discrete, amenable" — no countability
   hypothesis; our statement restricts, which is harmless.)
2. CRW matrices: the paper's x and y were SWAPPED relative to CRW's own
   assignment (CRW: x = h = the 3-cycle permutation matrix, y = aha, z = p;
   Theorem 2 relator list is exact, character for character).  The relator
   set is invariant under x↔y so nothing downstream was false, but as
   transcription it was wrong.  Fixed: matrices swapped, the v_i-action
   lines swapped to match the columns, and a provenance parenthetical added
   (CRW never display the integer realization as a single statement; it is
   assembled from their §§1,2,4; we verify relations + generation directly,
   enough by Hopficity).  Source: Wayback copy of PAMS 115 (1992) 19–26.
3. BDL: first author is **B.** (Benjamin) Bachner, not "G."; volume+pages
   are final (J. Algebra 702 (2026) 235–243, issue dated 2026-09-15), so
   "to appear" dropped.  arXiv:2508.17392.
4. DGLT published title spells **"nonapproximable"** (one word); fixed.
5. OAI: the cited URL now serves the REVISED PDF (updated 2026-08-06) in
   which Chapter 3 is titled "Nonsofic groups exist", pp. 78–95; the old
   title "A counterexample to the soficity conjecture" and pp. 77–93 belong
   to the original, which OpenAI moved to .../ten-proofs-oai-original.pdf.
   Entry updated to the current PDF's metadata, marked non-refereed, with
   the original-version pointer retained.
6. Bibliography order: [CRW] moved before [Dad] (author-alphabetical).
7. DOIs added where verified: AW 10.4153/CJM-1981-067-9, BK
   10.1007/s002080050039, CDE 10.1016/j.jfa.2013.04.004, TWW
   10.4007/annals.2017.185.1.4, Dad 10.1016/j.aim.2021.107722 (resolution
   to PII S0001870821001602 checked directly).
8. PMF≠MF guard added to the introduction with new entry [MdlS]
   Magee–de la Salle, "SL_4(Z) is not purely matricial field", C. R. Math.
   362 (2024) 903–910, arXiv:2312.03220.  Rationale: nearest published
   negative result in the MF family; a referee who knows PMF as a named
   property (standard since Gao–Kunnawalkam Elayavalli–Manzoor–Patchell,
   arXiv:2603.24502) could think "SL4(Z) non-MF was known"; the intro now
   states the distinction explicitly (SL4(Z) is RF, hence MF as used here).

### Verified correct (no change needed)

* CDE pinpoint §2.14 + Cor 2.18 exact (§2.14 = "An MF group that is not
  LEF", Abels' group; Cor 2.18 verbatim MF-not-LEF; non-RF via Hopf in the
  §2.14 body — citing both is right).  CDE Def 2.7 defines MF groups and
  claims the coinage; attribution "introduced by CDE" is correct.
* Shulman arXiv:2603.13564 (v2, 2026-03-22): Definition 3 + footnote 1 as
  cited; the three-metric sentence is there (her wording: "Hamming
  distance" on Sym(n), unnormalized wording — ours is a paraphrase, fine);
  "There are no examples of groups whose full or reduced C*-algebra is not
  MF" verbatim — anchor for both openness and the C*-corollary novelty.
* Dadarlat: Prop 3.19 labeled "(Ozawa-Thom)", preceded by "essentially
  pointed out by Thom on MathOverflow"; Lemma 3.18 is the HS-vector step.
  arXiv id is 2007.12655.  Joint Ozawa–Thom attribution is the fair one.
* AW, BHV(book data), BK, BO, CDE, CRW, Dad, DGLT(rest), KT (v1,
  2026-08-06, 16pp), Shulman, TWW metadata all verified.  BK Theorem 3.2.2
  is the corona-embedding characterization: `fact:qdcorona` now cites BK
  Thm 3.2.2 + BO Ch. 7 (BO sub-numbers vary across printings; avoid 7.x.y
  pinpoints).  CRW metadata rests on converging indexes + MR1079696 (AMS
  and zbMATH 403-block bots) — weakest sourcing, nothing contradicts.

### Priority sweep (fresh, 2026-08-13): NO COLLISION

* No paper or preprint claims a non-MF group through 2026-08-13.  Openness
  independently attested: Shulman (Mar 2026, verbatim above);
  Gao–KE–Manzoor–Patchell arXiv:2603.24502 (positive-direction PMF/PFF
  permanence); Korchagin arXiv:1704.06906 ("existence of non MF-groups is
  also open question", corona formulation, Higman candidate).
* Kun–Thom 2608.06222 v1 contains NO operator-norm/MF content (grep of
  full text: "MF", "matricial", "operator norm", "corona" absent).  Their
  Theorems: A = nonsofic wreath products; B = centralizer normality for
  sofic G; C = fixed-algebra invariance; E = explicit RF Kazhdan examples.
* OpenAI Ten Advances nonsofic chapter's open-problems list names
  hyperlinearity, surjunctivity, determinant conjecture etc. — MF is never
  mentioned.  The operator-norm lane was unoccupied.
* arXiv:2510.17003 = Mehdi Moradi, "Quasidiagonality of Kazhdan Groups"
  (Oct 2025), claimed infinite (T) groups never have FDD; WITHDRAWN in 3
  days ("serious gap in the proof of Theorem 3.2").  Same *shape* as our
  engine (property (T) vs finite-dimensional approximation), hence extra
  scrutiny expected on the Kazhdan step; our Lean lane covers exactly that.
* Adjacent but non-threatening: De Bondt–Thom arXiv:2607.19556 (trace-norm
  rigidity of reduced products); a July-2026 "Z^2 flexibly stable in
  operator norm" listing (arXiv id unconfirmed — do NOT cite without
  checking); Ersoy arXiv:2604.19174 (minimal nonsofic).
* Known alternative route worth one distinguishing sentence in the tex: a
  f.g. non-RF operator-norm-stable group would also refute MF (stability
  literature); no such group is known — our route does not go through
  stability.
* "MF radical with HNN theory" prior-art lead was a search-engine artifact
  (conflation with amenable radical); checked against Korchagin full text.

### Still pending (agents out)

BHV section-number check for `fact:T`/`fact:kazhdan`; Slofstra trio
(SlofstraCorrelations/Profile/Vidick) incl. whether Prop 2.7 and the
Section 3/Remark 3.3 pinpoints are right; OAI Prop 2.3 skeleton check;
AT Open Problem 6.2; second batch (BoS linear-mapping-torus SCOPE — this
one is load-bearing for Prop `prop:ambient` —, DV Thm 7.10, Go, Ma, Neu,
Ra metadata).

## Third pass, continued: BHV and the new prior-work citations

### BHV — both pinpoints were WRONG; APPLIED fixes

* `fact:T` cited "Sections 1.4–1.5 and 4.2": §1.4 is SL_n over LOCAL
  fields; §1.5 is symplectic (irrelevant); §4.2 stops at the n=2 relative
  statement.  The correct numbered source for both SL_3(Z) and
  Z^3⋊SL_3(Z) having (T) is **Example 1.7.4(i)** (via Cor. 1.4.16 +
  lattice Thm 1.7.1); explicit constants: Thm 4.2.5.  WORSE: the fact
  bundled "Γ is finitely presented" under the BHV cite, but (T) does NOT
  imply finite presentability and BHV §3.4 exists to refute exactly that
  (Behr / de Cornulier examples).  Fixed: fact:T now cites Example
  1.7.4(i) (+4.2.5), drops the unused relative-(T) clause, and derives
  finite presentation from the displayed CRW-based presentation instead.
* `fact:kazhdan` cited "BHV Chapter 6" — that chapter (expanders, ergodic
  theory, invariant means) contains NO Kazhdan projection; the book never
  treats it (index has no entry; C*max only in Appendix F.4).  Fixed:
  cite Akemann–Walter (confirmed the original source, per Drutu–Nowak
  arXiv:1501.03473) + Valette, *Minimal projections, integrable
  representations and property (T)*, Arch. Math. (Basel) 43 (1984)
  397–406, doi:10.1007/BF01193846 (verified; new bibitem [Va]).
* Numbering cross-checked between the free 2007 BHV PDF and the printed
  2008 edition via arXiv:1007.4463's quotations; section TITLES changed in
  print, numbers did not.  Do not quote BHV section titles from the PDF.

### Slofstra trio, OAI, KT, AT, FF — verified; six pinpoints APPLIED

* The three keys are three DISTINCT papers (peer's split was right):
  [SV] Slofstra–Vidick, Ann. Henri Poincaré 19 (2018) no. 10, 2979–3005,
  arXiv:1711.10676; [Slo18] Slofstra solo, arXiv:1806.05267, STILL
  UNPUBLISHED v1 (bibitem correctly says preprint); [Slo17] Slofstra,
  Forum Math. Pi 7 (2019) e1 (Definitions 2.5–2.7 range is fair; the
  quotients G^fin/G^fa live in surrounding prose — don't quote a single
  numbered definition as defining the quotient).
* SV Prop 2.7's STATEMENT is a profile inequality; the negative-eigenspace
  compression is its PROOF.  All three tex citations now say "proof of
  Proposition 2.7".  Same pattern for Dadarlat Lemma 3.18 (statement =
  weak containment of trivial rep in π⊗π̄; HS vectors = proof); tex
  rephrased and cites "Lemma 3.18 and its proof".
* Slofstra 1806.05267: Clifford/shift/HNN construction is **Section 2**
  (tex said 3, twice — fixed); Remark 3.3 (operator-norm + Schatten-p
  variant) is in §3 (correct).  Fritz BS(2,3) is **Example 3.1** of SV,
  not "§2.2" (neither paper has subsections) — fixed, plus original
  source added: [Fri] T. Fritz, J. Math. Phys. 54 (2013) no. 5, 052107,
  doi:10.1063/1.4807079.
* KT: wreath headline is Theorem A (B = centralizer normality, C =
  fixed-algebra invariance, Cor. D = Bernoulli, E = explicit examples);
  tex now cites Theorems A, B and C.  KT do NOT say "by cardinality" for
  the finite-quotient equality; gloss removed.  Compression semigroup /
  infranormality / sofic Mautner envelope terminology all verbatim-real.
* OAI Prop 2.3: number stable across BOTH PDF versions but hypotheses
  differ (original: Γ≤G both f.g. with (T), soficity ⇒ J LEF; current:
  (T) only on Γ, expander-approximation hypothesis).  Tex skeleton
  description is version-agnostic and stays.  Announcement 2026-08-01;
  update 2026-08-06; the redacted priority claim ("no progress ... for at
  least a decade", redacted 2026-08-03) is citable via Fournier-Facio's
  footnote 2 in arXiv:2608.02025.
* Alekseev–Thom Open Problem 6.2: statement checked against full text —
  the tex's description (commutant of a Kazhdan representation into a
  tracial matrix ultraproduct as an ultraproduct of finite-dimensional
  subalgebras / coordinate centralizers of lifts) is accurate.
* Fournier-Facio arXiv:2608.02025 (2026-08-03, 4pp): Theorem 1.3 = f.p.
  torsion-free nonsofic group via small cancellation + OAI Prop 2.3.
  Bibitem data verified.

## Third pass, final installment: second-batch sources (all APPLIED)

* **Borisov–Sapir SCOPE CONFIRMED**: Theorem 1.2 = free groups; **Theorem
  1.6** = "the mapping torus of any injective endomorphism of a finitely
  generated linear group is residually finite", footnote: "representable
  by matrices of any size over any field" — no characteristic or size
  restriction; covers G = HNN(Γ, α) for Γ = Z^3⋊SL_3(Z), α=(v,A)↦(2v,A)
  verbatim.  Pinpoints upgraded to Thm 1.6.  TRUST SURFACE: Theorem 1.6
  (unlike 1.2) is deduced from Hrushovski's Frobenius manuscript, which
  BS's own abstract calls "a not yet published result" and which remains
  an unrefereed preprint (arXiv:math/0406514); a caveat now appears in
  the external-inputs paragraph.  Corroborated by BS's 2008 sequel
  (arXiv:0810.0443) quoting "[BS, Theorem 1.6]" against the published
  version.
* Dogon–Vigdorovich Thm 7.10: metadata and v2 pin correct; the tex's
  existing sentence (Bader's almost-spectral-gap argument, proved from
  Ozawa's characterization) matches the actual statement — NO change
  needed.  (Numbering is 6.10 in v1; the bibitem's v2 pin is
  load-bearing, keep it.)
* Haagerup–Thorbjørnsen: metadata exact; the MF statement is **Corollary
  8.4**, valid for ALL r ∈ N ∪ {∞} (wider than the Ext corollary 8.5);
  pinpoints added, "every k" made explicit in cor:subalg's proof.
* Mal'cev 1940 (Mat. Sb. 8(50), 405–422): correct source for f.g. LINEAR
  ⇒ RF (all tex uses are the linear form — checked) and for f.g. linear
  ⇒ Hopfian (now cited for the SL_3(Z) Hopficity step in the CRW
  parenthetical).  The abstract "f.g. RF ⇒ Hopfian" would be Mal'cev
  1958 (Ivanov. Gos. Ped. Inst. Uchen. Zap. 18, 49–60) — not needed by
  the current text; do not attribute the MAP⇒RF corollary to the 1940
  paper as a stated theorem.
* Goryushkin (Math. Notes 16 (1974) no. 2, 725–727 / Mat. Zametki 16,
  231–235, doi:10.1007/BF01105577): verified incl. content (every
  countable group embeds in a 2-generated simple group).
* B. H. Neumann JLMS s1-12 (1937) 120–127: verified incl. continuum
  family content.  Rainone JFA 267 (2014) no. 2, 542–578: verified.
* Post-fix consistency: 31 cite keys ↔ 31 bibitems, no orphans either
  direction (checked mechanically).

## 2026-08-13 late: Alekseev–Thom read obligation CLOSED

Alekseev–Thom arXiv:2608.05362 read in full (19 pp) by the peer session.
Theorem A: Kazhdan + sofic embedding with ergodically-acting centralizer ⇒
LEF (f.p. ⇒ RF); technical Theorem 3.1: the centralizer of a sofic
embedding of a Kazhdan group is a metric ultraproduct of finite permutation
groups, via Kun's expander decomposition, cluster groupoids, and
Becker–Chapman stability.  Footnote 1 documents completion mid-July 2026,
before the OpenAI announcement.  Entirely Hamming/tracial: no
operator-norm, corona, or MF notion appears; no marked element is produced.
Overlap with our Lemmas 6.4–6.6 is ancestral only, and Open Problem 6.2
sits exactly on the tracial side of our limitations section — the existing
tex description is accurate.

CORRECTION (hallucination caught): the earlier fetched summary attributing
to Thom 2010 a "(T)-flavored central element invisible to
finite-dimensional representations while hyperlinear" phenomenon was NOT
supported by the direct read.  Thom 2010 is cited only for the
Cornulier–Abels–Thom base-group machine.  Lesson reaffirmed: every
attribution-critical claim gets primary-source verification by direct
reading before it enters the manuscript.

## Fourth pass (2026-08-12): unattributed machinery and proof-strategy audit

This pass searched by proof device rather than theorem statement.  It also
reopened every broad priority sentence affected by those devices.

### Major priority correction — APPLIED

The manuscript's old wording made Theorem D sound like the first negative
solution of the general Blackadar–Kirchberg MF problem.  That is false.
The failure of Connes embedding supplied by Ji–Natarajan–Vidick–Wright–Yuen,
*MIP*=RE* (arXiv:2001.04383), already implies a separable stably finite
non-MF C*-algebra.  Goldbring, *Model theory and ultrapower embedding
problems in operator algebras*, Corollary 5.2, states and proves the direct
deduction: a non-R^omega-embeddable II_1 factor cannot embed as a C*-algebra
in an ultrapower of the universal UHF algebra; a separable elementary
subalgebra gives the required counterexample.  Schafhauser–Tikuisis–White,
*Nuclear C*-algebras: 99 problems* (arXiv:2506.10902), independently records
the same status.

The defensible new C*-algebra statement is narrower and more concrete:
C*_r(E) is a reduced group C*-algebra, attached to the explicit finitely
presented non-MF group, with faithful canonical trace, and is not MF.
Shulman's March 2026 introduction explicitly says that no full or reduced
group C*-algebra was then known not to be MF.  The abstract, introduction,
Theorem D title, external-input accounting, and nonnuclearity remark have
all been rewritten accordingly.  The proof of Theorem D remains elementary
once Theorem A is known; the new citations correct priority, not a proof
dependency.

### Foundational analytic lineage — APPLIED

The operator-norm-lifts -> conjugation representation -> Hilbert–Schmidt
almost-invariant-vector step has a deeper lineage than the already-cited
Dadarlat/Ozawa–Thom application.  Bekka's 1990 theory of amenable unitary
representations makes the conjugation action on Hilbert–Schmidt operators,
equivalently pi tensor conjugate-pi, a central object.  Bekka–Valette 1993,
Theorem 1, ties property (T) to the resulting finite-dimensional
subrepresentations/weak-mixing obstruction.  The manuscript now names this
foundational layer, while retaining Dadarlat Lemma 3.18 and Proposition 3.19
as the closer operator-norm approximation predecessors.

### Clifford/cocycle correction — APPLIED

The construction incorrectly called its cocycle "intersection parity."
The displayed multiplication actually uses the ordered-inversion cocycle
nu(F,G) = #{(x,y) in F x G : y < x}.  Its commutator form, not its
multiplication cocycle, is determined by
(-1)^{|F||G|-|F intersect G|}.  This was a real mathematical description
error, not merely missing credit.  The text now uses the exact cocycle and
calls the group a Clifford 2-group.  It also points locally to Slofstra
Section 2, where the same finite- and infinite-rank Clifford groups and
distinguished central sign occur, rather than relying only on a generic CAR
reference.  Mermin–Peres/Pauli-group history was considered but is too
distant from the actual algebraic construction to improve the attribution;
Slofstra is the direct predecessor.

### Scaling-machine and metric correction — APPLIED

Direct comparison with Cornulier and Thom shows that Z^3 semidirect SL_3(Z)
with scaling by 2 should be described as an elementary integral *analogue*
of the Cornulier–Abels scaling pattern, not literally as a member of their
specific matrix-group family.  The old follow-up sentence also put all of
Thom's arguments in permutation/Hamming models; this was overbroad.
Thom's conclusions include both sofic (Hamming) and hyperlinear (tracial
Hilbert–Schmidt) approximation.  The manuscript now says exactly that and
contrasts both with the present operator-norm corona mechanism.

### Other unusual credit categories checked

* The finite-normal-subgroup average |F|^{-1} sum_F Theta(f) is the standard
  finite-group averaging/Reynolds projection onto F-invariants.  Naming this
  as standard machinery is appropriate; no research-priority claim or
  special citation is warranted because the manuscript proves all required
  identities inline.
* Theorem B's passage from one-sided inclusion to equality by dimension is
  an elementary finite-dimensional shadow of the same compression paradigm
  credited to OpenAI/Kun–Thom.  Searches found no closer theorem whose proof
  is being reused.  The manuscript already disclaims novelty for the
  paradigm and claims only its marked-kernel deployment.
* The central corner is directly preceded by the negative-eigenspace cuts in
  Slofstra–Vidick.  Bachner--Dogon--Lubotzky Proposition 1.5 is closer still:
  it rounds a central involution, passes to its nonzero negative eigenspace,
  changes the matrix dimension to that corner, and polar-corrects the
  compression.  Thus eliminating a positive relative-rank requirement by
  changing matrix size is prior art and must not be claimed as novel here.
* Bachner–Dogon–Lubotzky, Proposition 1.6, is a particularly close item that
  the earlier passes had cited only generically: for a finitely generated
  group Lambda with finite normal N and hyperlinear Lambda/N, MF-ness of
  Lambda implies hyperlinearity.  Thus finite normal extensions were already
  being used to cross the operator/Hilbert–Schmidt boundary.  Their argument
  does not kill N; the present proof instead combines the corner with the
  one-sided Kazhdan compressor and stable finiteness to kill the finite
  subgroup universally.  This distinction and the precise proposition are
  now stated in the prior-work section.
* The same paper has two further local antecedents that should be cited at the
  analytic step, not merely in the introduction.  Proposition 2.4 compresses a
  Schatten-`p` asymptotic representation to an almost-invariant projection and
  polar-corrects the compressed maps; this includes `p = ∞` and is directly
  adjacent to the finite-stage negative-corner construction.  Proposition 1.5
  uses central-involution rounding, the nonzero negative eigenspace, and that
  compression to show that operator--Hilbert--Schmidt stability would obstruct
  MF for a Deligne-type group.  Neither result supplies the present theorem:
  Proposition 1.5 assumes the unresolved stability input, while Proposition 2.4
  supplies only the compressed asymptotic representation, not the subsequent
  Kazhdan one-sided-inclusion, stable-finiteness pinning, or universal marked
  kernel.  Cite Proposition 2.4 beside the corner/polar-correction discussion
  and Proposition 1.5 in the operator/HS-boundary paragraph.
* Bachner--Dogon--Lubotzky Lemma 2.2 records exact involution rounding for every
  unitarily invariant norm (with the bound by `‖1-A²‖`), citing DGLT Proposition
  1.4; Lemma 2.3 records the corresponding polar correction.  These are useful
  historical anchors for the elementary analytic sublemmas.  The corner and
  dimension change do occur there; the Kazhdan compressor, stable-finiteness
  pinning, and unconditional universal marked kernel do not.
* The MF-radical/largest-quotient construction remains structural folklore,
  with Slofstra's finite/finite-approximate kernels and
  Nikolov–Schneider–Thom approximation kernels as the proper conceptual
  anchors.  The manuscript already makes no novelty claim for the universal
  quotient argument.
* Kazhdan's 1982 epsilon-representation paper was checked as historical
  background for operator-norm stability, but the present proof neither uses
  finite-group stability nor reproduces its argument.  Adding it would imply
  a false dependency and was rejected.

### Access record

Goldbring's De Gruyter chapter page is paywalled, but its complete author
preprint (arXiv:2210.01223) was accessible and Corollary 5.2 was checked in
full.  The complete arXiv versions of MIP*=RE, Schafhauser–Tikuisis–White,
Shulman, Cornulier, and Thom were accessible.  Springer metadata for Bekka
and Bekka–Valette was cross-checked through DOI records and institutional
indexes; the publisher-hosted full articles were not openly retrievable in
this session, so the precise theorem-level statement was cross-validated
against later primary papers that quote Bekka–Valette Theorem 1.  No
unverified content from an inaccessible source was used as a proof premise.

## Addendum, 2026-08-14 (evening): Kun–Thom v3 §5 antecedent of the OAI median device

Source: arXiv:1901.03963v3 (revised 2026-08-04, "Added Section 5, changed
the introduction"), Section 5 read in full from the PDF; details and quotes
in `notes/scout-2026-08-14.md` §C2.  This addendum records an attribution
fact about the two *sofic-side* August papers; it does not touch any
attribution used by the manuscript, and this repository claims nothing in
that lane.

* The OAI chapter's expander-matching proof (Prop 2.3, current version)
  normalizes component sizes by `f(z) = M(z)/(M(z)+mu)` with `mu` a median
  of the Γ-component sizes.  KT v3 §5 contains the same median device:
  Claim 5.4 ("Let m denote the median size of the Γ-components") proves the
  proportion of vertices with component size outside `[(1-ε)m, (1+ε)m]`
  tends to zero, supported by Claims 5.2–5.3 (bad/unbalanced edges are
  negligible; each boundary edge of a bad configuration makes a length-four
  commutator walk fail to close).
* Timing, from the v3 introduction verbatim: the paper "was mostly written
  in 2018 … We finally finished writing it by mid July 2026" — i.e. §5
  predates the 2026-08-01 OAI announcement — and the authors "spoke about
  the results of Section 5 on various occasions over the last years".  The
  same introduction describes the OAI Prop 2.3 proof as "a creative and
  effective application of the results and techniques of this paper".
* Consequence for this audit: the earlier sections of this file credit
  Kun 2016 / Kun–Thom 2019 for the (T)-rigidity engine and predate v3.
  The median-normalization step of the OAI argument now also has a
  documented pre-announcement Kun–Thom antecedent.  No change to the
  manuscript is required; if the manuscript ever discusses the OAI
  argument's provenance, cite KT v3 §5 alongside it.

## Addendum, 2026-08-14 (late): Shulman quote discipline and the full/reduced strengthening

Two paper-facing items surfaced during graph work (cairn-archivist
verification; cairn-quotient-mf artifact
`notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md`,
verbatim source record `research/artifacts/shulman-2603-13564-verified.md`).

* **Quote discipline for the Shulman priority sentence.**  The sentence
  from Shulman's introduction carries the trailing clause "at least in
  the case of full group C*-algebras", which one internal relay dropped.
  Any use must quote the full sentence from the verified artifact file,
  never from a message.  The defensible phrasing is: "Shulman records in
  March 2026 that no such example was **known**" — not "existed".
* **Strengthening available with no extra trust surface**: "neither
  `C*(E)` nor `C*_r(E)` is MF" follows in one step by contraposing
  Shulman's own bridge lemma against the repository's
  `literal-group-fails-mf-conventions`, with no appeal to the
  repository's reduced-algebra work.  If the manuscript's impact
  discussion is revised after the freeze lifts, this is the correct
  citation-economical route to the reduced-algebra statement.

## Addendum, 2026-08-15 (priority-risk check): the Dadarlat "MF ⇒ weakly quasidiagonal" chain

A graph agent (cairn-torsionfree) flagged a chain in Dadarlat,
arXiv:2007.12655 (Adv. Math. 2021) that, if valid, would be a published
non-MF criterion predating this repository's mechanism.  Checked directly
against the arXiv PDF via pdftotext (2026-08-15); verbatim findings:

* The paper's MF definition (its (1),(2)) is exactly the CDE/Shulman
  notion this manuscript uses: unitary-valued asymptotic homomorphisms,
  per-pair operator-norm defect → 0, per-element separation limsup > 0.
  Immediately after, verbatim: "It is an open problem to find examples of
  discrete countable groups which are not MF."
* Intro, one page later, verbatim: "It is clear from definitions that MF
  ⇒ weak quasidiagonality" — where weak quasidiagonality (Def. 3.10)
  requires *exactly* completely positive definite maps at each n
  satisfying (1),(2).
* Prop. 3.19 (attributed Ozawa–Thom; "essentially pointed out by Thom on
  MathOverflow"): an infinite property (T) weakly quasidiagonal group has
  an infinite residually finite quotient.  Proof in-paper (Kazhdan
  projections + Malcev).  Preceding text, verbatim: "It shows that an
  infinite simple property (T) group G is not weakly quasidiagonal.  As
  explained in [35, p.93] any lattice in Sp(n,1), n ≥ 2 has uncountably
  many infinite quotients which are simple (and torsion)"
  ([35] = de la Harpe–Robertson–Valette).
* The three bullets together would yield "explicit infinite simple (T)
  groups are not MF" — contradicting the same paper's own open-problem
  statement, Shulman (March 2026), and BDL (2026), none of whom draw the
  conclusion.
* **Assessment (recorded, not yet refereed):** the chain breaks at the
  intro's "clear from definitions".  An asymptotically multiplicative
  unitary-valued map is only *asymptotically* completely positive
  definite per finite set; weak quasidiagonality demands *exact* complete
  positive definiteness at every n over all finite sets simultaneously,
  and no conversion is given.  MF and weak quasidiagonality are different
  predicates (unitary vs exactly-cpd approximations), so Prop. 3.19 does
  not transfer to MF.  Consequence for priority: the chain is NOT a
  citable prior non-MF criterion, and the manuscript's framing is
  unaffected; in the residual case that a proof of MF ⇒ wQD exists, the
  affected statement would be the broad existence framing only — the
  headline (finitely presented; stable-finite Kazhdan pinning) is
  untouched, since the simple-(T)-quotient route can never reach finite
  presentation.  A specialist reviewer should see this addendum; it is
  also potential erratum-level feedback on the cited paper's intro remark.

## Attribution: Francesco Fournier-Facio

His observations, and what they do and do not cover.

**His.**

1. **Removing the distinguished-mover hypothesis.**  The circulated criterion
   assumes `Γ = ⟨H, γ⟩` and uses it in exactly one place, to get
   `δ_n(g) ≤ C_g k_n`.  Replacing the single `γ` by finitely many `γ_1, …, γ_m`
   generating `Γ` over `H` and normalizing by `k_n = max_i d_n(x_0, γ_i x_0)`
   is his.  Lean: `Sofic/MaxDisplacement`, `Sofic/MoverGeneration`.
2. **The reduction to a non-co-Hopfian property-(T) group** — that once (iii)
   is gone, a proper injective self-embedding of a Kazhdan group is the whole
   structural input.
3. **The ascending HNN extension as the prototypical construction**,
   `G = ⟨Γ, t | t γ t⁻¹ = α(γ)⟩`.  Lean: `Sofic/AscendingHNNStabilizer`.
4. **The framing that the ambient group need not have (T)**, in contrast with
   the ambient-(T) Kun--Thom examples.

**His, with the theorem elsewhere.**

5. **Amenability of `G ↷ G/Γ`** is Monod--Popa (arXiv:math/0301348); he pointed
   out that it applies here via `N = ⋃ t^{-n} Γ t^n`, `G = N ⋊ ⟨t⟩`.  Lean:
   `Sofic/AscendingHNNFolner`.
6. **Soficity of the coset action** is his question.  Wording for what we
   prove: "answers, under the stated hypotheses, a question of Francesco
   Fournier-Facio."  Lean: `Sofic/AscendingHNNCosetActionSofic`.
7. **The role of the three metrics** — the organization
   `operator norm → rank → Hilbert--Schmidt → (T)` was prompted by his
   question.  Lean: `Sofic/InvolutionRankMass`.

**Ours.**  The telescope radical and the exact radical computation, the
five-way residual coincidence, universal factorization, the perfect-lamp and
`A_5` results, finite-index radical heredity and commensurability invariance,
profinite twins, the noncommensurable `A_n` family, the split-extension
counterexample, non-finite-presentability, and the concrete affine model.
Also the norm-corona implementation of (1): his formulation passes to the
argmax subsequence, and subsequential vanishing is not vanishing in a
`c₀`-corona, so the finite-family block amplification replaces that step.

**Draft acknowledgement.**

> We thank Francesco Fournier-Facio for observing that the distinguished-mover
> hypothesis in the original collapse argument should be unnecessary: one may
> instead choose finitely many movers generating the Kazhdan subgroup modulo the
> stabilizer and normalize by their maximal displacement.  He also pointed out
> that this reduces the basic construction to a non-co-Hopfian property-(T)
> group via its ascending HNN extension, emphasized the resulting examples in
> which the ambient group is not property (T), and raised the question whether
> the associated coset action is sofic when the base group is sofic.  His
> comments also prompted the conceptual separation of the operator-norm, rank,
> and Hilbert--Schmidt roles in the proof.
