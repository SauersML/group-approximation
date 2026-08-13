# Credit and priority audit for the non-MF manuscript

Date: 2026-08-12.  This began from an adversarial literature review and was
then checked against the cited primary papers, including theorem-level checks
of every attribution added to the manuscript.  The adjacent sofic
breakthrough is six days old, so the audit remains time-sensitive.  These are
paper-facing facts and directives.  Nothing here enters Lean as a premise;
the Lean development remains zero-premise and claims correctness, not novelty.

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

## Manuscript corrections implemented

1. HISTORY/PRIORITY: the first nonsofic
   group is OpenAI's; Kun–Thom (arXiv:2608.06222, posted 2026-08-06)
   explicitly build on it and extract/generalize the mechanism.  Do not say
   the sofic case "was solved negatively by Kun and Thom" without the
   OpenAI attribution.
2. METRIC FIX: sofic approximation is the normalized HAMMING/permutation
   metric, not "rank metric".  Shulman states the three metrics: operator
   norm (MF), normalized Hilbert–Schmidt (hyperlinear), Hamming on
   symmetric groups (sofic).
3. Add a serious paragraph on OpenAI + Kun–Thom as the closest conceptual
   analogue (one-sided compression tΓt⁻¹ < Γ + property (T) + lamp
   centralizing Γ), and explain why the operator-norm argument is distinct:
   the decisive step P ≤ β(t)Pβ(t)* ⟹ equality holds because the
   conjugation representation lands in a stably finite norm matrix corona —
   a mechanism with no analogue in the permutation/Hamming setting.
4. Add Ozawa–Thom (via Dadarlat, Prop 3.19, S0001870821001602) as prior art
   for the operator-norm-lifts → Ad U on L²(Mₙ) → property-(T) fixed
   vectors maneuver.  It does not prove our theorem (E is not (T); Γ is
   residually finite; their output is quotient information, not a universal
   kernel element), but the analytic vocabulary is ancestral.  Cite
   prominently, not just Akemann–Walter/BHV.
5. Reframe Theorem C: "amenable MF but non-RFD/non-MAP" as a broad
   phenomenon is already covered by CDE's treatment of Abels' group
   (S0022123613001201).  Present C only as a sharp calibration: the same
   marked-sign compression pattern becomes MF once property (T) is removed.
6. Soften "genuinely a property-(T) phenomenon" to "property (T), or a
   substitute furnishing a uniform fixed-space projection, is essential to
   this argument."
7. Page 1 must say MF in the CDE–Shulman sense (embedding in the unitary
   group of a norm matrix corona); Shulman warns a stronger property has
   also been called MF.
8. Fix the CDE attribution for the "C*max fails stable finiteness under
   Kazhdan compression" remark: no precise CDE source verified.  Either
   locate a precise reference or state it as a short folklore observation
   and prove it in place.

## What to claim vs not claim

CLAIM (no predecessor found): non-MF group existence (CDE–Shulman sense);
explicit finitely presented example; the fixed marked element w ≠ 1 killed
by every matrix-corona representation ("MF radical" element); non-MF of both
C*max(E) and C*r(E) as a new corollary (Shulman explicitly noted no such
examples were known); the central-corner rank-renormalization tactic.

DO NOT CLAIM: property (T)/Kazhdan projections (classical); conjugation on
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
   characterization; generalizing Manuilov–Yu) — operator-norm almost
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
