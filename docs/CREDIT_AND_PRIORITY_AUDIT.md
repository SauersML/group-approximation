# Credit and priority audit for the non-MF manuscript

Date: 2026-08-12 (user-supplied adversarial literature audit; time-sensitive:
the adjacent sofic breakthrough is six days old).  These are PAPER-facing
facts and directives.  Nothing here enters Lean as a premise; the Lean
development remains zero-premise and claims correctness, not novelty.

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

## Mandatory manuscript corrections

1. HISTORY/PRIORITY FIX (currently wrong in the tex): the first nonsofic
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

## Checked non-collisions

* Theorem B (finite-dimensional sterility) does not trivialize A: no
  "finitely presented + MF ⟹ RFD/MAP" implication exists (CDE's Abels
  example blocks it).
* No hidden C*-algebra corollary: only the one-way implication
  "C*(G) or C*r(G) MF ⟹ G MF" is on record (Shulman); the group-level
  theorem is strictly stronger content.
* GitHub search surfaced only this repository, no external predecessor.
