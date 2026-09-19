# bh-g2-abh — gate E2 on F_n×Z (ABHT path-fold), 2026-09-18

Status: done (one-shot fork after the coordinator restart). No unlanded drafts from any earlier instance: the work dir was empty.

Landed 3c8b41742 (lane proof, elementary, algebraic, unreviewed):
- path-fold-rigidity-transfer-proof (new route).
- path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid: OPEN → ESTABLISHED.
  - Centrality (C) proved: every flow idempotent is central, via one-step commutation transport along the backward-arrow chain, using that the flow is t-invariant.
  - Then coherence (letters at equal horoheights are equal) and a section family for X. X-rigidity finishes the proof.
  - Scale: D ≥ max(2D_X, R+1). Valid for any field and any dimension.
- With the fold lemma (cc93f9797): Z rigid ⟺ X rigid.

Single-free-branch test: passes. A slab contains a full row, which fixes the fibre, so only the flow varies, and only in the end's branch.

Open next (for other lanes):
- Is ABHT's fibre X_0 (Labbé–Mann–McLoud-Mann, rotated) quantum rigid? This is now the whole E2-over-F_n×Z question along folds. Fault slabs probably block determinism-closure proofs (unchecked for X_0), so a self-similar scale certificate is the way in.
- Chain transport for Busemann transplants (C). It needs germ idempotents that are invariant along the deterministic tile direction, plus germ chains along cones.
- H×F_n version: stated as a remark, with the same proof. It is not written as a separate node.

**From bh-g2-labbe (09-18 evening): window-algebra method for E2, for reuse.** Nodes on main (cc1e8896b):
`contextual-closure-certifies-quantum-rigidity`, `labbe-scale-two-commutation-crosses-faults-at-distance-five`.
Scripts: `research/artifacts/gq-bh-g2-labbe-j2-contextual-probe.md` §8. MSI:
`/projects/standard/hsiehph/sauer354/bh-g2-labbe/{j2probe,wallsearch,cliquectx}.py`. Everything takes a box language, so
you can plug in yours, e.g. X_0's legal s×s patterns or a DRS face language.
- **Certificates (sound).** A case split over a commuting context S ⊆ T ∩ T', where T ∋ 0 and T' ∋ v are sets whose
  pairwise offsets are already certified. Patterns on T are admissible: every box B meeting T, even sticking out,
  restricts to something extendable to a legal box. If every S-pattern leaves 0 or v determined, then [P_0, P_v] = 0.
  - This crosses fault slabs, where determinism cannot. It is blocked only by double faults.
  - Iterate it with the determinism (w)/(z) steps.
- **Obstructions (exact).** A "window wall": two K-patterns, legal on the boxes inside K, whose difference set splits
  0 and v, differing at both. It is a 2-dim representation of the window algebra C_D(K), so no certificate of ANY
  degree is supported in K. Exact search: chains y–z–x, grouped by restrictions near each end.
- **Use for X_0 (bh-g2-abh).** Compute X_0's s×s language and run the determinism closure, then walls, then clique
  contexts. If X_0 is a toral coding, expect axis offsets to cross at small distance and resonant offsets along fault
  normals to need windows of about 2.5–3 × |v|.
- **Use for FLEF (fixedpoint-a).** An edge wall is a window wall at scale 1. A "contextual FLEF gadget" is exactly a
  context split in which the face context determines one end.
- **Warning.** A Gröbner run on C_D cannot terminate (one commutation orbit per displacement), so use window algebras
  instead.

## Pass 2 (coordinator follow-up, 2026-09-18): is ABHT's fibre X_0 rigid?
Landed 9b2f42860 (lane proof plus imports, unreviewed). No MSI jobs and no computation; the stray MSI ls/find I had started was killed.
- Import (sources read as PDFs): jeandel-rao-minimal-subshift-is-morphic-image-of-labbe-shift + jeandel-rao-substitutive-structure-citation. Sources: Labbé DCG 2021 Thm 3 and Cor 5; LMM DCDS 2023 (X_0 is an SFT, its 4 nonexpansive slopes, Thm 4.1); ABHT's X_0 is this X_0.
- recognizable-morphisms-give-kakutani-equivalent-z2-groupoids (+ proof): a recognizable morphism onto up to a shift is a Kakutani equivalence. With steinberg-fp-is-a-kakutani-invariant, finite presentation and rigidity pass in both directions.
- jeandel-rao-minimal-subshift-is-quantum-rigid-iff-labbe-shift-is: X_0 ⟺ Ω_U ⟺ J_2(Ω_U)=0 ⟺ ABHT's Z on F_n×Z is rigid.
- path-folds node (refereed PASS by bh-ref-kourovka-a, cb53a036f): added a pointer to this.
- Fixed-point edge-family criterion (0e750fc93): not applicable, since no side-local self-simulation exists here. Its edge-wall test is a first-order screen for bh-g2-labbe, but a refutation would need the analogue of its item 2 for non-side-local morphisms (open).
Open next: J_2(Ω_U)=0 itself (bh-g2-labbe). Also whether LMM's irrational-direction worms give X_0 a second fault normal (determinism no-go for X_0).

## Pass 3 (coordinator: bypass J_2 via the crossing-wire shift), 2026-09-18
Landed c05f7793b (lane proof, unreviewed):
- abht-path-folds-accept-exactly-expansive-rational-half-planes (+ one-sided-path-fold-acceptance-proof).
  - Faithful fold ⟺ −e_2 determining (n≥2). Up to GL_2(Z), the accepted fibres are exactly those with a rational determining normal.
  - Transfer of freeness, minimality and rigidity; the rigidity-up proof uses only the downward rule.
  - Corner determinism suffices; Ledrappier folds but is not horizontally expansive.
- foldable-free-minimal-quantum-rigid-z2-sft-exists (OPEN target). Payoff: F_n×Z (no J_2), plus Ã2 transplants.
Assessment of 49939b957: as landed it is NOT corner-deterministic, and its foldability is undecided. Heuristically, side-local margins block the axis normals (just-below-margin chains see only top colours).
SPLIT for bh-g2-fixedpoint-a: aim for the A4 variant with SW-deterministic GROUND tiles, not horizontal expansivity. Folding is then immediate by item 5, and my transfer gives a minimal free rigid SFT on F_n×Z.

## Pass 4 (coordinator: final-form fold theorem), 2026-09-18
Landed c06e85518: fold-transfer-theorem-for-fibres-with-a-determining-half-plane + fold-transfer-theorem-proof. Also corrected the acceptance node and the OPEN target: (D) at one macro level suffices, not at ground level.
Ready to apply: once bh-g2-fixedpoint-a / bh-invent-04 land a corner-deterministic (at some level) free minimal rigid fibre, cite (D) and items 2, 3, 4, 6. Status: idle.
