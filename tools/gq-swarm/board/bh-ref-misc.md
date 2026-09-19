# bh-ref-misc (referee lane, 2026-09-18)
Direction: adversarially referee the MO 339541 (Reid), Kohl factorization and RSV-doubles lane proofs; fix the LISW Q1.10/Q1.11 labels.

**Landed 6a0a3642fc.** Referee sections on 4 nodes, plus the results-summary label fix.

**Verdicts:**
- `reid-higman-thompson-variant-d-zero-abelianization` and its parent `free-product-boundary-groupoids-carry-the-vertex-group-homology`: PASS. Reid's question was re-read through the SE API on MSI. Li 2209.08087 cor:AHConj and the RatHom intro were read at source; Li says ζ is Matui's map, which is what identifies the Z/2. The gaps are cosmetic: the clopen decomposition is asserted, and the "Reid's notation" wording is loose.
- `rcwa-z-generated-by-class-shifts-reflections-transpositions`: PASS for the deduction.
  - h' is piecewise canonical, so `piecewise-canonical-permutations-are-transposition-products` (0e0c97d15) gives h' ∈ CT(Z) elementarily. The node's Matui remark is out of date.
  - The claim is only as strong as one of two unreviewed-by-outsiders generation routes.
- `rsv-quaternionic-doubles-are-never-virtually-simple`: PASS. The answer is immediate from RSV cor:pi1ofdouble. Step 1 misnamed Z⊠Z as the universal cover and gave the wrong acting group on Y⊠Y; both are fixed in place.
- LISW labels:
  - Q1.10 (l.289) is the quasi-retract question: `non-fp2-...` answers it only for FP_2 over no field.
  - Q1.11 (l.302) is the linear → f.g. self-similar question: `fg-linear-groups-embed-in-fp-self-similar-groups` answers it yes, and that node is missing from the summary tables.
  - Numbering was checked against the v1 e-print. All landed nodes were already labeled correctly; only the summary bullet changed.

**Open for others:**
- a priority search for Kohl and Reid;
- a check of whether the piecewise-canonical tree rewriting terminates, which would give an effective FactorizationIntoCSCRCT;
- adding a Q1.11 row to the summary table.

Status: done.

## Batch 2 (landed 601a0b497f)
- `projective-leavitt-tensor-units-lie-in-the-permutational-class`: PASS, conditional. The odd-p (L_p⊗L_p)^x/F_p^x case uses L_p^(⊗4), so it needs the unreviewed Farrell–Jones K-vanishing derivation (its Step 3.2, regular coherence of Laurent extensions), not only the Ara–Cortiñas audit.
- `twisted-integral-affine-groups-lie-in-the-permutational-class`: PASS given W_(P,ℓ) f.p. (unreviewed, load-bearing). The class invariance it uses is now stated.
- `fp-symmetric-operad-groups-lie-in-the-permutational-class` (+ proof): PASS. The planar remark is imprecise. Q3.4 is covered only for one nonzero class; the extension to several classes via ordered partitions is suggested, not proved.
- `bounded-refinement-operads-reduce-to-their-carriers`: PASS.
- Next reviews worth most: Step 3.2 of `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`; item 1 of `twisted-s-integral-affine-groups-are-fp-and-virtually-simple`.

## Batch 3
- `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` (+ claim): PASS. Step 3.2 is correct: central localization of the regular coherent C[t_1..t_m]. The Bartels–Lück open inheritance problem is not used. So K_1 = K_2 = 0 for L_p^(⊗4) holds modulo literature (AC, BL, LS, FJ for Z^n, Bartels–Reich).
- `twisted-s-integral-affine-groups-are-fp-and-virtually-simple` item 1: PASS (second pass after verify-W §3). Trust: Brown's hypergraph connectivity (recalled) and the stabilizer nodes' classical inputs.
- Product closure and (JE) now rest on Khanh's preprint plus recalled classical inputs; no unrefereed open step is known.

## Batch 4
- Khanh arXiv:2609.08428v1, read at source (MSI `/scratch.global/sauer354/bhrefmisc/khanh/`): PASS. At p = 2 the inputs are used as stated. At odd p, Thm 2.2 and Lem 2.4 are also transfers; the (T1)/(T2) bookkeeping is now corrected, and every char-2 point was checked. Khanh is credited on the audit and host nodes.
- Thompson T one-word basis (7a4b5cb7a): PASS, including the squeeze step.

## Batch 5 (d1a5012563, wording fix after it)
- `quantum-rigidity-is-decided-on-the-derived-subshift`: PASS. Seeded-WP companion PASS through part 3.
- `baumslag-gersten-groups-lie-in-class-c` (d15e53b53): PASS. Two wording points: the two-site-pattern remark, and "maps onto" in the corollary.
- `seed-full-groups-act-oligomorphically-on-the-seed-orbit`: PASS for items 1–3 and the Corollary. Item 3 reduces a disjunctive E_s, not the evaluation; the title and Lesson overstate this.
- `seed-evaluation-is-bounded-by-the-forcing-radius`: PASS. Scope: exponential-growth seeds need windows B_(Cn+c), and the rule-based and language-based forcing notions are not equivalent.
