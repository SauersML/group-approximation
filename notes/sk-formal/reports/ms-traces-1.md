# Lane ms-traces-1: `simple_kazhdan_sofic_group.tex`

Lead: session nonsofic-existence-06 (main). The census is `metadata/SK_SENTENCE_CENSUS.tsv`, and my row file is
`metadata/sk-census-rows/ms-traces-1.tsv`.

## Item 1 (main, 09-14 ~09:40): sec:lef rows, l.288–338

Census 9cb80166d, tip 8b36733d7 (md5 29d63f7944bccccbf9a91b0b2714c0b4). The key split was agreed with
sk-lef-assembly: it keeps 022271399cfb (cor:lef) and 9b1a6e7489a1 (cor:host).

| key | lines | status | carrier or reason |
|---|---|---|---|
| 83394521b2d5 | 288 | attribution | the Kionke–Schesler question |
| fd312b860bb5 | 291–295 | attribution | the parallel with Boone–Higman in Thompson's form |
| 2745cd64eada | 316 | attribution | lead-in to the two known-host sentences |
| 8212b1470040 | 316–321 | attribution | Kionke–Schesler Theorem 1.2 with Wilson; the "so …" clause needs those cited theorems, which the note does not prove (main's ruling) |
| fc84c012b409 | 321–325 | attribution | Gorjuskin–Schupp, Coulon–Fournier-Facio Theorem 1.5 and Higman; the same ruling |
| d00f0309aff7 | 336–338 | formalized | `printedCommutatorMultipliesFirstCoordinate` (sk-lef-ultra, `#audit_closed_axioms`), proved by `LevelCommutatorWords.commutator_fPerm_tPerm` (174130833) |

LANDED 53e1897cb.

## Item 2 (main, 09-14 ~10:10): Questions block, row 7d13cf4208bc

Sentence (l.525–526): "If (X,T) is topologically conjugate to (Y,T′) or to (Y,T′⁻¹), then G_X ≅ G_Y."
ms-traces-3 keeps 1c40d21401f6 and dc73886fdc13.

CLAIM census row 7d13cf4208bc.
- The carrier already exists, so this lane builds nothing. ct-involution's `printedConjugacyIsomorphism`
  (`Manuscript/SimpleKazhdanSofic/CrossedProductConjugacy`, 730da5240) is root-imported and `#audit_closed_axioms`,
  and it follows the printed route: `conjRingEquiv` (f ↦ f ∘ φ⁻¹, u ↦ u), `flipRingEquiv` (u ↦ u⁻¹),
  `nonempty_ringEquiv_of_conj_or_flip`, then `nonempty_elementaryGroup_equiv_of_conj_or_flip`.
- If its generality falls short of the printed sentence, the gap goes in
  `GroupApproximation/Manuscript/SimpleKazhdanSofic/ConjugacyIsomorphismGeneral.lean`.
