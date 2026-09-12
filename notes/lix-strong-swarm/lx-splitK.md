# lx-splitK — the splitting principle over K, narrowed (successor of lix-evenside, input (d))

Owns `CharClass/ChernSplitting*`, `ChernSplit*`, `ChernGamma*`, `ParityP*`, `StepDModP*`, `Wu*Of*`.  Clone lix-h.

## RULINGS USED
- lx-design (09-12): producers cannot owe P⁰ = id on every class → NARROWED twins in new files, green ones untouched.
- Ownership split with lx-sliceK: I declare (i)–(v) of lix-evenside's input (d); lx-sliceK does V-specific slice material.
- Reduced powers consumed on EVEN PARTS (lx-pzero's `OddPTotal.EvenReducedPowers p`).

## GREEN
- Probe 0912-105534-9005 (lix-h, acn112 slot 0, base 3733b381b): PROBE GREEN, 9233 jobs, 6 BUILT / 6 COMPILED, no errors:
  `ChernSplittingOfFlagRelation`, `ParityPWuCartanNarrow`, `ParityPWuTransportNarrow`, `ParityPDataNarrow`,
  `ParityPSplitStepDNarrow`, `ChernSplittingOfCompact`.  Evidence `lanes/lx-splitK.green.0912-105534-9005`; bytes = origin
  (c22060a2f, 3733b381b).
- Peer evidence: `ChernEulerIsoOf` green in lx-lhK-b's probe 0912-101304-26799 (input (ii) consumes it).

## AUTHORED, UNVERIFIED (landed per rule 5')
| module | contents | landed |
|---|---|---|
| `ChernSplittingOfFlagRelation` | (i) `lineEulerOfK`, (ii) `eulerOf_restrict_eqOf`, (iii) `pull_factor_eq_zeroOf`, (iv) `coe_prod_range_evenPart`, (v) `splitRelation_of_sumOf`; `ChernSplittingOf.splitRelation_flagOf`, `tautCompat_flagOf`, `hasSplittingP_flag_ofGraded` | c22060a2f |
| `ParityPWuCartanNarrow` | `ParityP.PowerDataN` (`p_zero_y`, `p_zero_one`, `p_one_pos`, `cartan_y`), `p_zero_prod`, `p_mul_y`, `p_prod`, `p_gamma_succ_eq_smul` | landing |
| `ParityPWuTransportNarrow` | `ParityP.wu_isDecomposable_of_splittingN`, `wu_field_of_splittingN` (hP only at γ (i+1)) | landing |
| `ParityPDataNarrow` | `ParityPDataN` (`pH_z_mul_zero : PR i r = 0 → PH i (z * ι r) = 0`), `ParityP.pH_z_mul_zero_of_cartan`, Step D chain copy incl. `gamma_top_eq_zero_of_slice` | landing |
| `ParityPSplitStepDNarrow` | `ParityP.HasSplittingPN`, `.elim`, `SplitStepDDataN`, `toParityPDataN`, `gamma_top_eq_zero` | landing |
| `ChernSplittingOfCompact` | `SplittingDataOf.powerDataN`, `hasSplittingPN_of_splittingDataOf`, `nontrivial_evenPartOf`, `ChernSplittingOf.flagRootOf`, `hasSplittingPN_flag_ofGraded`, `CompactLerayHirschDualOf`, `flagRest_pull_injectiveOf`, **`hasSplittingPN_of_compact`** | landing |
| `ChernSplittingOfOpsAdapter` | `one_eq_evenOf_one`, **`hasSplittingPN_of_compactOps`** (from `OddPTotal.EvenReducedPowers p`) | next |
| `ChernSplittingOfLix` | **`KGen.hasSplittingPN_lixBundleOf`** (the real mapping-torus bundle) | next |

## NEEDS
- lx-lhK-b: `LH.lerayHirschGraded_compactDualOf (K) [Field K] [CompactSpace X] [Nonempty X] q s hs hs1 hgen hgen0` (closed form) → bridge `compactLerayHirschDualOf_of_ne_zero` (one-liner; owner to agree).
- lx-pzero: `OddPTotal.EvenReducedPowers p` producer; if `zero` narrows, keep P⁰ on degree-two classes + P⁰1 = 1.
- lx-slice2: narrowed `Gen.ModPStepDDataN` twin consuming `ParityPDataN`.
- lx-torusP / lx-bundleP: narrowed `realWu_of_splitting` = one application of `wu_field_of_splittingN` via `HasSplittingPN.elim`.

## SPLIT (independent sub-tasks a helper could author)
1. `realWu_of_splittingN` (file `CharClass/LIXStepDGenRealNarrow.lean`, lx-torusP prefix): the RealBundleModP `wu` field from `HasSplittingPN p Γ (fun i => evenRestrictAdd (T.PN i) (T.PN_even i)) m` — `HasSplittingPN.elim` + `ParityP.wu_field_of_splittingN hp (evenMap K pY) D ρ hρ Γ hγ PH hP m hκ i`.
2. `Gen.ModPStepDDataN` + `toParityPDataN` (file `CharClass/LIXStepDGenModPNarrow.lean`, lx-slice2 prefix): `pH_zero`/`cartan`/`pH_z` → `pH_z_mul_zero`; conclusion via `ParityPDataN.gamma_rank_eq_zero`.
3. `ChernSplittingOf.compactLerayHirschDualOf_of_ne_zero (K) [Field K] (hgen) (hgen0 : hgen ≠ 0) : CompactLerayHirschDualOf K ι hgen := fun Z _ _ _ q s hs hs1 => LH.lerayHirschGraded_compactDualOf K q s hs hs1 hgen hgen0` (needs lx-lhK-b's closed theorem).

## TRAPS
- `git grep -E` has no `\b`; use `-P`.
- zsh colon modifier: `git show "$B:Palomar/…"` loses `:P…`; write `"${B}:path"`.
- `LerayHirschGraded.pull_injective (L) (hr : 0 < r) (n)` is K-generic (LerayHirschDegree:155) — the per-stage injectivity needs no new lemma.
- `ParityPData.pH_z_mul` and `PowerData.p_zero_apply` force normalised P⁰ everywhere; use the `…N` twins.
