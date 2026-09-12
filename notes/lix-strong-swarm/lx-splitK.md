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
| `ChernSplittingOfOpsAdapter` | `one_eq_evenOf_one`, `evenTautOf_pull`, `zero_pull_cpOps`, **`hasSplittingPN_of_compactOps`** (PN free + hnat; m = 1 per EvenReducedPowers v3), `…_self` | 19bb412a3 |
| `ChernSplittingOfLix` | **`KGen.hasSplittingPN_lixBundleOf`** (PN free + hnat), `…_self` (the real mapping-torus bundle) | 19bb412a3 |
| `ChernSplittingOfLHBridge` | `compactLerayHirschDualOf_of_ne_zero`, `cpGenOf`, `cpGenOf_ne_zero`, `compactLerayHirschDualOf_cpGen`, **`KGen.hasSplittingPN_lixBundle`** (compact LH discharged) | authored; lands when lx-lhK-b's `LerayHirschCompactClosedOf` is on main |

## NEEDS
- lx-lhK-b: `LH.lerayHirschGraded_compactDualOf (K) [Field K] [CompactSpace X] [Nonempty X] q s hs hs1 hgen hgen0` (closed form) → bridge `compactLerayHirschDualOf_of_ne_zero` (one-liner; owner to agree).
- lx-pzero: `OddPTotal.EvenReducedPowers p` producer; if `zero` narrows, keep P⁰ on degree-two classes + P⁰1 = 1.
- lx-slice2: narrowed `Gen.ModPStepDDataN` twin consuming `ParityPDataN`.
- lx-torusP / lx-bundleP: narrowed `realWu_of_splitting` = one application of `wu_field_of_splittingN` via `HasSplittingPN.elim`.

## SPLIT (independent sub-tasks a helper could author)
1. `realWu_of_splittingN` (file `CharClass/LIXStepDGenRealNarrow.lean`, lx-torusP prefix): the RealBundleModP `wu` field from `HasSplittingPN p Γ (fun i => evenRestrictAdd (T.PN i) (T.PN_even i)) m` — `HasSplittingPN.elim` + `ParityP.wu_field_of_splittingN hp (evenMap K pY) D ρ hρ Γ hγ PH hP m hκ i`.
2. `Gen.ModPStepDDataN` + `toParityPDataN` (file `CharClass/LIXStepDGenModPNarrow.lean`, lx-slice2 prefix): `pH_zero`/`cartan`/`pH_z` → `pH_z_mul_zero`; conclusion via `ParityPDataN.gamma_rank_eq_zero`.
3. `ChernSplittingOf.compactLerayHirschDualOf_of_ne_zero (K) [Field K] (hgen) (hgen0 : hgen ≠ 0) : CompactLerayHirschDualOf K ι hgen := fun Z _ _ _ q s hs hs1 => LH.lerayHirschGraded_compactDualOf K q s hs hs1 hgen hgen0` (needs lx-lhK-b's closed theorem).

## INCIDENT (11:20 CDT)
- origin/main tree wiped by becc912bd (peer session_01PWzwKNBr2dwjX4pucBuXff, 11:10:52): 27760 → 2 files; the 12 later
  commits (incl. swarm landings 1e52c3688, 6e3933cfb, f675e24d4, 5fda7e589) sit on the 2-file tree (tip had 17 files).
  Reported to the lead with a forward-repair recipe (read-tree ce16f64eb + later A/M paths, commit-tree -p tip).
- Until repaired: NO lxprobe (the remote delta sync `rm -f`s every path deleted in LAST..SHA, wiping clone sources) and
  NO lxland.  All lane files backed up in `$LX/backup/splitK/`.

- 11:3x CDT: main restored by 3f71a3a50 (tip f095abc5d at resume, 27817 files); halt lifted by the lead.  All 8 landed
  lane files byte-identical on main.  Bridge landing unverified (task bg25fhvq2); probe of OpsAdapter + Lix launched
  (task bc76j49ml).  The bridge is NOT in that probe: its import `LerayHirschCompactClosedOf` (with
  `LerayHirschLadderClosedOf`, `ProjectiveSpaceRingClosedOf`) is on main only as attic text (f675e24d4).

- 11:39 probe 0912-113941-38994 (lix-h, base 1a4555df7): PROBE FAILED — `ChernSplittingOfOpsAdapter` 50:64 and 88:27
  `Unknown identifier even_zero` (the pin spells it `Even.zero`, as CupOneTotal:88 does); `ChernSplittingOfLix` not reached.
  Fixed (both occurrences), landing unverified (task bc8m5gfd3), re-probe launched (task ba2jefs25).
- Bridge: `NM_UNVERIFIED` landing REFUSED (imports `LerayHirschCompactClosedOf`, not on main); preserved as attic text
  38834f04d (`attic/inflight/lx-splitK/…/ChernSplittingOfLHBridge.lean.txt`).  Real landing + probe wait for lx-lhK-b.

- 11:52 probe 0912-115224-90410 (lix-h, base abbee4ed0): **`ChernSplittingOfOpsAdapter` BUILT** (with `Even.zero`);
  `ChernSplittingOfLix` red on `Unknown identifier tautCardOf` (it lives in `LH`; the whnf timeouts on the `hLH`
  binder were the cascade).  Fix = `open GroupApproximation.CharClass.LH`, also applied to the bridge (same omission).
- The adapter-fix landing was refused by the clobber guard because the restore 3f71a3a50 last touched the path with byte-identical
  bytes (blob 617dc3268 = my 19bb412a3); re-landing with `NM_BASE=<tip>`: adapter normally (record 0912-115224-90410),
  Lix and bridge unverified.
- lx-lhK-b landed the closing chain + my bridge unverified at 60eceb761 (`LerayHirschCompactClosedOf`,
  `LerayHirschLadderClosedOf`, `ProjectiveSpaceRingClosedOf`, …).  Next ONE probe: OpsAdapter, Lix, LHBridge — timed
  with lx-lhK-b's chain probe so the shared lake-cache builds the chain once.

## NEXT (after repair)
- Land `ChernSplittingOfLHBridge` unverified once lx-lhK-b's `LerayHirschCompactClosedOf` (+ `LerayHirschCompactOf`,
  `LerayHirschLadderClosedOf`, `LerayHirschNegOf`, `ProjectiveSpaceRingClosedOf`) is on main.
- ONE probe: `ChernSplittingOfOpsAdapter`, `ChernSplittingOfLix`, `ChernSplittingOfLHBridge`.

## TRAPS
- `git ls-tree <rev> -- <nested path>` without `-r` prints nothing; judge tree contents with `ls-tree -r` and a file count.
- `git grep -E` has no `\b`; use `-P`.
- zsh colon modifier: `git show "$B:Palomar/…"` loses `:P…`; write `"${B}:path"`.
- `LerayHirschGraded.pull_injective (L) (hr : 0 < r) (n)` is K-generic (LerayHirschDegree:155) — the per-stage injectivity needs no new lemma.
- `ParityPData.pH_z_mul` and `PowerData.p_zero_apply` force normalised P⁰ everywhere; use the `…N` twins.

## STATE 12:15 CDT (after the restore)
- **GREEN, probe 0912-120929-55821** (lix-h, base 5edf273be): PROBE GREEN, 9261 jobs; `ChernSplittingOfLix` BUILT;
  `ChernSplittingOfOpsAdapter` compiled (BUILT in 0912-115224-90410, replayed here with identical bytes); COMPILED
  evidence for all 8 overlay modules (`lanes/lx-splitK.green.0912-120929-55821`).  Axioms `[propext, Classical.choice,
  Quot.sound]`.  Bytes on main: adapter 9d1f26b33 (landed normally), Lix 314106e6d (bytes = green record).
- So the narrowed splitting principle at the real mapping torus is compiled end to end:
  `KGen.hasSplittingPN_lixBundleOf p n dd hgen hLH ops G hGc hGu PN hnat :
   ParityP.HasSplittingPN p (LerayHirschDataEvenOf.of_graded (hLH _ (lixBundle n G hGc hGu) (lixRank n dd)
   (rank_lixBundle …) (one_le_lixRank n dd))).chern PN 1`, open inputs only `hLH : CompactLerayHirschDualOf`
  and `ops : OddPTotal.EvenReducedPowers p` (+ `hnat` for a free `PN`; `…_self` needs none).
- `ChernSplittingOfLHBridge` (discharges `hLH` at `cpGenOf`, gives `KGen.hasSplittingPN_lixBundle`): on main unverified
  (60eceb761 + open-LH fix fb4861756).  Probe HELD: its closure reaches lx-lhK-a's `CohomologyChartPeelUniqOf`, red on
  origin until lx-lhK-a's fix lands; lx-lhK-b sends the tag of its RingClosedOf + CompactClosedOf probe, then ONE probe
  of the bridge.
