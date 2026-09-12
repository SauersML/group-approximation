# lx-bundleP — the bundle data of Step D mod `p` (`Gen.RealBundleModP`), its Wu field, and the ExpChar instance

Lane of the LIX strongest swarm (lead: main session nonsofic-existence-39). Clone spare2.
Owns `CharClass/LIXStepDGenBundleP*`, `CharClass/LIXStepDGenExpChar*`, and `Gen.realWu_of_splittingN`
(coordinator ruling 09-12).

## Group probe 0912-114034-42709 (spare2, acn112, base faf9c127d)
- BUILT + COMPILED: `LIXStepDGenBundlePWuN`, `LIXStepDGenBundleP`, `LIXStepDGenExpChar`, `LIXStepDGenBundlePLix`.
  Landed normally at 6ff29b783 (NM_BASE = restored tip; the restore 3f71a3a50 reproduced my earlier blobs byte for byte).
- NOT BUILT: `LIXStepDGenBundlePReal`, because its import `CharClass/LIXKGenChernOf` (lx-stepcK-local) is red:
  Type mismatch at 64:6, 78:10, 94:10; `lixChernDegOf_eq_of_graded` / `lixChernDegOf_mappingTorus` depend on `sorryAx`.
  BundlePReal landed unverified at 1302f8022; re-probe once LIXKGenChernOf is fixed (owner told).

## Files (group probed together)
| file | content | state |
|---|---|---|
| `LIXStepDGenBundlePWuN` | `Gen.realWu_of_splittingN` (the `wu` field from `PowerDataN` components), `Gen.realWu_of_hasSplittingPN T hp Γ m hwu i`, `Gen.isUnit_realWuLeading` | see group probe above |
| `LIXStepDGenBundleP` | `Gen.EvenKunnethSplitOf`; `bundlePA/PB/PB_low/PGamma_eq/PA_eq_map`; `Gen.realBundleModP_of_split hp T Γ hhom hsplit s hs hsz gen hslice m hpY hm (hwu : HasSplittingPN p Γ T.PN m)`; `Gen.gamma_top_eq_zero_of_split` | GREEN 0912-114034-42709, landed 6ff29b783 |
| `LIXStepDGenExpChar` | `Gen.nonempty_baseY`, `instance Gen.expChar_evenPart_baseY p dd`, `Gen.natCast_p_evenPart`, `Gen.isUnit_intCast_evenPart` | GREEN 0912-102525-49371 and 0912-114034-42709; bytes unchanged |
| `LIXStepDGenBundlePLix` | `Gen.realBundleModP_stages` (data binder of `lemmaTwoFor_powers_of_stepC_realModP` over `ZMod p`, any `N`), `Gen.evenDeg`, `Gen.realBundleModP_stages_deg`, `Gen.nonempty_realBundleModP_stages_deg`, `Gen.lemmaTwoFor_powers_of_stepC_bundleP` | see group probe above |
| `LIXStepDGenBundlePReal` | `Gen.coe_chern_eq_lixChernDegOf`, `Gen.realBundleModP_lixChernDegOf K p hp n dd T hgen G hGc hGu LE hhomE LV q m hpY hm hwu`, `Gen.nonempty_realBundleModP_lixChernDegOf_stages` (clause (i) of `NinetyNineProblems.LemmaTwoPowersModPData`) | see group probe above |

Semantic changes of 09-12 (after lx-torusP e6b92af13 and lx-splitK's narrowing): `hwu` is the narrowed
`HasSplittingPN p Γ T.PN m`; the reduced powers are the even-part `T.PN`; the strong `HasSplittingP` and
`Gen.realWu_of_splitting` are no longer consumed (lx-torusP told it may retire the latter).

## Discharged at the real torus (`LIXStepDGenBundlePReal`)
- Künneth split: `KnLix.evenKunnethSplitOf K n dd` (lx-kunneth, GREEN 0912-105131-84638).
- Slice section `KnLix.slice n dd southPole q`, `KnLix.slice_map_prY_map`, `KnLix.slice_map_zClass` (lx-kunneth).
- Slice value: `Gen.sliceValue_lixBundleOf K n dd G hGc hGu s q (fun _ => rfl) hgen LE LV` (lx-sliceK, GREEN 0912-110336-46269).
- Degreewise link: `KGen.lixChernDegOf_mappingTorus` (lx-stepcK-local, unverified 0547a55c3).
- `p = 0`, unit normalisation, ExpChar: `LIXStepDGenExpChar`.

## NEEDS (remaining binders of `nonempty_realBundleModP_lixChernDegOf_stages`)
- `T j`: `RealTorusModP n (ZMod p) (KnLix.prY …) (KnLix.prS1 …) (KnLix.prSodd …) (sphereTopClassOf _ 1 _) (sphereTopClassOf _ (2n+1) _)` (lx-torusP, `realTorusModP_ofIso ops …`).
- `LE j G hGc hGu := hLH _ (KGen.lixBundle n G hGc hGu) _ (rank_lixBundle …) (one_le_lixRank …)`, `LV j` (lx-lhK-b's compact LH over K).
- `hhomE`: `LerayHirschDataEvenOf.chern_eq_of_graded (LE j G hGc hGu)` (lx-lhK-b, `ChernClassesEvenHomogOf`, red at probe 0912-110215-40113 in its helper; fix known, not yet saved).
- `hwu j G hGc hGu := KGen.hasSplittingPN_lixBundleOf p n _ (hgen j) hLH ops G hGc hGu (T j).PN hnat` (lx-splitK, 19bb412a3), `κ := 1`.
- `q`: any unit vector.

## TRAPS
- `Gen.splitA`/`splitB` would shadow `CharClass.splitA/splitB` (ParityEvenTransport) inside `namespace Gen`; renamed `bundlePA/bundlePB`.
- A peer commit (becc912bd) deleted the repository tree and 3f71a3a50 restored it; a probe/landing in that
  window fails with "bad import" / "imports X which is not on origin/main" on files that exist. Check
  `git cat-file -e <probe base>:<path>` before debugging; relaunch on the restored tip.
- `rw` matches at reducible transparency: `↑x : TotalHOf K (KGen.lixN n dd)` and `↑x : TotalHOf K (TopCat.of …)`
  do not match syntactically; move such steps through `congrArg`/`Eq.trans`/`exact`, which unify at default.
- The local disk is at 100% (~900 MiB free, 09-12 11:20): keep scratch small.
