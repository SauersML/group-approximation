# lx-slice2 — the `WuStepDData` producer at p = 2, rank n (LIX strongest swarm)

Owns `CharClass/LIXStepDGen*` except `…Real*`, `…TorusP*`, `…BundleP*`.  Clone lix-c (shared with lx-kunneth).
Deliverable: the binder `data` of `Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean:45`).
Consumer: lx-endpoint's `NinetyNineProblems.LemmaTwoPowersTwoWuData n` (e1cd56947).

## GREEN
- `CharClass/LIXStepDGenSplit` (`Gen.hasSplitting_lixN`, field `split`): probe 0912-101559-52334, base a85f75a9c, BUILT,
  PROBE GREEN 9212 jobs, axioms [propext, Classical.choice, Quot.sound].  Bytes = origin (84b833ac2).

## AUTHORED, UNVERIFIED
Landed unverified deceece4e (probe 0912-… on lix-c queued/running):
- `CharClass/LIXStepDGenChernSplit`: `Gen.eq_map_section_of_split` (a k = s^* γ k for ANY decomposition: no pinned
  splitting), `Gen.map_tClass_eq_zero_of_const`, `Gen.WuStepDData.ofSection`.
- `CharClass/LIXStepDGenSlice`: `Gen.lixSliceMapN`, `Gen.lixSliceN`, `Gen.pull_lixChern_lixSliceN`,
  `Gen.mappingTorus_lixSliceN` (south pole: 0 ⊕ V on the nose), `Gen.map_lixSliceN_lixChernOf`.
Attic copies (imports not yet on main; real landing when the imports land):
- `CharClass/LIXStepDGenSliceV` (imports lx-integrator's `SliceGenValue`): `Gen.chernOf_lixSliceN_eq_vBundleY`,
  `Gen.map_lixSliceN_lixChernOf_eq_sliceClass`.
- `CharClass/LIXStepDGenWuData`: `Gen.lixSliceN_comp_prY`, `Gen.lixSliceN_comp_prS1` (rfl, lx-kunneth's torusHomeo keeps
  y and the circle point), **`Gen.wuStepDData_lixN n [NeZero n] j G hGc hGu`** (every field a theorem),
  `Gen.nonempty_wuStepDData_lixN`, **`Gen.lemmaTwoFor_powers_two_of_localData`** (Lemma 2 at p = 2 from Step C's local
  data alone).
- `CharClass/LIXStepDGenModPNarrow` (imports lx-splitK's `ParityPDataNarrow`): `Gen.pH_z_mul_zero_of_cartan`,
  `Gen.ModPStepDDataN` (no `pH_zero`/`cartan`/`pH_z`; field `pH_z_mul_zero`), `Gen.ModPStepDDataN.toParityPDataN`.
  Still to add once `ParityPDataN`'s conclusion name is known: `ModPStepDDataN.gamma_top_eq_zero`.

## NEEDS
- lx-integrator: `CharClass/SliceGenValue.lean` with `Gen.VSliceValue n dd gen`, `Gen.vSliceValue_sliceGen n dd hdd` (agreed).
- lx-splitK: `CharClass/ParityPDataNarrow.lean` (`ParityPDataN`, field `pH_z_mul_zero` after `pH_ι`) and its Step D conclusion.
- On main already: lx-kunneth `KnLix.*` (f29a035ec, compiled), lx-sliceK `SliceGenOfLines` (fbdce4552).

## SPLIT (independent sub-tasks a helper could take)
- none open in this lane: every remaining step waits on the two NEEDS files, then one probe of SliceV + WuData + ModPNarrow.

## TRAPS
- zsh `echo =====` is equals-expansion; `"$B:path"` loses `:P` to a colon modifier — write `"${B}:path"`.
- `git grep -E` has no `\b`: use `-P` or `-w`.
- `lxland.sh` refuses a file importing a module not on origin, in every mode except `NM_ATTIC=1`.
