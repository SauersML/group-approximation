# lx-slice2 — the `WuStepDData` producer at p = 2, rank n (LIX strongest swarm)

Owns `CharClass/LIXStepDGen*` except `…Real*`, `…TorusP*`, `…BundleP*`.  Clone lix-l (lxprobe map; earlier probes on lix-c).
Deliverable: the binder `data` of `Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean:45`).
Consumer: lx-endpoint's `NinetyNineProblems.LemmaTwoPowersTwoWuData n` (e1cd56947).

## GREEN
- `CharClass/LIXStepDGenSplit` (`Gen.hasSplitting_lixN`, field `split`): probe 0912-101559-52334, base a85f75a9c, BUILT,
  PROBE GREEN 9212 jobs, axioms [propext, Classical.choice, Quot.sound].  Bytes = origin (84b833ac2).
- Probe 0912-114107-44886 (lix-l, acn112 cores 88-95, base e0d8365e0, after main was restored by 3f71a3a50):
  PROBE GREEN, 9360 jobs, 0 errors, 0 sorryAx.
  - `CharClass/LIXStepDGenWuData`: `✔ [9360/9360] Built` (19s).  By name:
    `Gen.wuStepDData_lixN`, `Gen.nonempty_wuStepDData_lixN`, `Gen.lemmaTwoFor_powers_two_of_localData` each
    depend on axioms [propext, Classical.choice, Quot.sound].
  - `CharClass/LIXStepDGenSlice`, `LIXStepDGenSliceV`: Replayed (compiled earlier in 0912-110215-40064); COMPILED lines.
  - `CharClass/LIXStepDGenChernSplit`: COMPILED line (compiled in 0912-110215-40064).
  - `CharClass/LIXStepDGenModPNarrow`: COMPILED line only.  Its olean (11:38, three hard links) was restored from the
    shared lake artifact cache before this probe started, so lake printed no Built line and replayed no
    `#audit_axioms` info for it.  The cache is keyed by input hash, so some build compiled exactly these bytes,
    but this log carries no axiom line for `Gen.ModPStepDDataN.toParityPDataN` / `gamma_top_eq_zero`.
  - Evidence record: `lanes/lx-slice2.green.0912-114107-44886` (5 files).
- Fix landed e0d8365e0: `open scoped Matrix` in `LIXStepDGenWuData` (the `*ᵥ` notation in
  `lemmaTwoFor_powers_two_of_localData`); no statement changed.  Every lane file is byte-identical to origin.

## What is proved (declarations)
- `CharClass/LIXStepDGenChernSplit`: `Gen.eq_map_section_of_split` (a k = s^* γ k for ANY decomposition: no pinned
  splitting), `Gen.map_tClass_eq_zero_of_const`, `Gen.WuStepDData.ofSection`.
- `CharClass/LIXStepDGenSlice`: `Gen.lixSliceMapN`, `Gen.lixSliceN`, `Gen.pull_lixChern_lixSliceN`,
  `Gen.mappingTorus_lixSliceN` (south pole: 0 ⊕ V on the nose), `Gen.map_lixSliceN_lixChernOf`.
- `CharClass/LIXStepDGenSliceV`: `Gen.chernOf_lixSliceN_eq_vBundleY`, `Gen.map_lixSliceN_lixChernOf_eq_sliceClass`.
- `CharClass/LIXStepDGenWuData`: `Gen.lixSliceN_comp_prY`, `Gen.lixSliceN_comp_prS1` (rfl), **`Gen.wuStepDData_lixN n
  [NeZero n] j G hGc hGu`** (every field a theorem), `Gen.nonempty_wuStepDData_lixN`,
  **`Gen.lemmaTwoFor_powers_two_of_localData`** (Lemma 2 at p = 2 from Step C's local data alone).
- `CharClass/LIXStepDGenModPNarrow`: `Gen.pH_z_mul_zero_of_cartan`, `Gen.ModPStepDDataN` (field `pH_z_mul_zero`, no
  `pH_zero`), `Gen.ModPStepDDataN.toParityPDataN`, `Gen.ModPStepDDataN.gamma_top_eq_zero`.

## Discharge recipe for lx-endpoint (`LemmaTwoPowersTwoWuData n`)
`Y j := TopCat.of (baseY (LIX.Gen.lixDD n j))`, `S₁ j := TopCat.of (Sphere 1)`, `Sodd j := TopCat.of (Sphere (2*n+1))`,
`pY j := KnLix.prY n _`, `q₁ j := KnLix.prS1 n _`, `qodd j := KnLix.prSodd n _`,
`hS₁ := fun _ => hasSphereCohomology_sphere 1 (by omega)`, `hSodd := fun _ => hasSphereCohomology_sphere (2*n+1) (by omega)`,
`σ₁ := fun _ => sphereTopClass 1 (by omega)`, `σodd := fun _ => sphereTopClass (2*n+1) (by omega)`,
data `fun j G hGc hGu => CharClass.Gen.nonempty_wuStepDData_lixN n j G hGc hGu` under `[NeZero n]`.

## AUTHORED, UNVERIFIED
- none.

## NEEDS
- none for this lane's deliverable.  The p = 2 chain still needs Step C's `KGen.KZeroLocalData` (lx-local2a/2b).

## TRAPS
- zsh `echo =====` is equals-expansion; `"$B:path"` loses `:P` to a colon modifier — write `"${B}:path"`.
- `git grep -E` has no `\b`: use `-P` or `-w`.
- `lxland.sh` refuses a file importing a module not on origin, in every mode except `NM_ATTIC=1`.
- After a tree restore commit, the clobber guard sees the restore as the last change: land with `NM_BASE=<full origin
  sha>` after checking `git show origin/main:<path> | diff - <path>` shows only your hunk.  A mistyped abbreviated sha in
  `NM_BASE` makes the ancestor test fail silently and reads as a clobber refusal.
- A module restored from the shared lake artifact cache is SILENT in the log (no Built, no audit lines) even when named
  as a target; its COMPILED line is the only evidence.
