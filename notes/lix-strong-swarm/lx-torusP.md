# lx-torusP — the torus data `Gen.RealTorusModP` at the real mapping torus (2026-09-12)

Owns `CharClass/LIXStepDGenReal*`, `CharClass/LIXStepDGenTorusP*`. Clone lix-g (probes ran on lix-g, lix-p).

## GREEN
- Probe 0912-113737-31045 (base 427fba0af): COMPILED `LIXStepDGenReal` v3, `LIXStepDGenTorusPModel` v2; BUILT against
  them `LIXStepDGenRealTorus`, `LIXStepDGenRealTorusModel`, `ProblemLIXStrongAssemblyOddP`.
- Probe 0912-121048-60132 (base 7d220e568, SLURM, 9240 jobs, PROBE GREEN): BUILT `LIXStepDGenTorusPPtot` v3 and
  `LIXStepDGenTorusPLix` v2; all four lane files COMPILED; `Gen.realTorusModP_lixStage` depends on axioms
  `[propext, Classical.choice, Quot.sound]`.

## LANDED
- 21c8eb2a6 `LIXStepDGenReal` v3 (normal). 427fba0af `TorusPModel` v2 + `TorusPLix` v2. 6146a3480 `TorusPPtot` v3.
  Bytes on main equal the green records.
- History: e6b92af13 Real v1 (compiled); cf40c6aa0 Model v1, 337c42c4d Lix v1 (unverified, superseded); attic
  copies d39366acf, 6e3933cfb (on the gutted tree becc912bd), 68c365435.

## `Gen.RealTorusModP` (semantic history)
- v0 (lix-evenside-n): P on all of `TotalHOf`, `P⁰ = id`, Cartan, `P_t`, `P_x`.
- v1 e6b92af13: even parts; `P_z` replaces `P_t`/`P_x`.
- v3 21c8eb2a6: fields `circle_two`, `z_inj`, `PN`, `PY`, `natural`,
  `z_mul_zero : ∀ i r, PY i r = 0 → PN i (evenZClass K q₁ qodd σ₁ σodd * evenMap K pY r) = 0`, `PY_unstable`
  (even degrees). `toModPStepDDataN` → lx-slice2's `Gen.ModPStepDDataN`. `realWu_of_splitting` retired
  (lx-bundleP's `realWu_of_hasSplittingPN` replaces it). `gamma_top_eq_zero`, `stepDHalf_of_realModP`,
  `lemmaTwoFor_powers_of_stepC_realModP` unchanged in statement.

## Producers (all compiled)
- `TorusPModel`: `prSphOf`, `zSphereProd`, `even_zDeg`, `sphereProd_coh_eq_zero_of_ne` (H^m(S^{2n+1}×S¹;K) = 0 for
  m ∉ {0,1,2n+1,2n+2}), `sphereProd_coh_eq_zero`, `zClass_comp_sphereProd`, `P_z_of_sphereFactor`,
  `totalHOf_map_comp_apply`, `totalHOf_map_id_apply`, `z_inj_ofIso`.
- `TorusPPtot`: `totalHOf_of_smul`, `sphereProd_top_eq_smul` (H^{2n+2} spanned by z₀), `pull_point_zSphereProd`,
  `sphereProd_coh_zero_eq_zero_of_pull` (point restriction injective on H⁰), `ptot_sphereProd_component_zero`,
  `ptot_sphereProd` (Ptot z₀ = ν • z₀), `z_mul_zero_of_sphereFactor` (via `mul_single`), `RealTorusModP.ofEven`,
  `realTorusModP_ofIso ops Y n e σ₁ hσ₁ σodd hσodd`.
- `TorusPLix`: `realTorusModP_lix ops n dd` at `KnLix.prY/prS1/prSodd` with `sphereTopClassOf (ZMod p) 1 _`,
  `sphereTopClassOf (ZMod p) (2n+1) _`; `realTorusModP_lixStage ops n j` (dd := `LIX.Gen.lixDD n j`).
- No hypothesis on `Y` anywhere: stage 0 (Y a point) is covered.

## NEEDS
- A producer of `OddPTotal.EvenReducedPowers p` (lx-pzero). With it, `T j := Gen.realTorusModP_lixStage ops n j`
  is the torus input of `LemmaTwoPowersModPData n p` (lx-endpoint).

## SPLIT
- none: every field of `RealTorusModP` has a compiled producer over `ops`.

## TRAPS
- `DirectSum.of_smul`'s first explicit argument is the ring `R`; pass `(R := K) (M := …) (i := d) (c := s) (x := c)`.
- A coercion target written with `_` for the space (`(x : TotalHOf K _) 0`) inserts no coercion; name the space and go
  through `TotalHOf.component`.
- State cohomological lemmas over an arbitrary `[Field K]` and use them at `ZMod p` as terms: no rewrite then compares
  `ZMod.commRing p` with `Field.toCommRing`.
- Never probe or land while main is gutted: the probe job delta-syncs the clone to origin/main and deletes absent paths.
- `lxland.sh` can outlast the 120 s Bash timeout; run it in the background. Lanes share clones; read your own tag's log.
