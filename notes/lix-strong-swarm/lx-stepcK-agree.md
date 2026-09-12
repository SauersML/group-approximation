# lx-stepcK-agree — LocalClassesAgree and KZeroStepCDataOf over a field

Owns `CharClass/LIXKGenOfStepC*`, `LIXKGenAgree*`, `LIXKGenRotate*`, `LIXKCount*`, `Thom*`, `Gysin*`, `RelativeSupport*`.
Clone lix-e (the probe summary reported lix-k).

## The mathematics (LocalClassesAgree over any field, for EVERY u and EVERY split)
R_c(t, x, y) = (t, update x 0 (c·x₀), y). With c = kUnity^i, R_c z_0 = z_i. joinC k (c z) = c^{k+1} joinC k z,
so Ψ_k∘R_c = Ψ_k and the southern field β = blockSouth(aVecK, bVecK n k, cVec∘snd) is R_c-invariant.
On S = {circHeight < 0} the section is P(p)(0 ⊕ β p), injective on V's fibre, so for p ∈ S,
R_c p ∈ Z ⇔ p ∈ Z. The ball is B_i = S ∖ otherZeros i, and F_i = relPullback incl : H(N, N∖z_i) → H(B_i, B_i∖Z) is
injective (excision). restrictTo_{B_i}(Σ ρ_j x_j) = F_i x_i. Half B: the frozen-field homotopy
H(τ, p) = (R_{c(τ)} p, P(R_{c(τ)} p)(0 ⊕ β p)) is a homotopy of pairs (B_0, B_0∖Z) → (E, E∖0), so
F_0(R^* x_i) = F_0 x_0. Half A: naturality of relToAbs along R, plus R ≃ id. Reviewed by lx-review: no flaw.
Model test `lixs/agree` on MSI: joinC invariance, root rotation, zero-set invariance, path endpoint.

## GREEN (12:0x CDT)
**Probe 0912-115818-13551 (acn112 slot 1, base 2968d8530): PROBE GREEN, 8987 jobs.** `Built LIXKGenAgree (25s)`, `Built
LIXKGenOfStepCAgree (24s)`, COMPILED Rotate/Agree/OfStepCAgree, 0 sorryAx lines. Axioms read by name, each
`[propext, Classical.choice, Quot.sound]`: `KGen.injective_agreeRes`, `restrictTo_eq_agreeRes`, `agreeRes_rotRel`,
`lixKJlocOf_rotRel`, **`localClassesAgree_of_localSplitOf`**, **`kZeroStepCDataOf_of_localNonzeroOf`**,
**`stepCHalf_of_localNonzeroOf`**. Origin bytes = compiled bytes (md5 Rotate bec623c6, Agree 439b5559, OfStepCAgree
45c3ef8a) at bac03055a. Landings: fix batch 2 3dc9499aa, fix batch 3 7cb04ef68.

**LocalClassesAgree over any field is a THEOREM**, for every relative class u and every split. The Step C half over K now
needs exactly: `KGenLocalNonzeroOf K n k … u` (lx-stepcK-local, `kGenLocalNonzeroOf_of_top_closed`) and
`jE u = π* topClass` (S2, lx-sliceK, `LIXKGenOfStepCThom`, landed unverified e40a89a08).

## ThomChartTautZeroOf (new, my Thom* prefix; S2's residual (c) `hchart`)
`CharClass/ThomChartTautZeroOf.lean` landed fe8a1e09d; **probe 0912-121807-89542 (acn112, base 178be1c22): PROBE GREEN,
9183 jobs, `BUILT ThomChartTautZeroOf` on the first probe** (COMPILED with Rotate/Agree/OfStepCAgree): `eulerOfBundleOf_comap_const_eq_zero`,
`eulerOfBundleOf_pushforward_eq_zero_of_trivIso`, `LH.pull_zeroSectionProj_tautEulerOfK`,
`LH.pull_chartInclMap_tautEulerOfK`, `LH.pull_bridgeChartIncl_tautEulerOfK`, **`LH.pull_bridgeChartIncl_tautEulerDualK K
hgen p : pull (cmap (bridgeChartIncl p)) 2 (tautEulerDualK K hgen p.plusOne) = 0`** (`[Field K]`, generator arbitrary).
Axioms read by name in the log, each `[propext, Classical.choice, Quot.sound]`: all six declarations above; 0 sorryAx
lines; `Built GroupApproximation.CharClass.ThomChartTautZeroOf (21s)`. Origin bytes = compiled bytes at cbeced59f (md5
d7a56480). lx-kunneth confirmed the statement is exactly the `hξ` of `pull_bridgeChartIncl_lhSumOf` /
`relToAbs_total_eq_pull_coordOf`; lx-sliceK has the SHA for S2's `hchart`.
S2's residual (b) `htaut` (O(1) along the hyperplane inclusion) is the K-form of `ChernTautRestrict`/`ChernTautHyperIso`:
`Chern*` prefix. lx-lhK-b accepted it, then WITHDREW: the lead booked it to lx-sliceK (`CharClass/LIXKGenOfStepCThomClosed.lean`,
namespace `KGen`), and lx-lhK-b sent lx-sliceK the compiled K tools (`eulerOfBundle_eq_of_bundleIsoOf`,
`eulerOfBundle_pushforward_congrOf`, `eulerOfBundle_pushforward_iterFinOf`). Residual (a) `hgamma` is with lx-stepcK-local.
lx-review F1 (review-2.md): `lixHclassOf` gives `π*(−Lh.gamma r)` at the `ι ⊕ Unit` generator, while the endpoint's topClass is
`lixChernDegOf` at the `VIdx ⊕ VIdx` generator. They differ by a nonzero scalar. Fix on this lane's consumer side: a scaled
Step C half (`∃ c ≠ 0, jE u = π*(c • topClass)`, `u' := c⁻¹ • u`). Also: `LIXKGenOfThomLH` (51a0e52c) has no compiled record
(lx-stepcK-local's probe 0912-114035-42872 FAILED).

## OPEN (none owned by this lane)
- `KGenLocalNonzeroOf` at the Thom class: lx-stepcK-local (`LIXKGenOfThomLH`, `kGenLocalNonzeroOf_of_top_closed`).
- `jE u = π* topClass`: S2 lx-sliceK (`LIXKGenOfStepCThom`, e40a89a08), residuals (a) lx-stepcK-local, (b) lx-lhK-b, (c) DONE here.
- For lx-endpoint's odd-prime assembly: make its hypothesis Prop the `hdata` of `KGen.stepCHalf_of_localNonzeroOf` at
  `K = ZMod p`; the generator seam between `lixLHplusDualOf` (index `(VIdx ⊕ VIdx) ⊕ Unit`) and `lixChernDegOf`'s
  `cpGenOf (1 + tautCardOf (VIdx ⊕ VIdx))` is the same compatibility as (b).

## TRAPS (this lane)
- `calc` over two defeq carrier spellings (`↑(lixN n dd)` vs `↥sphereOne × Gen.baseM n dd`) fails with "failed to
  synthesize Trans Eq Eq ?m": `Trans` search runs at instances transparency and does not unfold `lixN`. Chain with
  `Eq.trans` instead (default transparency).
- A lambda `fun _ hx => lemma _ hx` passed as the FIRST mapsTo argument of `relPullback_eq_of_homotopy` assigns the
  implicit domain from the lemma's statement (here `X := lixN`), and the second lambda then mistypes its point: pass
  `(X := …) (A := …) (f := …) (g := …)` explicitly.
- `injective_relPullback_id_of_eq K (agreeBall_preimage_eq …) hsub q`: `W` is not inferable from a set equation whose
  sets live over a subtype (`↑?W =?= ↥(agreeBall …)` is stuck); name `W`.
- After `rw` in a `Homotopy.map_zero_left` field, both sides can print identically but differ in how the subtype point is
  coerced; `rw`'s reducible `rfl` fails, a plain `rfl` closes it.
- A local network outage (`Could not resolve host: github.com`) makes lxprobe/lxland exit early with "PROBE FAILED: git
  fetch (infra)" and nothing built: re-arm behind a `git ls-remote` wait loop.

## RESUMED (main restored by 3f71a3a50; tip 65dfdecc7, 27,817 files)
Origin blobs of Rotate/Agree/OfStepCAgree equal d73168597; the working-tree Agree = fix batch 2 (md5 45c3ef8a).
Fix batch 2 landing (NM_UNVERIFIED, NM_BASE = tip); ONE probe of Agree + OfStepCAgree launched at the tip.
SPLIT reassigned by the lead: S1 `ThomLIXHclassOf` → lx-kunneth, S2 `LIXKGenOfStepCThom` → lx-sliceK (spellings sent,
with lx-stepcK-local's `lixLHplusDualOf` / `kGenLocalNonzeroOf_of_top_closed` route). This lane authors neither.

**Fix batch 2 LANDED 3dc9499aa** (one file). **Probe 0912-114126-45825 (SLURM acn02, base e0d8365e0): PROBE FAILED**,
4 errors in LIXKGenAgree: (191) `W` unassigned in `injective_relPullback_id_of_eq`; (333) `map_zero_left` needs `rfl`
after `rw`; (429) `hf`'s lambda fixed `X := lixN`; (435) `calc` Trans failure across the two carrier spellings
`↑(lixN n dd)` / `↥sphereOne × Gen.baseM n dd`. `restrictTo_eq_agreeRes` and `lixKJlocOf_rotRel` elaborated with the
classical axioms. Rotate COMPILED again (evidence `lanes/lx-stepcK-agree.green.0912-114126-45825`).
Fix batch 3 authored (named W; rfl; explicit X/A/f/g/points; Eq.trans chain), landing + second probe launched.

## MAIN WIPED (11:10 CDT): HOLD (lifted, see above)
Commit becc912bd (Sauers, "Import Evington--Pennig triviality…") deleted 27,760 files from origin/main. At tip
bff8f642a the tree has 23 files. The parent ce16f64eb is intact (27,760 files); the 13 later commits are additive. The
lead was alerted with the forward-restore recipe. No landings or probes from this lane until main is restored.
Backup of the unlanded bytes: `lixs/backup/lx-stepcK-agree/` (md5: LIXKGenAgree 69b1a560… = fix batch 2,
LIXKGenOfStepCAgree 45c3ef8a…, LIXKGenRotate bec623c6…; an earlier version of this line had the labels permuted).
12:0x CDT: the first retry of landing + probe died locally on `Could not resolve host: github.com` (nothing landed,
no build ran); both are re-armed to wait for the network.

## GREEN
- **LIXKGenRotate** COMPILED, probe 0912-110434-51619 (acn112, base d73168597, BUILT). Bytes = unverified landing
  d73168597. The normal re-landing was refused because main is wiped.
- Probe 0912-104623-53351 (earlier): 4 errors in Rotate, all fixed.

## RED / IN FLIGHT
- **LIXKGenAgree** red at 0912-110434-51619. Causes: T1Space ↑(lixN n dd) not found (fixed by importing LIXKGenBaseChart,
  instance `KGen.instT1SpaceLixN`); a right-associated `×` in two `show` ascriptions (fixed); rw/simp on terms not type-correct at
  instances transparency (replaced by a `calc` of explicit equalities); `relPullback_eq_of_homotopy` is
  `RelativeSupport.relPullback_eq_of_homotopy` (fixed); an unused binder `x` (fixed). `restrictTo_eq_agreeRes` already
  elaborated with the classical axioms. Fix batch 2 is authored and backed up, not landed, not probed.
- **LIXKGenOfStepCAgree** landed unverified at d73168597, not reached (its import was red).

## AUTHORED, UNVERIFIED (landed per rule 5')
- `CharClass/LIXKGenRotate.lean` (a6622e53c + fix batch): rotVec, rotPt, rotMap, rotPt_lixKZero, blockSouth_rotPt,
  lixKSection_of_circHeight_neg, mappingTorus_mulVec_inr_eq_zero_iff, mem_lixKZeroSet_of_rotPt, rotPath, rotHomotopy,
  pull_rotMap.
- `CharClass/LIXKGenAgree.lean`: agreeBall, agreeRes (+ injective), restrictTo_eq_agreeRes, rotBall,
  agreeHomotopy (+ mapsTo), agreeRes_rotRel (Half B), lixKJlocOf_rotRel (Half A),
  **`KGen.localClassesAgree_of_localSplitOf`**.
- `CharClass/LIXKGenOfStepCAgree.lean`: `KGen.kZeroStepCDataOf_of_localNonzeroOf`,
  **`KGen.stepCHalf_of_localNonzeroOf`**: Step C half over K from (∀ G, ∃ u, KGenLocalNonzeroOf u ∧ jE u = π* topClass).

## NEEDS
- lx-stepcK-local: `KGen.kGenLocalNonzeroOf_of_fibre` (landed unverified d3fefdbc6) + hfib at the K-Thom class.
- lx-stepcK-local: K Chern classes `KGen.lixChernDegOf K n dd hgen W k : Hmod K (lixN n dd) (2*k)`, LH data with
  `LH.tautEulerDualK`.
- lx-lhK-b: `LH.lerayHirschGraded_compactOf` (Leray–Hirsch data for the plusOne bundle over K).

## SPLIT (independent sub-tasks a helper can author now)
- S1 `CharClass/ThomLIXHclassOf.lean` (my prefix `Thom*`): K-twins of the generic helpers of
  `CharClass/LIXHclass.lean` over `[Field K]`, `ξ : Hmod K P 2`, `L : LerayHirschGraded π ξ r`:
  `gammaCoeff_eq_of_valOf`, `gamma_top_eq_chernCoeffOf`, `chernMul_top_unitOf`, `lhTerm_zero_classOf`,
  `lhTerm_at_index_zeroOf`, `pull_bridgeChartIncl_lhSumOf (p : Bundle X ι) (r) (hr : 1 ≤ r) (a)` — same statements
  with `Hmod2` → `Hmod K`, `thomJmTotal` → `thomJmTotalOf K`, `chernMul` → `chernMulOf`, `lhTopEquiv` → `lhTopEquivOf`.
  Inputs on main: `ThomChernDegreewiseOf`, `ThomHabsOf`, `ThomJmNaturalOf`, `ThomBridgeRelToAbsOf`.
  Signs: over K the degreewise gamma is −c_k (lix-lh design note); keep whatever sign the port produces, since a unit
  is absorbed by rescaling u.
- S2 `CharClass/LIXKGenOfStepCThom.lean` (my prefix): `KGen.lixThomClassTermOf K n hGc hGu L Lh` =
  `(ThomDeg.thomEquiv (fun i => chernMulOf Lh i) (thomJmTotalOf K E L) hinj hrange).symm (top unit)`, and
  `KGen.lixHclassOf : (lixJEOf K n hGc hGu (2r)).hom (lixThomClassTermOf …) = (lixPiStarOf …).hom (± topChern)`,
  the K-port of `CharClass/LIXKGenHclass.lean` over S1. Parametric in L, Lh until lx-lhK-b's compact LH lands.

## TRAPS
- `congrArg f h` with an expected type `f a = f b` unifies the arguments with the expected ones, not with h's sides;
  state the equality at h's sides and `exact`.
- `(𝟙 X).hom` is invalid field notation (type `CategoryStruct.toQuiver.1 X X`); use `TopCat.Homotopy (𝟙 X) g`.
- `continuous_rotPt_param … (fun q => norm_rotPath k i (q.1 : ℝ))`: pass `(c := fun q => …)` explicitly, or the norm
  proof's argument stays a metavariable.
- The msi cat-upload of a script can be silently empty; inline the script in the remote command.
