# lx-review, round 3: the narrowed structures on the D1 chain (2026-09-12, origin cbeced59f)

Scope: every Prop and structure between `LemmaTwoHoldsAtPowers n` and the producers, after 6e3933cfb/68c365435
(`Gen.RealTorusModP`), 19bb412a3 (`HasSplittingPN` producers), f71de7421 (`Gen.ModPStepDDataN`), e0d8365e0
(`LIXStepDGenWuData`), 3dc9499aa (`LIXKGenAgree`), de17c2bb1 (OddPTotal packaging), plus what landed alongside
(58f87fe90, 142fedcac, e40a89a08, 3e0c73d91, 427fba0af/6146a3480).  Checks:
- (a) satisfiable at stage 0 (`lixDD n 0` empty) and deeper;
- (b) not vacuous;
- (c) no over-ask;
- (d) conventions agree between producer and consumer.
Evidence column: whether main's bytes equal a compiled record of the lane's probe (`lxprobe` green records).

## Verdicts

| structure / Prop (file) | (a) | (b) | (c) | (d) | evidence |
|---|---|---|---|---|---|
| `Gen.RealTorusModP` (LIXStepDGenReal, md5 2fdc1f85) | yes: `Y` a point at stage 0; `z_inj` needs nonzero sphere classes, supplied by `sphereTopClassOf` | no | `z_mul_zero` is exactly `ModPStepDDataN.pH_z_mul_zero` (`toModPStepDDataN`) | ok | compiled (lx-torusP 113737, 121048) |
| `Gen.realTorusModP_ofIso` / `z_mul_zero_of_sphereFactor` (TorusPPtot) | producer: `mul_single` at z, `Ptot z = ν z` (degree-0 component dies by restriction to a point, degree 2n+2 a line) | — | — | ok | compiled (121048) |
| `Gen.ModPStepDDataN` (LIXStepDGenModPNarrow) | yes | no | none: no `pH_zero`/`cartan`/`pH_z` left; sole use ParityPDataNarrow:151 | ok | compiled (lx-slice2 114107) |
| `ParityP.HasSplittingPN` (ParityPSplitStepDNarrow:32) | yes | no | `hP` only at `γ (i+1)`, matching `wu_field_of_splittingN`, `realWu_of_hasSplittingPN` | κ = 1 (`degree_two`); leading coefficient a unit by `isUnit_realWuLeading` + `natCast_p_evenPart` | adapter and Lix compiled (lx-splitK 120929) |
| `ChernSplittingOf.CompactLerayHirschDualOf` (ChernSplittingOfCompact:181) | only for `hgen ≠ 0` (false at `hgen = 0`); discharged at `cpGenOf` by `compactLerayHirschDualOf_cpGen` | no | — | `tautEulerDualK` throughout Step D | — |
| `Gen.EvenKunnethSplitOf` (LIXStepDGenBundleP:57) | yes, with nonzero sphere classes (`KnLix.evenKunnethSplitOf`) | no | general in `k`, true | degree `2k` ↔ `β` in `2(k − n − 1)` | compiled (lx-bundleP 120132) |
| `Gen.realBundleModP_lixChernDegOf` / `…_stages` (LIXStepDGenBundlePReal) | yes | no | `hhomE` owed (F2) | `LE`, `LV`, the splitting and `lixChernDegOf` share `hgen` (use `cpGenOf`); sphere classes agree with `realTorusModP_lix` (`le_rfl` vs `by omega` is proof-irrelevant) | compiled (120132) |
| `Gen.wuStepDData_lixN`, `lemmaTwoFor_powers_two_of_localData` (LIXStepDGenWuData) | theorems | — | — | — | compiled (lx-slice2 114107) |
| `KGen.KZeroLocalData` → `kZeroLocalData_holds` (LIXKGenLocalNonzero:105) | theorem, every rank / exponent / stage | — | — | — | compiled (lx-local2b 114043) |
| `KGen.localClassesAgree_of_localSplitOf` (LIXKGenAgree:461) | theorem for every `u` and split | — | — | — | compiled (lx-stepcK-agree 115818, 121807) |
| `OddPTotal.EvenReducedPowers` / `TotalReducedPowers.toEven` (OddPTotalPackaging*) | producible; normalisation checked (below) | no | Cartan only on `Good`; `zero` only on `H²(ℂP^M)` | `totalP s = μ^{−(k−s)}·[D_{(2k−2s)(p−1)}]` is the classical `P^s` | `OddPTotalPackaging` NO compiled record (lx-pzero 120528 FAILED) |
| `KGen.lixHclassOf(_of_eq)` (LIXKGenOfStepCThom:225/254) | theorem | — | — | different generator from Step D's class (F1) | compiled (lx-sliceK 121712) |
| `KGen.kGenLocalNonzeroOf_of_top_closed` (LIXKGenOfThomLH:39) | yes (`hgen0`) | no | — | generator for `ι ⊕ Unit` (F1) | NO compiled record (lx-stepcK-local 114035 FAILED) |
| `NinetyNineProblems.lemmaTwoHoldsAtPowers_two_pow_holds`, `exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow` (ProblemLIXStrongAssemblyTwoWu:39, :46) | hypothesis-free | — | — | — | compiled (lx-endpoint 115408); axioms to be read by name (F4) |

Model test `tools/review_packaging.py` (MSI, 25 odd primes ≤ 101, 157961 checks, 0 failures):
- `μ = ν(2)^{−1} = −1`;
- `μ^{−(k−s)}·ν(2k)^{−1}·(−1)^s = 1` (the packaged `P^s` is the Steenrod–Epstein `P^s`), with `ν(q) = (−1)^{m q(q−1)/2}(m!)^q`;
- `zero_cp`: `μ^{−1}μ = 1`;
- the `GoodDeg` bound `a + 2s(p−1) ≤ pa ⟺ s ≤ a/2`;
- the Cartan exponent identity `(a/2 − j) + (b/2 − (i−j)) = (a+b)/2 − i` whenever `j ≤ a/2`, `i − j ≤ b/2` (outside that range `totalP_of_eq_zero` kills the term).

## Defects and open seams

**F1. Step C over `F_p`: the top class `lixHclassOf` produces is not the class `htop` demands.**
- **`htop`.** `NinetyNineProblems.LemmaTwoPowersModPData` links Step C to Step D through
  `topClass j W := KGen.lixChernDegOf (ZMod p) n dd hgen_D W (lixRank)`: Leray–Hirsch at
  `projMapOf (lixBundle)`, `tautEulerDualK`, and `hgen_D : Hmod (CPtop (1 + tautCardOf (VIdx ⊕ VIdx))) 2`.
- **`lixHclassOf`.** It gives `jE u = π^*(−Lh.gamma r)`, where `Lh` is Leray–Hirsch on
  `hyperProj (lixBundle)` at the restriction of `ξ` from `P(W ⊕ 1)`.
- **`kGenLocalNonzeroOf_of_top_closed`.** It builds `ξ` from `hgen_C : Hmod (CPtop (1 + tautCardOf ((VIdx ⊕ VIdx) ⊕ Unit))) 2`.
- **Why `lixHclassOf_of_eq` cannot be fed.** Its `hgamma : −Lh.gamma r = topClass` is not an identity: the two
  generators differ by a unit `c` (`bijective_pull_cpInclIterOf`), so `γ_r` scales by `c^r`, and the hyperplane
  and `projMapOf` presentations need a base change.  No producer exists on main.
- **Fix.**
  - Prove `∃ c, IsUnit c ∧ −Lh.gamma (lixRank) = c • lixChernDegOf K n dd hgen_D W (lixRank)`, from the base
    change `hyperProj ≅ projMapOf` and the generator comparison.
  - Take `u := c⁻¹ • lixThomClassTermOf …`.  `KGenLocalNonzeroOf` survives by `kGenLocalNonzeroOf_smul`
    (LIXKGenOfLocalScale:36).
  - `hchart` is `ThomChartTautZeroOf.pull_bridgeChartIncl_tautEulerOfK` (:145) with `map_neg`.
- **Owners.** lx-sliceK (`lixHclassOf`), lx-stepcK-agree (the seam), lx-lhK-b (the generator comparison).

**F2. `hhomE` has no producer.**  `Gen.realBundleModP_lixChernDegOf` and `…_stages` take `hhomE : ∀ k, ∃ x,
((LerayHirschDataEvenOf.of_graded LE).chern k).1 = TotalHOf.of _ (2k) x`.  It is true (the Leray–Hirsch
coordinates of `ξ^r` are homogeneous), and a grep of main finds no producer.  Fix: one lemma in the
`CohomologyLH*` files, homogeneity of `LerayHirschDataEvenOf.of_graded … .chern k` in degree `2k`.  Owner lx-kunneth
(prefix `CohomologyLH*`), or lx-lhK-b.

**F3. No compiled evidence at main's bytes on the D1 path:**
- `CharClass/OddPTotalPackaging.lean` (880bca73): lx-pzero's latest probe 0912-120528-42984 FAILED.  It is the
  only producer of `EvenReducedPowers`, hence of `RealTorusModP` and `HasSplittingPN` at odd `p`.
- `CharClass/LIXKGenOfThomLH.lean` (51a0e52c): lx-stepcK-local's latest probe 0912-114035-42872 FAILED.
- Everything else in the table matches a green record.

**F4. The rank-`2^m` endpoint.**  `lemmaTwoHoldsAtPowers_two_pow_holds m` and
`exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow m` are hypothesis-free, and their bytes match
lx-endpoint's green 0912-115408-95665.  Before anyone reports the ranks `2^m` as closed:
- read the `depends on axioms` lines for both names from the RAW log of that probe (a replayed `info` line proves
  nothing);
- confirm `sorryAx` is absent;
- wire the module.
The Palomar challenge is stated for every `n ≥ 2`, so this discharges no challenge theorem; `n = 6` needs `p = 3`.

**Not defects.**  `CompactLerayHirschDualOf` is false at `hgen = 0`, and every producer on main instantiates it at
`cpGenOf`.  Keep it that way: no consumer should take `hgen` as a free binder with this Prop.
