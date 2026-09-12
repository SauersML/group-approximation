# lx-bundleP — the bundle data of Step D mod `p` (`Gen.RealBundleModP`) and the ExpChar instance

Lane of the LIX strongest swarm (lead: main session nonsofic-existence-39). Clone spare2.
Owns `CharClass/LIXStepDGenBundleP*`, `CharClass/LIXStepDGenExpChar*`.

## GREEN
- Probe 0912-102525-49371 (spare2, SLURM acn101, base 8fb7ad6ad, PROBE GREEN, 8901 jobs):
  `BUILT CharClass.LIXStepDGenBundleP`, `BUILT CharClass.LIXStepDGenExpChar`, both COMPILED;
  `gamma_top_eq_zero_of_split` depends on axioms `[propext, Classical.choice, Quot.sound]`.
  Landed 8fb7ad6ad (bytes identical to the green record).
  * `Gen.EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd` (Prop): every even class of degree `2k` is
    `pY^* of(2k) α + zClass * pY^* of(2(k−(n+1))) β`, with `β = 0` for `k < n+1`.
  * `Gen.bundlePA/bundlePB/bundlePB_low/bundlePGamma_eq/bundlePA_eq_map`: the chosen components; a
    section `s` of `pY` with `map s ∘ map pY = id` and `map s z = 0` reads `a` off.
  * `Gen.realBundleModP_of_split (hp : 2 ≤ p) T Γ hhom hsplit s hs hsz gen hslice m hpY hm hwu :
    RealBundleModP p dd T (fun k => (Γ k : TotalHOf K N))`, where `c i := m^i · wuCoeff p i`.
  * `Gen.gamma_top_eq_zero_of_split`: Step D at the top index from the same inputs.
  * `Gen.nonempty_baseY`, `instance Gen.expChar_evenPart_baseY p dd`, `Gen.natCast_p_evenPart`,
    `Gen.isUnit_intCast_evenPart` (a unit mod `p` is a unit of the even part).

## AUTHORED, UNVERIFIED
- `CharClass/LIXStepDGenBundlePLix.lean` (landed 3805e2c4b): `Gen.realBundleModP_stages` = the `data`
  binder of `lemmaTwoFor_powers_of_stepC_realModP` over `ZMod p` at every stage `j` and `G`, with
  `Y j = TopCat.of (baseY (lixDD n j))`; `Gen.lemmaTwoFor_powers_of_stepC_bundleP` = Lemma 2 for the
  degree-`k` family from the Step C half and the named inputs.
- STAGED, NOT LANDED (scratch `lixs/bp/BundleP.next.lean`, `BundlePLix.next.lean`): the re-spelling of
  `hwu` to `HasSplittingP p Γ T.PN m` for lx-torusP's even-part `RealTorusModP.PN` (their attic copy);
  applied the moment their module lands. The deg-family adapter `realBundleModP_stages_deg` follows.

## NEEDS (named inputs, owners, agreed spellings)
- lx-kunneth: `KnLix.evenKunnethSplitOf K n dd` (the Prop body verbatim, at `KnLix.prY/prS1/prSodd`,
  `sphereTopClassOf K 1 _`, `sphereTopClassOf K (2n+1) _`); `KnLix.slice n dd p₁ q` with
  `slice_map_prY_map` (= `hs`) and `slice_map_zClass` (= `hsz`); needs `NoOddCohomologyOf K (baseY dd)`.
- lx-lhK-b: `LerayHirschDataEvenOf.chern_eq_of_graded L k : ∃ x, (chern k : TotalHOf) = of (2k) x`
  (`CharClass/ChernClassesEvenHomogOf.lean`), the bridge from `D.chern` to the degreewise family.
- lx-stepcK-local: `KGen.lixChernDegOf K n dd hgen W k : Hmod K (lixN n dd) (2k)` (degreewise, total);
  `γfun j W k := of (2k) (lixChernDegOf …)`, `topClass j W := lixChernDegOf … W (lixRank n dd)` (htop rfl).
- lx-sliceK: `hslice : ∀ q, evenMap K s (Γ q) = (sliceClass Finset.univ gen dd).coeff q`.
- lx-splitK: `HasSplittingP p Γ T.PN m` at the real bundle (narrowed variant pending); lx-design: `m = 1`.
- lx-torusP: `T` at the same objects (`realTorusModP_ofIso ops Y n (KnLix.lixIso n dd) …`).

## TRAPS
- `Gen.splitA`/`splitB` would shadow `CharClass.splitA/splitB` (ParityEvenTransport) inside `namespace Gen`;
  renamed to `bundlePA/bundlePB`.
- Structure-instance fields whose expected type is a beta-redex of an earlier field: prove by term mode or
  `have h : <explicit type> := …; exact h.trans …`, never `rw` against the redex.
