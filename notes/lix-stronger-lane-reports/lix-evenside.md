# Lane `lix-evenside` — Step D mod `p`, the even side (successor of `sp-evenside`)

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.4.  Design: `sp-design.md` §3.2–3.4.
Predecessor report: `notes/lix-stronger-lane-reports/sp-evenside.md` (deliverable 1 and the L4a
infrastructure, all on main and green).  Clone: `lix-c` (shared with lix-evenside-n, lix-steenrod;
rule 20).  Owns `CharClass/ParityP*`, `CharClass/StepDModP*`.

## STOPPED 2026-09-12 ~09:35 CDT (wind-down; ruling recorded in `notes/nm-swarm/LIX_LANES.md`)

No new authoring and no probes.  Nothing was in flight.  All twelve owned modules on `origin/main` are
byte-identical to the shared tree, and each one compiled on lix-c (last green record
`0912-004214-2389`).  Nothing was deleted.

**GREEN, on main** (last landing sha): `ParityPTwistSymm`, `ParityPWuValue` 5929e3699;
`ParityPDecomposable` b1467418a; `ParityPWuComponent` 251dd56c0; `ParityPWuTransport` 924c01f0c;
`ParityPSplitStepD` 02d0df66c; `ParityPWuAxiomGuard` 2be49495a; `ChernSplittingOfPowers` 9d422f49d;
`ChernSplittingOfInjective` 9c15285d0; `ChernSplittingOfWhitney` fff335f17; `ChernSplittingOfFlag`,
`ChernSplittingOfAxiomGuard` 62de870b7.

**UNVERIFIED / attic:** none.

### RESIDUAL: input (d) of `ChernSplittingOf.hasSplittingP_flag` (never authored)

This is the `K`-form of `ChernSplitFactor` and `ChernSplitRelation`, planned as
`CharClass/ChernSplittingOfFlagRelation.lean`.  The file does not exist.

Context: `{X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
(hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)`.

```lean
-- (i) the root, at the index of LH.tautEulerOfK
def lineEulerOfK (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) : Hmod K (TopCat.of X) 2 :=
  eulerOfBundleOf K hgen (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q)
    (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) q hq)

-- (ii) proof: CPn.eulerOfBundle_eq_of_bundleIsoOf K (show 1 ≤ 1 + tautCardOf ι by omega) hgen _ _ _ _
--        (pushforwardBundleIso (tautEmbOf ι) (tautEmbOf_injective ι) (tautLineIsoSummand p q hq))
theorem eulerOf_restrict_eqOf (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    lineEulerOfK K hgen (Bundle.restrictTo (tautLine p) (lineOpenSet p q))
        (fun y => trace_tautLine p (y : Proj p))
      = lineEulerOfK K hgen (Bundle.restrictTo (comap (projPi p) q) (lineOpenSet p q))
        (fun y => hq (projPi p (y : Proj p)))

-- (iii) proof: pull_add; unfold LH.tautEulerDualK; map_neg (pullLinear (K := K) _ 2); both summands
--        by eulerOfBundle_comapOf (the second after ← pull_comp); rw (ii); neg_add_cancel
theorem pull_factor_eq_zeroOf (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    pull (opIncl (lineOpens p q)) 2
        (LH.tautEulerDualK K hgen p + pull (cmap (projPi p)) 2 (lineEulerOfK K hgen q hq)) = 0

-- (iv) induction on r: Finset.prod_range_succ, List.range_succ, List.map_append, List.prod_append
theorem coe_prod_range_evenPart {Y : TopCat} (f : ℕ → Gen.evenPart K Y) (g : ℕ → TotalHOf K Y)
    (hfg : ∀ l, (f l : TotalHOf K Y) = g l) (r : ℕ) :
    ((∏ l ∈ Finset.range r, f l : Gen.evenPart K Y) : TotalHOf K Y) = ((List.range r).map g).prod

-- (v) proof: Subtype.ext; (iv) with g l := TotalHOf.of K _ 2 (factor l) (TotalHOf.map_of, map_add);
--        prod_eq_zero_of_coverOf K (fun l => lineOpens p (qf l)) r (by omega)
--          (coverSup_lineOpens p r qf hsum) 2 (by omega) _ (fun l => pull_factor_eq_zeroOf K hgen p (qf l) (hq l))
theorem splitRelation_of_sumOf (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (qf : ℕ → Bundle X ι) (hq : ∀ l x, (qf l x).trace = 1)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, qf l x) :
    ∏ l ∈ Finset.range r,
      (evenTautOf K (LH.tautEulerDualK K hgen p)
        + Gen.evenMap K (cmap (projPi p)) (evenTautOf K (lineEulerOfK K hgen (qf l) (hq l)))) = 0

-- (vi) (v) at p := Wu.flagPullback E r (abbrev for Bundle.comap (Bundle.flagProj E r) E),
--        qf := Wu.flagLineFlat E r, hq := Wu.trace_flagLineFlat E r hr1, hsum := Wu.sum_flagLineFlat E r hrank
theorem splitRelation_flagOf (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, E.rank x = r) :
    ∏ l ∈ Finset.range r,
      (evenTautOf K (LH.tautEulerDualK K hgen (Wu.flagPullback E r))
        + Gen.evenMap K (cmap (projPi (Wu.flagPullback E r)))
            (evenTautOf K (lineEulerOfK K hgen (Wu.flagLineFlat E r l) (Wu.trace_flagLineFlat E r hr1 l)))) = 0

-- (vii) hasSplittingP_flag E r (LerayHirschDataEvenOf.of_graded L) rfl rfl (LerayHirschDataEvenOf.of_graded L') rfl rfl
--        (by rw [TotalHOf.map_of, LH.tautEulerDual_comapOf]) hstage
--        (fun l => lineEulerOfK K hgen (Wu.flagLineFlat E r l) (Wu.trace_flagLineFlat E r hr1 l))
--        (splitRelation_flagOf K hgen E r hr1 hrank) PN hPN PF hPF hzero hcartan m hone hhigh hnat
theorem hasSplittingP_flag_ofGraded {p : ℕ} (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, E.rank x = r)
    [Nontrivial (Gen.evenPart K (TopCat.of X))]
    [Nontrivial (Gen.evenPart K (TopCat.of (Bundle.Flag E r)))]
    (L : LerayHirschGraded (cmap (projPi E)) (LH.tautEulerDualK K hgen E) r)
    (L' : LerayHirschGraded (cmap (projPi (Wu.flagPullback E r)))
      (LH.tautEulerDualK K hgen (Wu.flagPullback E r)) r)
    -- hstage PN hPN PF hPF hzero hcartan m hone hhigh hnat: verbatim as in hasSplittingP_flag
    : ParityP.HasSplittingP p (LerayHirschDataEvenOf.of_graded L).chern
        (fun i => Gen.evenRestrictAdd (PN i) (hPN i)) m
```

Peer declarations consumed, all on main:
* lix-lh `CPn.eulerOfBundle_eq_of_bundleIsoOf` (`ChernEulerIsoOf`, 77c5176d3, UNVERIFIED, never probed).
  It holds for every `hgen`, so there is no stability hypothesis.
* lix-lh `LH.tautEulerDualK` and `LH.tautEulerDual_comapOf` (`LerayHirschChartClassGenK`, green).
* lix-coeff `LerayHirschDataEvenOf.of_graded` (`CohomologyLHRingDataOf`), whose `proj`, `rank` and
  `taut` are `rfl`.
* lix-cupone `prod_eq_zero_of_coverOf` (`CupVanishIterateOf`).
* The `F₂` geometry, green: `lineOpens`, `coverSup_lineOpens`, `tautLineIsoSummand`,
  `pushforwardBundleIso`, `trace_pushforward_one`, `Wu.flagLineFlat`, `Wu.sum_flagLineFlat`.

Still open beyond (d), and none of it was delivered:
* `L` and `L'`, the compact Leray–Hirsch over `K` with `taut = tautEulerDualK` (lix-lh).
* `hstage`, injectivity of `pull (cmap (projPi (flagRest E n)))` at each stage.
* The reduced powers `PN`/`PF` and their fields (lix-steenrod).

Traps for (d):
* `D'.taut = −tautEulerOfK`, so each factor is `−a + a` and closes by `neg_add_cancel`, not by
  `two_smul` as over `F₂`.
* `TotalHOf` is not commutative and `prod_eq_zero_of_coverOf` is stated with `List.prod`, so the
  product has to go through (iv).
* The coercions of `Gen.evenMap` and of `*`, `+`, `1` in `evenPart` are `rfl`.

## STEP 0

All thirteen `ParityP*` files of `sp-evenside` were already on origin byte-identical to the shared
tree; nothing unlanded, nothing in the attic.  `ParityPAxiomGuard` is compiled on main.

## GREEN (lix-c probes, `BUILT` lines, PROBE GREEN)

| module | probe | jobs | landed |
|---|---|---|---|
| `ParityPTwistSymm` | 0911-215611-68815 | 1615 | 5929e3699 (identical re-land) |
| `ParityPWuValue` | 0911-215611-68815 | 1615 | 5929e3699 (identical re-land) |
| `ParityPDecomposable` | 0911-220816-52720 | 1616 | b1467418a (identical re-land) |
| `ParityPWuComponent` | 0911-223415-30104 | 1655 | 251dd56c0 |
| `ParityPWuTransport` | 0911-223415-30104 | 1655 | 924c01f0c (identical re-land) |
| `ParityPSplitStepD` | 0911-224342-96729 | 1684 | 02d0df66c (identical re-land) |
| `ParityPWuAxiomGuard` | latest lix-c probe | 1686 | 2be49495a (identical re-land) |

## What is proved

* **L4a, the value** (`ParityPWuValue.eCoeff_twistSub_esymmSub_succ`): over a characteristic-zero
  domain, `eCoeff_{ip}(φ_κ(e_{i+1})) = (−1)^{i+ip}·κ^i·(ip+1)`.  Newton modulo decomposables pushed
  through the twist; only the `k = 1` binomial term reaches weight `ip+1`; the factor `i+1` cancels.
  The docstring carries both clauses of the sign convention (§1.6): odd `p` because `p − 1` is
  even, `p = 2` because `h ↦ −h` is the identity, and the invariance of the leading coefficient.
* **L4a, the membership** (`ParityPDecomposable.isDecomposable_of_eCoeff_eq_zero`): a symmetric
  `ℤ`-polynomial homogeneous of degree `N ≥ 1` with vanishing `e_N`-coefficient lies in
  `IsDecomposable (esymm ·) N`.  Via the crux (`eExpand_isWeightedHomogeneous`): every monomial of
  the `e`-expansion has weight `N`, the only linear one is `X_{N−1}`, so every surviving monomial
  has degree `≥ 2`.
* **L4a, universally** (`ParityPWuComponent.isDecomposable_wuRHSP`): `m_{(p^i,1)} −
  wuCoeff p i · e_{ip+1}` is decomposable, with `wuCoeff p i = (−1)^{i+ip}(ip+1)`; `m_{(p^i,1)}` is
  the degree-`(ip+1)` component of `φ_1(e_{i+1})` (`wuComp_eq_wuRHSP`); `isUnit_wuCoeff_cast`: a
  unit once `(p : K) = 0`.  No bound on the number of variables is needed.
* **Transport** (`ParityPWuTransport`): padding a finset-indexed family of roots to `Fin n`
  (`exists_pad`), evaluation of the universal identity, pull-back of decomposables along an
  injective hom (`IsDecomposable.exists_lift`), and `wu_isDecomposable_of_splitting` /
  `wu_field_of_splitting` / `isUnit_wuLeading` — exactly the fields `wu` and `c_isUnit` of
  `ParityPData`, with `c i = κ^i · wuCoeff p i` for `κ ∈ ℤ`.
* **The interface for the real objects** (`ParityPSplitStepD`): `ParityP.HasSplittingP` (the
  splitting principle with the extension hidden), `SplitStepDData` (Cartan, `P^0 = id`,
  `P(z) = z`, instability, `κ ∈ ℤ` a unit, `p = 0`, splitting), `toParityPData` deriving every
  field, and `SplitStepDData.gamma_top_eq_zero : γ ((∑ j ∈ u, d j) + (n + 1)) = 0` for `p ∣ n`,
  `p ∣ d_j` — the index order of the rank-generic `F₂` bridge `Gen.stepD_of_wu`.

## Scope 2 (lead's ruling, 09-11 23:00): the splitting principle over `K`, prefix `ChernSplittingOf*`

| module | probe | jobs | what |
|---|---|---|---|
| `ChernSplittingOfPowers` | lix-c, BUILT | 2321+ | `SplittingDataOf` (even parts), `SplittingDataOf.powerData`, `hasSplittingP_of_splittingDataOf`, `HasSplittingP.elim` |
| `ChernSplittingOfInjective` | lix-c, BUILT | 3421 | `totalHOf_map_id/comp`, `totalHOf_component_map`, `totalHOf_map_injective`, `flagProj_map_injective_of_proj` over any `CommRing K` |
| `ChernSplittingOfWhitney` | lix-c, BUILT | 3461 | on `LerayHirschDataEvenOf`: `chern_eq_coeff`, `chern_split_of_splitPoly`, `splittingDataOf_of_splitPoly`, `aeval_taut_map`, `splitPoly_of_splitRelation`, **`hasSplittingP_of_splitRelation`** |
| `ChernSplittingOfFlag` | lix-c, BUILT | 3463 | `flag_square`, **`hasSplittingP_flag`** (the bundle-level assembly) |
| `ChernSplittingOfAxiomGuard` | lix-c, BUILT | 3463 | `#audit_axioms` over the four modules |

Open inputs for the flag assembly (lix-lh / lix-coeff by the lead's ruling): compact Leray–Hirsch over
`K` and its `of_graded` into `LerayHirschDataEvenOf`; `tautEulerOf_comapOf`; the split relation at the
flag `∏_{l<r}(ξ' + π'^* e_K(flagLineFlat p r l)) = 0` in the even part.  The reduced powers on the flag
space are lix-steenrod's export.

Traps: `esymmOn` needs `CommRing`, so every splitting statement lives in `Gen.evenPart`; `map_mul`
applied to a ring hom coercion does not unify through `evenRestrictAdd` — pass the factors explicitly;
`cmap` lives in `CohomologyBridge`, which `BundleFlagStage` does not import.

## AUTHORED, UNVERIFIED

Nothing.  Every file this lane owns is compiled on main.

## NEEDS (for the real-object bridge; none blocks the algebra)

* `lix-steenrod`: the odd-primary export on `H^*(−; F_p)` as additive maps `P^i` with `P^0 = id`,
  the Cartan formula, instability, naturality, and `P(h) = h + κ·h^p` on degree-two classes with
  `κ ∈ F_p^×` (hence an integer cast).
* `lix-lh` / `lix-coeff`: Chern classes over `K` (`LerayHirschDataOf K` exists) and the splitting
  principle as an injective ring map into a flag-bundle cohomology carrying the roots, i.e. the
  data of `HasSplittingP`; the Künneth uniqueness for `z_inj`.
* `lix-cupone`: commutativity of the even part (`TotalH.mul_comm_of_even` or an even commutative
  subring), so that `H` is a `CommRing`.
* **Family ruling (21:35)**: ParityPData and SplitStepDData are stage-free and section-free; no
  section degree enters here.  The `k`-indexing is lix-evenside-n's instantiation.

## TRAPS

* `IsDecomposable` is only an additive subgroup, so it is closed under integer multiples and not
  under multiplication by an arbitrary scalar.  The normalisation constant must enter as an integer
  cast (automatic over `F_p`).
* The `ℤ`-scalar action on a symmetric subalgebra over `ℤ` has two instance paths (the algebra
  action and `zsmul`).  Stating `c • esymmSub` in a `ℤ`-specific proof risks a mismatch with lemmas
  elaborated at a generic `R`.  The fix used here: an anonymous-constructor element `⟨C c * ↑g, hx⟩`
  plus a generic-`R` lemma `eCoeff_C_mul`.
* `Finset.sum_powerset` needs `import Mathlib.Algebra.BigOperators.Group.Finset.Powerset`.  Without
  it the error is `Unknown constant`, although the name is the `to_additive` of `prod_powerset`.
* An unused hypothesis is a hard error (`Variable name hn is not explicitly referenced`); here it
  showed that the L4a membership needs no bound on the number of variables.
* `rw` cannot rewrite inside a beta-redex goal such as `(fun x => g (e x) ^ p) x = …`; use
  `congrArg` in term mode, or `show` first.
