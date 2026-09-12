# Lane `lix-evenside` — Step D mod `p`, the even side (successor of `sp-evenside`)

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.4.  Design: `sp-design.md` §3.2–3.4.
Predecessor report: `notes/lix-stronger-lane-reports/sp-evenside.md` (deliverable 1 and the L4a
infrastructure, all on main and green).  Clone: `lix-c` (shared with lix-evenside-n, lix-steenrod;
rule 20).  Owns `CharClass/ParityP*`, `CharClass/StepDModP*`.

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
