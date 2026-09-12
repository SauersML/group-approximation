# lx-sliceK — the slice value over a field K at sphere rank n (gen / slice fields of Gen.RealBundleModP)

Lane of the LIX strongest swarm.  Owns `CharClass/Slice*Of*`, `CharClass/SliceGenOf*`.  Clone lix-h.

## GREEN
Probe 0912-110336-46269 (PROBE GREEN, 9276 jobs, each module with its own BUILT line; the evidence records every
overlay file COMPILED), after probe 0912-103638-13353 (first four green, SliceRootsOf red, fixed).
`Gen.sliceValue_lixBundleOf` depends on axioms `[propext, Classical.choice, Quot.sound]`.

| file | main declarations |
|---|---|
| SliceGenOfLines | coefficient-free rank-n lines of `V = 1^{n+1} ⊕ H`: `Gen.trivLine`, `Gen.hLine`, `Gen.vLineY`, `Gen.vLine`, `Gen.VmatY(_eq)`, `Gen.VmatY_eq_sum_lines`, `Gen.Vmat_eq_sum_lines`, `Gen.vBundleY`, `Gen.rank_vBundleY` (= `KGen.lixRank n dd`), `Gen.kgenLixRank_pos`, `Gen.vLineYBundle`, `Gen.trace_vLineYBundle`, `Gen.vIndexEquiv`, `Gen.vLineYFlat`, `Gen.VmatY_eq_sum_rangeY`, `Gen.vLineFlatBundle`, `Gen.sum_vLineFlatBundle`, `Gen.blockEmb`, `Gen.vLineY_inr_eq`, `Gen.vLineYBundle_inr_eq` |
| SliceGenOfBlocks | `Gen.prod_blocks_eq_sliceClass` (n + 1 constant lines, any commutative ring) |
| SliceHomogeneousOf | `exists_of_prodOf`, `of_component_of_prodOf`, `of_component_esymmOnOf` |
| SliceValueVOf | `evenTautOf_zero`, `evenMap_id_apply`, `nontrivial_evenPartOf`, `LerayHirschDataEvenOf.chern_eq_esymmOn_of_splitRelationOf` (Whitney for one bundle), `.chern_eq_sliceClass_coeffOf` (the slice value), `.chern_map_of_squareOf` (naturality) |
| SliceRootsOf | `Gen.eulerOfBundleOf_congr`, `Gen.eulerOfBundleOf_pushforward_eq_zero_of_const`, `Gen.vRootOf(_inl/_inr)`, `Gen.blockTautEmb`, `Gen.blockClassOf(_congr)`, `Gen.sliceGenOf`, `Gen.evenTautOf_vRootOf_inr`, `Gen.vRootFlatOf(_equiv)`, and after a pushforward `u`: `Gen.vRootPushOf`, `Gen.blockPushEmb`, `Gen.blockClassPushOf(_congr)`, `Gen.sliceGenPushOf`, `Gen.evenTautOf_vRootPushOf_inr`, `Gen.vRootFlatPushOf(_equiv)` |
| SliceNaturalOf | `chern_comap_of_gradedOf` |
| SliceSplitVOf | `Gen.splitRelation_vBundleYOf`, `Gen.vSliceValueOf`, `Gen.sum_pushforward_vLineFlatBundle`, `Gen.splitRelation_pushOf`, `Gen.vSliceValuePushOf`, `Gen.sliceValue_of_comapOf` |
| SliceTorusOf | `Gen.comap_lixBundle_eq_pushforward_vBundleY`, **`Gen.sliceValue_lixBundleOf`** |

Landings: fbdce4552, b129f04e1, a00490bdf, 0e1c65353.

## THE DELIVERABLE (lx-bundleP's `hslice`)
```
theorem Gen.sliceValue_lixBundleOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (s : C(baseY dd, ↥sphereOne × baseM n dd)) (q : ↥(unitVectors (Fin (n + 1))))
    (hs : ∀ y, s y = (southPole, ((q, y) : baseM n dd)))
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2)
    (LE : LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd))
    (LV : LerayHirschGraded (projMapOf (pushforward Sum.inr Sum.inr_injective (vBundleY n dd)))
      (LH.tautEulerDualK K hgen (pushforward Sum.inr Sum.inr_injective (vBundleY n dd))) (KGen.lixRank n dd))
    (k : ℕ) :
    Gen.evenMap K (cmap s) ((LerayHirschDataEvenOf.of_graded LE).chern k)
      = (sliceClass Finset.univ (sliceGenPushOf K n Sum.inr Sum.inr_injective hgen) dd).coeff k
```
Proved inside: the slice equation (the mapping torus on the south polar slice is `V` pushed along `Sum.inr`), naturality
of the even-part Chern classes under the pullback, the split relation at the flat family of lines (lx-splitK's
`splitRelation_of_sumOf`), roots zero on the `n + 1` constant lines and the pulled-back class of the tautological line
on every block line, reciprocal Vieta and the block product.  No generator is canonical over K and none is needed.

## NEEDS
- lx-lhK-b: `LH.lerayHirschGraded_compactOf` / `…DualOf` for `LE` and `LV`, the only open inputs.

## SPLIT
- none: the slice field is authored and compiled.

## TRAPS
- `Gen.lixRank_pos` already exists (at `Gen.lixRank`); the `KGen.lixRank` positivity is `Gen.kgenLixRank_pos`.
- `projMapOf` is `LH.projMapOf`.
- A hole `_` for a block `β` in `blockEmb_injective n _`, under the dependent domain `Fin (dd β.1 + 1)`, times out
  `isDefEq`.  Name the composite injection as a definition with explicit arguments.
- A `show` is needed before rewriting under `(of_graded L).rank` vs `KGen.lixRank n dd`: they are defeq, not syntactic.
