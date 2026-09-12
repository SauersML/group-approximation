# lx-integrator: LIX-strong swarm lane (clone now lix-s)

Re-tasked 2026-09-12 ~10:25 CDT from integration to authoring: the F₂ rank-n slice value, the `slice` leaf of `Gen.WuStepDData` (lix-evenside-n STOPPED residual (b)).  Prefix `CharClass/SliceGen*` except `SliceGenOf*` (lx-sliceK).

## GREEN
- `CharClass/SliceGenValue.lean`, landed 970d1f3e6.  Probe 0912-104840-68239 on base 970d1f3e6: PROBE GREEN, `BUILT GroupApproximation.CharClass.SliceGenValue`, 9235 jobs, 1 module rebuilt.  The probed md5 d9e0e351… equals the bytes on main.
  - `Gen.vSliceValue_sliceGen` depends on axioms `[propext, Classical.choice, Quot.sound]`.
  - Declarations:
    - `Gen.splitRelation_V n dd root hroot`
    - `Gen.lineEulerOf_vLineYBundle_inl n dd i` (value 0)
    - `Gen.lineEulerOf_vLineYBundle_inr n β hd` (value: the pulled-back `cpGen`)
    - `Gen.sliceGen_eq_rootN n dd hdd β`
    - `Gen.vRootE n dd l`, `Gen.vRootE_equiv n dd k`
    - **`Gen.VSliceValue n dd gen`**: `∀ q, TotalH.of (KnTwo.YTop (baseY dd)) (2 * q) (LH.chernOf (vBundleY n dd) (KGen.lixRank n dd) (rank_vBundleY n dd) (kgenLixRank_pos n dd) q) = (sliceClass univ gen dd).coeff q`
    - **`Gen.vSliceValue_sliceGen n dd hdd : VSliceValue n dd (LH.sliceGen dd hdd)`**
  - Built on lx-sliceK's coefficient-free `SliceGenOfLines` and `SliceGenOfBlocks` (fbdce4552), with rank-two `SliceValueV` as the F₂ toolkit import.
- Earlier, as integrator:
  - `notes/lix-strong-swarm/BOARD.md` landed at 40801adec and 19b478821; the board refresh was dropped by lead order.
  - Tops probe 0912-100606-67380: GREEN.
  - Probe 0912-102247-19148: red in lx-pzero's `OddPTotalInterface:111:37`, an unused `hd`. Routed to lx-pzero.
  - Probe 0912-102928-74491 of `ProblemLIXStrongAssemblyTwo` and `…OddP`: GREEN, restore only. lx-endpoint holds the BUILT evidence, and OddP has changed since, at 972f81ac4.
  - Duplicate scan at c3b58d90c: the only name collisions are in the parked `OddPTupleBd`/`OddPTupleSlot`. lx-diag acknowledged.

## AUTHORED, UNVERIFIED
- none

## NEEDS
- none.  The consumer is lx-slice2: `LIXStepDGenSlice*` needs the mapping-torus → V bridge plus `Gen.vSliceValue_sliceGen n (LIX.Gen.lixDD n j) hdd`, where `hdd` is rank-n positivity of `lixDD`.

## SPLIT
- No open sub-task in this lane; the leaf is a theorem.

## TRAPS
- Positivity spelling: `LH.chernOf`'s `hs1 : 1 ≤ s` accepts `kgenLixRank_pos n dd : 0 < KGen.lixRank n dd` by defeq.  Consumers stating it with `KGen.one_le_lixRank n dd` still unify, since the proofs are irrelevant.
- Two `lixRank`s: `Gen.lixRank` (LIXShapeGenericRank) and `KGen.lixRank` (LIXKGenPunctured) are definitionally equal but not syntactically.  Always write `KGen.lixRank` in the slice layer, to match `Gen.rank_vBundleY`.
- Two `cpTaut`s: `Bundle.cpTaut` (the tautological bundle) and `KnCP.cpTaut` (a class).  Only the first is reachable through `open Bundle`.
- An empty-overlay probe of unchanged tops reports `mentioned-not-built` (restored by input hash).  It is a consistency check, not a compile.
