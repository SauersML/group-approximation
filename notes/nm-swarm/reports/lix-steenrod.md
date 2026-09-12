# lix-steenrod — running report (relaunch 2026-09-12)

Owns `CharClass/OddP*` except `OddPDescent*` (and the OddPWDiagonal* files lix-tower authored). Clone lix-c (shared).

## LANDED on main
| sha | module | state |
|---|---|---|
| 7e2fb5081 | `CharClass/OddPDiagonal` | unverified, in probe |
| 93494e31f | `CharClass/OddPDiagonalAug`, `CharClass/OddPDiagonalSrc` | unverified, in the same probe |
| 00bd390be | `CharClass/OddPTupleFunctor` | COMPILED (green 0911-234607) |
| 2304ffd1f, fa6459269 | `CharClass/OddPTupleAction`, `CharClass/OddPTupleD` | COMPILED (green 0911-222411) |

## PROBE
- batch `OddPDiagonalAug` + `OddPDiagonalSrc` + `OddPDiagonal` (clone lix-c): running.

## INTERFACE — `CharClass/OddPDiagonal` (for lix-descent's OddPCochain / OddPClasses / OddPAdditive)
- `oddDiagonal p [NeZero p] [Fact p.Prime] r s (hs : r ∣ s * p) : oddSrc p (oddSingularBoundary p) ⟶ oddTgt p r s hs`
- `oddDiagApp p X k (x : OddWTensor p k X) : tupMod (ZMod p) X p k := (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom x`
- `oddDiagApp_d X k (x : OddWTensor p (k + 1) X) : tupD (ZMod p) X p k (oddDiagApp p X (k + 1) x) = oddDiagApp p X k (oddDiff p (oddSingularBoundary p) X k x)`
- `oddDiagApp_natural (f : X ⟶ Y) k x : tupMap (ZMod p) f p k (oddDiagApp p X k x) = oddDiagApp p Y k (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k) x)`
- `oddDiagApp_add X k x y`; `oddDiagApp_smul X k c x : oddDiagApp p X k (c • x) = galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) c (oddDiagApp p X k x)`
- `oddDiagApp_grGen X k x : oddDiagApp p X k (grGen p • x) = tupT (ZMod p) X p k (oddDiagApp p X k x)`
- `oddDiagApp_zero X (x : stdSimplexTop 0 ⟶ X) : oddDiagApp p X 0 (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) 1) = Finsupp.single (diagPt X p x) 1`
- helpers: `oddTgt_acyclicZeroOnModels`, `tupD_exists_preimage_zero_stdSimplexTop_zmod`, `oddSrc_obj_d`.

## NEXT
1. green → re-land the three modules normally.
2. top-power identity `P^{q/2} u = u^p`: the second acyclic-models comparison (the `W`-degree-top component of Δ on the diagonal simplex).
3. `P^0` / κ with `EvalIsHeadCoeff` (the p-fold AW evaluation of a degree-one element is the head coefficient; lix-descent's constant export `printedOddPDescentConstant`).
4. Cartan comparison, coordinated with lix-tower's `OddPWDiagonal*`.

## TRAPS
- The degree-`0` lemma of the acyclic-models existence theorem is `acyclicModelsMap_zero`; `acyclicModelsMap_app_f_zero` does not exist.
- lix-cupone's acyclicity exports are stated at `[Field K]`, while the target complex uses `ZMod.commRing p`: state a `_zmod` wrapper at `ZMod p` and apply the export inside it.
- `ChainComplex.of` guards `d i j` by a `dite`; rewrite `d (k+1) k` through `oddTgt_obj_d` / `oddSrc_obj_d`, and for `d 1 0` pass `oddTgt_obj_d … 0` through `show … from`.
