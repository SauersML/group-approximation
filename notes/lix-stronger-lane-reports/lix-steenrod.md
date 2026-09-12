# lix-steenrod — final report (wound down 2026-09-12)

**Status: STOPPED.** The lead ordered all LIX-stronger lanes to stop, relayed by lix-cupone on 2026-09-12; lix-tower's wind-down confirms it. There was no new authoring and no new probe after the order. Nothing was deleted, and every file below is on main for a later restart.

Owns `CharClass/OddP*` except `OddPDescent*` (lix-descent) and `OddPWDiagonal*` (lix-tower).

## LANDED on main
| sha | module | state |
|---|---|---|
| 7e2fb5081 | `CharClass/OddPDiagonal` | UNVERIFIED — never reached (imports a red module) |
| b07f2e96c | `CharClass/OddPDiagonalSrc` | UNVERIFIED — never reached (imports a red module) |
| 93494e31f | `CharClass/OddPDiagonalAug` | **RED** at probe 0912-092529-64114, see below |
| 00bd390be | `CharClass/OddPTupleFunctor` | GREEN (compiled evidence `lix-steenrod.green.0911-234607-62890`) |
| 2304ffd1f, fa6459269 | `CharClass/OddPTupleAction`, `CharClass/OddPTupleD` | GREEN (`lix-steenrod.green.0911-222411-66645`) |

All three `OddPDiagonal*` modules are unwired: nothing imports them and no root import reaches them.

## RED — `OddPDiagonalAug` (probe 0912-092529-64114, base e725a36e2)
```
OddPDiagonalAug.lean:262:0: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
OddPDiagonalAug.lean:271:8: (kernel) unknown constant 'GroupApproximation.CharClass.tupD_exists_preimage_stdSimplexTop_zmod'
```
The first error is in the body of `tupD_exists_preimage_stdSimplexTop_zmod`:
```lean
  tupD_exists_preimage_stdSimplexTop (ZMod p) n r k y hy
```
The second error is a cascade: `oddTgt_acyclicOnModels` uses the failed theorem, but its own elaboration went through.

**Diagnosis (hypothesis, not tested).** The export `tupD_exists_preimage_stdSimplexTop (K : Type) [Field K]` (OddPAcyclic:239) elaborates `tupD` at `Field.toCommRing`. The target elaborates it at `ZMod.commRing p`. In one application, `hy` is unified against `@tupD (ZMod p) (Field.toCommRing ?inst) …` while the `Field (ZMod p)` argument may still be pending, and unification then unfolds `tupD`. The instance diamond itself should be cheap: at the Mathlib pin, `Mathlib/Algebra/Field/ZMod.lean:30` (`instance : Field (ZMod p)`) gives only `mul_inv_cancel`, `inv_zero`, `nnqsmul`, `qsmul`, so `toCommRing` is filled by instance synthesis.

**Candidate fix (not authored, per the stop order).** Apply it to both wrappers: the positive-degree one at `OddPDiagonalAug:263`, and `tupD_exists_preimage_zero_stdSimplexTop_zmod` at `OddPDiagonal:38`, which the probe never reached and which has the same shape.
```lean
  := by
  have h := tupD_exists_preimage_stdSimplexTop (ZMod p) n r k   -- instance synthesized here
  exact h y hy
```
Second choice is to generalise the instance, so unification compares only ring structures:
```lean
  have key : ∀ inst : CommRing (ZMod p), inst = Field.toCommRing →
      ∀ y : @tupMod (ZMod p) inst (stdSimplexTop n) r (k + 1),
        @tupD (ZMod p) inst (stdSimplexTop n) r k y = 0 →
        ∃ z : @tupMod (ZMod p) inst (stdSimplexTop n) r (k + 2),
          @tupD (ZMod p) inst (stdSimplexTop n) r (k + 1) z = y := by
    rintro inst rfl y hy
    exact tupD_exists_preimage_stdSimplexTop (ZMod p) n r k y hy
  exact key (ZMod.commRing p) rfl y hy
```
Write `ZMod.commRing p` explicitly. With `_`, the `rfl` assigns `Field.toCommRing`, and `hy` meets the diamond again. After a fix, probe `OddPDiagonalAug OddPDiagonalSrc OddPDiagonal` together.

## INTERFACE — `CharClass/OddPDiagonal` (sent to lix-descent 2026-09-12)
Variables `(p : ℕ) [NeZero p]`; every declaration also takes `[Fact p.Prime]`.
- Δ0 `def oddDiagonal (r s : ℕ) (hs : r ∣ s * p) : oddSrc p (oddSingularBoundary p) ⟶ oddTgt p r s hs` — `acyclicModelsMap (oddSrcFree p (oddSingularBoundary p)) (oddTgt_acyclicOnModels p r s hs) (srcAug p) (tgtAug p r s hs) (oddTgt_acyclicZeroOnModels p r s hs) (diagF0 p r s hs) (diagF0_natural p r s hs) (diagF0_aug p r s hs)`
- Δ0' `def oddDiagApp (X : TopCat.{0}) (k : ℕ) (x : OddWTensor p k X) : tupMod (ZMod p) X p k := (((oddDiagonal p p 1 (dvd_mul_left p 1)).app X).f k).hom x`
- Δ1 `oddDiagApp_d X k (x : OddWTensor p (k + 1) X) : tupD (ZMod p) X p k (oddDiagApp p X (k + 1) x) = oddDiagApp p X k (oddDiff p (oddSingularBoundary p) X k x)`
- Δ2 `oddDiagApp_natural {X Y} (f : X ⟶ Y) k x : tupMap (ZMod p) f p k (oddDiagApp p X k x) = oddDiagApp p Y k (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k) x)`
- Δ3 `oddDiagApp_add X k x y : oddDiagApp p X k (x + y) = oddDiagApp p X k x + oddDiagApp p X k y`
- Δ4 `oddDiagApp_smul X k (c : GroupRingZMod p) x : oddDiagApp p X k (c • x) = galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) c (oddDiagApp p X k x)`
- Δ5 `oddDiagApp_grGen X k x : oddDiagApp p X k (grGen p • x) = tupT (ZMod p) X p k (oddDiagApp p X k x)`
- Δ6 `oddDiagApp_zero X (x : stdSimplexTop 0 ⟶ X) : oddDiagApp p X 0 (Finsupp.single (⟨0, x⟩ : WSIndex 0 X) (1 : GroupRingZMod p)) = Finsupp.single (diagPt X p x) (1 : ZMod p)`
- helpers: `oddTgt_acyclicZeroOnModels`, `tupD_exists_preimage_zero_stdSimplexTop_zmod`, `oddSrc_obj_d`; in `OddPDiagonalAug`: `oddTgt_obj_d (r s hs X k) : ((oddTgt p r s hs).obj X).d (k + 1) k = tupDHom p X r k s hs`, `tgtAug`, `oddTgt_acyclicOnModels`; in `OddPDiagonalSrc`: `srcAug`, `diagPt`, `diagF0`, `diagF0_natural`, `diagF0_aug`.

## RESIDUAL — not authored (planned statements; no declarations exist)
Notation: `u ∈ C^q(X; F_p)` is a cocycle, and `D_j(u)(σ) = tupEval (ZMod p) X p (p*q) (fun _ => Pi.single q u) (Δ(e_j ⊗ σ))` for a `(pq − j)`-simplex `σ`. Here `Δ` is `oddDiagApp p X (p*q)` on the source generator of `W`-degree `j`; lix-descent's `OddPCochain` owns `D_j`.
1. **Top power (`OddPTopPower`).** `[D_0(u)] = [u ⌣ ⋯ ⌣ u]` (`p` factors) in `H^{pq}(X; F_p)`. Route (plan `sp-steenrod.md` §4.2): the non-equivariant acyclic-models homotopy, at `Λ = F_p` rather than the group ring, between `Δ(e_0 ⊗ −)` and the iterated Alexander–Whitney diagonal `Φ₀^{(p)}`. It owes no constant.
2. **`P^0` / κ.** Discharge `EvalIsHeadCoeff (ZMod p) ev` (`OddPDescentValue:301`, `∀ x : EMod K p, ev x = x (eHeadWord p)`). Here `ev` is the `tupEval` evaluation of the `p`-fold Alexander–Whitney diagonal of the fundamental 1-simplex. The constant then follows from `eDescent_value_of_eval` (`OddPDescentValue:330`): `ev (eA K m) = m!` for `p = 2m + 1`. It is a unit by `eDescent_value_isUnit`, and the closed endpoint is `printedOddPDescentConstant`.
3. **Cartan comparison.** Coordinate with lix-tower. Green on main: `psiW`, `psiW_chainMap`, `psiW_grGen_mul`, `psiW_counitLeft/Right`. `OddPShuffle` was never authored. Its planned statements are in `notes/lix-stronger-lane-reports/lix-tower.md` (608bb4c98): `tupRiffleAll K X m` with sign `(−1)^{Σ_j |y_j|·Σ_{l>j} |x_l|}`, `tupBlockRotAll`, `tupRiffleAll_mul_tupDAll`, and `tupRiffleAll_conj : tupRiffleAll K X m * tupBlockRotAll K X m = tupTAll K X (2 * m) ^ 2 * tupRiffleAll K X m`, plus degree-`k` twins.

## TRAPS
- The degree-`0` lemma of the acyclic-models existence theorem is `acyclicModelsMap_zero`. `acyclicModelsMap_app_f_zero` does not exist.
- lix-cupone's acyclicity exports are stated at `[Field K]`, while the target uses `ZMod.commRing p`. See RED above: synthesize the export's instance before unifying the hypothesis.
- `ChainComplex.of` guards `d i j` by a `dite`. Rewrite `d (k+1) k` through `oddTgt_obj_d` / `oddSrc_obj_d`, and for `d 1 0` pass `oddTgt_obj_d … 0` through `show … from`.
- `oddDiagApp_grGen`: `moduleOfOrderP_smul` gives `(tupT … ^ 1) v`, not `tupT … v`. State it as a `have`, then `rw [h, pow_one]`.
- A scratch diamond probe (`OddPZmodDiamondProbe`, `rfl` tests of `ZMod.commRing p = Field.toCommRing`) was never landed or compiled. It is kept in the lane backup, not on main.
