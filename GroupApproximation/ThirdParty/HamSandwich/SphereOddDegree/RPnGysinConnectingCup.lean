import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnecting
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnW1ClassEqActualRPAlpha
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferSES
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CochainCupLeibniz
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib

/-!
# The Smith/Gysin connecting map is cup product with `actualRPAlpha`

This file proves, at the level of singular cochains, that the Smith/Gysin
connecting homomorphism `rpGysinConnecting n k : Hᵏ(RPⁿ; F₂) ⟶ Hᵏ⁺¹(RPⁿ; F₂)`
(the connecting map of the dualized Smith short exact sequence
`transferSEScoch n`) is cup product with the canonical class `α = actualRPAlpha n`
(the first Stiefel–Whitney class of the double cover):

```text
rpGysinConnecting n k x = cupZMod2 x (actualRPAlpha n).
```

## Proof strategy (a two-sheeted cover)

Represent a class `x = [c]` by a cocycle `c ∈ Cᵏ(RPⁿ)`.  A lift of `c` along the
cochain transfer `tr* = g` is the cochain `gysinLift n k c` on `Sⁿ`, defined by

```text
(gysinLift c)(τ) = c(sProj τ) · sheetParity(τ(last vertex)),
```

where `sProj τ` is the projected simplex and `sheetParity` measures which sheet a
sphere point lies on.  Because the two lifts of a base simplex are antipodal and
`sheetParity` flips under the antipode, `tr*(gysinLift c) = c`
(`transfer_gysinLift`).

The coboundary of the lift descends, and the key `dc = 0` computation shows that
its descent is *exactly* the Alexander–Whitney cochain cup `c ⌣ w₁`
(`f_cup_eq_coboundary`).  Feeding these two cochain facts into Mathlib's
element-level connecting-map formula `ShortComplex.ShortExact.δ_apply` yields the
identity in cohomology.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Charts, vertex sheets and the lifted cochain -/

/-- The underlying continuous map `Δᵏ → Sⁿ` of a singular `k`-simplex `τ` of the
sphere (the `toSSetObjEquiv` chart, matching the convention used by `sProj`). -/
noncomputable def sChart (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    C(stdSimplex ℝ (Fin (k + 1)), Sphere n) :=
  TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) τ

/-- The underlying continuous map `Δᵏ → RPⁿ` of a singular `k`-simplex `σ` of
`RPⁿ`. -/
noncomputable def rpChart (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    C(stdSimplex ℝ (Fin (k + 1)), RP n) :=
  TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) σ

/-
The chart of the projected simplex is `proj n` composed with the sphere chart.
-/
theorem rpChart_sProj (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) (x) :
    rpChart n k (sProj n k τ) x = proj n (sChart n k τ x) := by
  convert congr_arg ( fun f => f x ) ( Equiv.apply_symm_apply ( TopCat.toSSetObjEquiv ( TopCat.of ( RP n ) ) ( Opposite.op ( SimplexCategory.mk k ) ) ) ( ( proj n ).comp ( sChart n k τ ) ) ) using 1

/-
**Antipode flips the chart.** The chart of the deck-image `sAnti τ` is the
negation of the chart of `τ`.
-/
theorem sChart_sAnti (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k)
    (x : stdSimplex ℝ (Fin (k + 1))) :
    sChart n k (sAnti n k τ) x = -(sChart n k τ x) := by
  convert Homeomorph.apply_symm_apply ( _ : _ ≃ₜ _ ) _ using 1

/-- The **sheet parity of the last vertex** of a sphere `k`-simplex `τ`. -/
noncomputable def gLastSheet (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) : ZMod 2 :=
  sheetParity n (sChart n k τ (stdSimplex.vertex (Fin.last k)))

/-- **The lifted cochain.** `gysinLift n k c ∈ Cᵏ(Sⁿ; F₂)` lifts the cocycle
`c ∈ Cᵏ(RPⁿ; F₂)` along the cochain transfer. -/
noncomputable def gysinLift (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k) :
    singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) k :=
  Sigma.desc (fun τ =>
    ModuleCat.ofHom ((cochainEval k c (sProj n k τ) * gLastSheet n k τ)
      • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

/-- Evaluation of `gysinLift`. -/
theorem gysinLift_eval (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    cochainEval k (gysinLift n k c) τ = cochainEval k c (sProj n k τ) * gLastSheet n k τ := by
  show (gysinLift n k c).hom _ = _
  unfold gysinLift
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (Sigma.ι_desc (fun (τ : singularSimplices (TopCat.of (Sphere n)) k) =>
      ModuleCat.ofHom ((cochainEval k c (sProj n k τ) * gLastSheet n k τ)
        • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))) τ)) (1 : ZMod 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simpa [cochainEval, ModuleCat.hom_ofHom] using h

/-- **The antipode toggles the last-vertex sheet parity.** -/
theorem gLastSheet_sAnti (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    gLastSheet n k (sAnti n k τ) = gLastSheet n k τ + 1 := by
  unfold gLastSheet
  rw [sChart_sAnti, sheetParity_neg]

/-! ## 2. Face/vertex combinatorics of the charts -/

/-
**Faces commute with projection.**
-/
theorem sProj_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    sProj n k (faceSimplex (TopCat.of (Sphere n)) k i ρ)
      = faceSimplex (TopCat.of (RP n)) k i (sProj n (k + 1) ρ) := by
  congr! 1

/-
**Vertex of a face.** The `j`-th vertex chart-value of the `i`-th boundary
face of `ρ` is the `(i.succAbove j)`-th vertex chart-value of `ρ`.
-/
theorem sChart_faceSimplex_vertex (n k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    sChart n k (faceSimplex (TopCat.of (Sphere n)) k i ρ) (stdSimplex.vertex j)
      = sChart n (k + 1) ρ (stdSimplex.vertex (i.succAbove j)) := by
  unfold sChart; simp +decide [ faceSimplex ] ;
  simp +decide [ TopCat.toSSetObjEquiv, TopCat.toSSet ];
  simp +decide [ Homeomorph.ulift, ConcreteCategory.homEquiv ];
  simp +decide [ Homeomorph.continuousMapCongr, TopCat.uliftFunctor ];
  simp +decide [ Equiv.ulift, stdSimplex.map_vertex, SimplexCategory.δ ];
  congr

/-- **Last-vertex sheet of a face**, in terms of the vertices of `ρ`. -/
theorem gLastSheet_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    gLastSheet n k (faceSimplex (TopCat.of (Sphere n)) k i ρ)
      = sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (i.succAbove (Fin.last k)))) := by
  unfold gLastSheet
  rw [sChart_faceSimplex_vertex]

/-
**The front `k`-face is the last boundary face.**
-/
theorem frontSimplex_eq_lastFace (n k : ℕ) (σ' : singularSimplices (TopCat.of (RP n)) (k + 1)) :
    frontSimplex (TopCat.of (RP n)) k 1 σ'
      = faceSimplex (TopCat.of (RP n)) k (Fin.last (k + 1)) σ' := by
  simp +decide [ frontSimplex, faceSimplex ];
  convert rfl;
  ext i;
  simp +decide [ SimplexCategory.δ, frontFace ]

/-! ## 3. `w₁` on the back edge -/

/-
**Lift-independence of `w1Value`.** For any singular `1`-simplex `σ` of `RPⁿ`
and any continuous lift `g : Δ¹ → Sⁿ` of its chart, the `w₁` value of `σ` is the
sum of the sheet parities of `g` at the two endpoints.
-/
set_option maxHeartbeats 1000000 in
theorem w1Value_of_lift (n : ℕ) (σ : singularSimplices (TopCat.of (RP n)) 1)
    (g : C(stdSimplex ℝ (Fin 2), Sphere n)) (hg : ∀ x, proj n (g x) = rpChart n 1 σ x) :
    w1Value n σ
      = sheetParity n (g (stdSimplex.vertex 0)) + sheetParity n (g (stdSimplex.vertex 1)) := by
  unfold w1Value;
  have h_lift : ∀ a : stdSimplex ℝ (Fin 2), g a = simplexLift n 1 σ (ULift.up a) ∨ g a = -(simplexLift n 1 σ (ULift.up a)) := by
    intro a
    have h_lift : proj n (g a) = proj n (simplexLift n 1 σ (ULift.up a)) := by
      have := simplexLift_spec n 1 σ;
      convert hg a using 1;
      convert congr_fun this ⟨ a ⟩ using 1;
    grind +suggestions;
  have h_lift_cases : (g (stdSimplex.vertex 0) = simplexLift n 1 σ (ULift.up (stdSimplex.vertex 0)) ∧ g (stdSimplex.vertex 1) = simplexLift n 1 σ (ULift.up (stdSimplex.vertex 1))) ∨
                      (g (stdSimplex.vertex 0) = -(simplexLift n 1 σ (ULift.up (stdSimplex.vertex 0))) ∧ g (stdSimplex.vertex 1) = -(simplexLift n 1 σ (ULift.up (stdSimplex.vertex 1)))) := by
                        have h_lift_cases : IsConnected (Set.range (fun a : stdSimplex ℝ (Fin 2) => if g a = simplexLift n 1 σ (ULift.up a) then 0 else 1 : stdSimplex ℝ (Fin 2) → ZMod 2)) := by
                          apply_rules [ isConnected_range ];
                          refine' continuous_iff_continuousAt.mpr _;
                          intro x;
                          by_cases hx : g x = simplexLift n 1 σ (ULift.up x);
                          · refine' tendsto_const_nhds.congr' _;
                            filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq g.continuous <| show Continuous fun a => - ( simplexLift n 1 σ { down := a } ) from Continuous.neg <| by continuity ) <| show g x ≠ - ( simplexLift n 1 σ { down := x } ) from by
                                                                                                                                                                                                                                                                grind +suggestions ] with y hy using by
                                                                                                                                                                                                                                                                grind;
                          · refine' tendsto_const_nhds.congr' _;
                            filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq g.continuous <| show Continuous fun a : stdSimplex ℝ ( Fin 2 ) => simplexLift n 1 σ { down := a } from by continuity ) hx ] with y hy using by aesop;
                        have := h_lift_cases.isPreconnected.subsingleton ( Set.mem_range_self ( stdSimplex.vertex 0 ) ) ( Set.mem_range_self ( stdSimplex.vertex 1 ) ) ; simp_all +decide ;
                        grind;
  cases h_lift_cases <;> simp +decide [ * ];
  · rfl;
  · rw [ sheetParity_neg, sheetParity_neg, show simplexVertex 1 0 = (⟨stdSimplex.vertex 0⟩ : _) from rfl,
      show simplexVertex 1 1 = (⟨stdSimplex.vertex 1⟩ : _) from rfl ]
    generalize sheetParity n ((simplexLift n 1 σ) ⟨stdSimplex.vertex 0⟩) = a
    generalize sheetParity n ((simplexLift n 1 σ) ⟨stdSimplex.vertex 1⟩) = b
    revert a b
    decide

/-
**The back-edge value of `w₁`.** Evaluated on the back `1`-face
`backSimplex k 1 σ'` (the edge on the last two vertices) of `σ' = sProj ρ`, the
`w₁` cochain is the sum of the sheet parities of `ρ` at vertices `k` and `k+1`.
-/
theorem w1Cochain_backSimplex (n k : ℕ)
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    cochainEval 1 (w1Cochain n) (backSimplex (TopCat.of (RP n)) k 1 (sProj n (k + 1) ρ))
      = sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (Fin.castSucc (Fin.last k))))
        + sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (Fin.last (k + 1)))) := by
  convert w1Value_of_lift n (backSimplex _ _ _ _) _ _ using 1;
  convert w1Cochain_eval n _ using 1;
  rotate_left;
  exact ( sChart n ( k + 1 ) ρ ).comp ( ContinuousMap.mk ( stdSimplex.map ( backFace k 1 |> SimplexCategory.Hom.toOrderHom ) ) ( by continuity ) );
  · intro x; exact (by
    convert rpChart_sProj n ( k + 1 ) ρ ( stdSimplex.map ( backFace k 1 |> SimplexCategory.Hom.toOrderHom ) x ) using 1);
  · congr! 2;
    · simp +decide [ stdSimplex.vertex, backFace ];
      congr;
    · simp +decide [ backFace, stdSimplex.map_vertex ];
      congr! 2;
      exact Fin.ext ( by simp +decide [ add_comm ] )

/-! ## 4. Evaluation of the two transfer/pullback cochain maps -/

/-
**Evaluation of the cochain transfer** `g = tr*` on a basis simplex.
-/
theorem transferCochain_eval (n k : ℕ) (b : singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) k)
    (σ : singularSimplices (TopCat.of (RP n)) k) :
    cochainEval k (((transferSEScoch n).g.f k).hom b) σ
      = cochainEval k b (canLift n k σ) + cochainEval k b (sAnti n k (canLift n k σ)) := by
  convert ModuleCat.comp_apply _ _ _ using 1;
  convert Iff.rfl;
  rotate_left;
  exact ZMod 2;
  exact inferInstance;
  exact ModuleCat.of ( ZMod 2 ) ( ZMod 2 );
  exact ModuleCat.of ( ZMod 2 ) ( ZMod 2 );
  exact ModuleCat.of ( ZMod 2 ) ( ZMod 2 );
  exact ModuleCat.ofHom ( LinearMap.id );
  exact ModuleCat.ofHom ( LinearMap.id );
  exact 1;
  constructor <;> intro h <;> simp_all +decide [ cochainEval ];
  convert congr_arg ( fun x => b.hom x ) ( projTransferChainDegree_ι_canLift n k σ |> congr_arg ( fun f => f 1 ) ) using 1;
  simp +decide [ transferCoeff ];
  convert rfl

/-- **Evaluation of the pullback** `f = proj*` on a basis simplex. -/
theorem pullbackCochain_eval (n k : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (ρ : singularSimplices (TopCat.of (Sphere n)) k) :
    cochainEval k (((transferSEScoch n).f.f k).hom ψ) ρ
      = cochainEval k ψ (sProj n k ρ) := by
  unfold cochainEval
  have h1 : (((transferSEScoch n).f.f k).hom ψ).hom
        ((Limits.Sigma.ι (fun _ => ModuleCat.of (ZMod 2) (ZMod 2)) ρ).hom (1:ZMod 2))
      = ψ.hom (((chainFunctorZMod2.map (TopCat.ofHom (proj n))).f k).hom
          ((Limits.Sigma.ι (fun _ => ModuleCat.of (ZMod 2) (ZMod 2)) ρ).hom (1:ZMod 2))) := by
    convert ModuleCat.comp_apply _ _ _ using 1
  refine h1.trans ?_
  congr 1
  have h3 := congrArg (fun m => (ModuleCat.Hom.hom m) (1:ZMod 2)) (projChainMap_ι n k ρ)
  simpa using h3

/-! ## 5. The two cochain-level identities -/

/-- **The lift lifts the cocycle:** `tr*(gysinLift c) = c`. -/
theorem transfer_gysinLift (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k) :
    ((transferSEScoch n).g.f k).hom (gysinLift n k c) = c := by
  apply cochain_ext
  intro σ
  rw [transferCochain_eval, gysinLift_eval, gysinLift_eval,
    sProj_canLift, sProj_sAnti, sProj_canLift, gLastSheet_sAnti]
  generalize cochainEval k c σ = cval
  generalize gLastSheet n k (canLift n k σ) = s
  revert cval s
  decide

/-
**The coboundary descends to the cochain cup with `w₁`:**
`proj*(c ⌣ w₁) = δ(gysinLift c)` provided `c` is a cocycle.
-/
theorem f_cup_eq_coboundary (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (hc : cochainCoboundary (ZMod 2) (TopCat.of (RP n)) k c = 0) :
    ((transferSEScoch n).f.f (k + 1)).hom (cochainCup k 1 c (w1Cochain n))
      = ((transferSEScoch n).X₂.d k (k + 1)).hom (gysinLift n k c) := by
  refine' cochain_ext ( fun ρ => _ );
  convert congr_arg ( fun x : ZMod 2 => x ) ( show cochainEval k c ( faceSimplex ( TopCat.of ( RP n ) ) k ( Fin.last ( k + 1 ) ) ( sProj n ( k + 1 ) ρ ) ) * ( sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( Fin.castSucc ( Fin.last k ) ) ) ) + sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( Fin.last ( k + 1 ) ) ) ) ) = ∑ i : Fin ( k + 2 ), cochainEval k c ( faceSimplex ( TopCat.of ( RP n ) ) k i ( sProj n ( k + 1 ) ρ ) ) * sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( i.succAbove ( Fin.last k ) ) ) ) from ?_ ) using 1;
  · rw [ pullbackCochain_eval, cochainCup_eval ];
    rw [ frontSimplex_eq_lastFace, w1Cochain_backSimplex ];
  · convert cochainCoboundary_eval ( ZMod 2 ) ( TopCat.of ( Sphere n ) ) k ( gysinLift n k c ) ρ using 1;
    rw [ Finset.sum_congr rfl ] ; intros ; rw [ gysinLift_eval ] ;
    rw [ sProj_faceSimplex, gLastSheet_faceSimplex ];
    rw [ neg_one_pow_zmod2 ] ; ring;
  · have h_sum : ∑ i : Fin (k + 2), cochainEval k c (faceSimplex (TopCat.of (RP n)) k i (sProj n (k + 1) ρ)) = 0 := by
      convert congr_arg ( fun x : singularCochainGroup ( ZMod 2 ) ( TopCat.of ( RP n ) ) ( k + 1 ) => cochainEval ( k + 1 ) x ( sProj n ( k + 1 ) ρ ) ) hc using 1;
      rw [ cochainCoboundary_eval ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ neg_one_pow_zmod2 ] ; norm_num;
    rw [ Fin.sum_univ_castSucc ] at * ; simp_all +decide [ Fin.sum_univ_succ ];
    rw [ ← Finset.sum_mul _ _ _ ] at *;
    grind

/-! ## 6. The connecting-map identity -/

/-- Wiring lemma: given a cocycle `c` and the two cochain identities, the
connecting map sends `[c]` to the class of `cochainCup k 1 c (w1Cochain n)`. -/
theorem rpGysinConnecting_cocycleClass (n k : ℕ)
    (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (hc : cochainCoboundary (ZMod 2) (TopCat.of (RP n)) k c = 0) :
    (rpGysinConnecting n k).hom (cocycleClass (TopCat.of (RP n)) k c hc)
      = cocycleClass (TopCat.of (RP n)) (k + 1) (cochainCup k 1 c (w1Cochain n))
          (cochainCupZMod2_respects_cocycles k 1 c (w1Cochain n) hc (w1Cochain_cocycle n)) := by
  have hSE := transferSEScoch_shortExact n
  have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
  have hx₃ : ((forget₂ (ModuleCat (ZMod 2)) Ab).map ((transferSEScoch n).X₃.d k (k + 1))) c = 0 := hc
  have hg' : ((forget₂ (ModuleCat (ZMod 2)) Ab).map ((transferSEScoch n).g.f k)) (gysinLift n k c)
      = c := transfer_gysinLift n k c
  have hf' : ((forget₂ (ModuleCat (ZMod 2)) Ab).map ((transferSEScoch n).f.f (k + 1)))
        (cochainCup k 1 c (w1Cochain n))
      = ((forget₂ (ModuleCat (ZMod 2)) Ab).map ((transferSEScoch n).X₂.d k (k + 1)))
          (gysinLift n k c) := f_cup_eq_coboundary n k c hc
  have key := hSE.δ_apply k (k + 1) hrel c hx₃ (gysinLift n k c) hg'
    (cochainCup k 1 c (w1Cochain n)) hf' (k + 2) (by simp [ComplexShape.next])
  rw [rpGysinConnecting_eq_δ]
  exact key

/-- **The Smith/Gysin connecting map is cup product with the canonical class**
`α = actualRPAlpha n`, evaluated pointwise. -/
theorem rpGysinConnecting_eq_cup_actualRPAlpha (n k : ℕ) (x : rpCohomology n k) :
    (rpGysinConnecting n k).hom x = cupZMod2 x (actualRPAlpha n) := by
  obtain ⟨c, hc, rfl⟩ := cocycleClass_surjective (TopCat.of (RP n)) k x
  rw [rpGysinConnecting_cocycleClass n k c hc]
  rw [← rpW1Class_eq_actualRPAlpha]
  rw [show rpW1Class n = cocycleClass (TopCat.of (RP n)) 1 (w1Cochain n) (w1Cochain_cocycle n) from rfl]
  rw [cupZMod2_mk]

/-- **`simp` form of the connecting-map identity.** -/
@[simp] theorem rpGysinConnecting_apply (n k : ℕ) (x : rpCohomology n k) :
    (rpGysinConnecting n k).hom x = cupZMod2 x (actualRPAlpha n) :=
  rpGysinConnecting_eq_cup_actualRPAlpha n k x

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
