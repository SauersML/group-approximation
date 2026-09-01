import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupMaps

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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
  change cochainPullback (TopCat.ofHom (proj n)) (k + 1)
      (cochainCup k 1 c (w1Cochain n)) =
    cochainCoboundary (ZMod 2) (TopCat.of (Sphere n)) k (gysinLift n k c)
  refine' cochain_ext ( fun ρ => _ );
  convert congr_arg ( fun x : ZMod 2 => x ) ( show cochainEval k c ( faceSimplex ( TopCat.of ( RP n ) ) k ( Fin.last ( k + 1 ) ) ( sProj n ( k + 1 ) ρ ) ) * ( sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( Fin.castSucc ( Fin.last k ) ) ) ) + sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( Fin.last ( k + 1 ) ) ) ) ) = ∑ i : Fin ( k + 2 ), cochainEval k c ( faceSimplex ( TopCat.of ( RP n ) ) k i ( sProj n ( k + 1 ) ρ ) ) * sheetParity n ( sChart n ( k + 1 ) ρ ( stdSimplex.vertex ( i.succAbove ( Fin.last k ) ) ) ) from ?_ ) using 1;
  · rw [cochainPullback_eval, cochainCup_eval];
    rw [frontSimplex_eq_lastFace]
    change cochainEval k c
        (faceSimplex (TopCat.of (RP n)) k (Fin.last (k + 1)) (sProj n (k + 1) ρ)) *
      cochainEval 1 (w1Cochain n)
        (backSimplex (TopCat.of (RP n)) k 1 (sProj n (k + 1) ρ)) = _
    rw [w1Cochain_backSimplex]
  · convert cochainCoboundary_eval ( ZMod 2 ) ( TopCat.of ( Sphere n ) ) k ( gysinLift n k c ) ρ using 1;
    rw [ Finset.sum_congr rfl ] ; intros ; rw [ gysinLift_eval ] ;
    rw [ sProj_faceSimplex, gLastSheet_faceSimplex ];
    rw [ neg_one_pow_zmod2 ] ; ring;
  · have h_sum : ∑ i : Fin (k + 2), cochainEval k c (faceSimplex (TopCat.of (RP n)) k i (sProj n (k + 1) ρ)) = 0 := by
      have heval := congr_arg
        (fun x : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) (k + 1) =>
          cochainEval (k + 1) x (sProj n (k + 1) ρ)) hc
      rw [cochainCoboundary_eval, cochainEval_zero] at heval
      calc
        _ = ∑ i : Fin (k + 2), (-1 : ZMod 2) ^ (i : ℕ) *
            cochainEval k c
              (faceSimplex (TopCat.of (RP n)) k i (sProj n (k + 1) ρ)) := by
          exact Finset.sum_congr rfl fun _ _ => by rw [neg_one_pow_zmod2]; norm_num
        _ = 0 := heval
    rw [ Fin.sum_univ_castSucc ] at * ; simp_all +decide [ Fin.sum_univ_succ ];
    rw [ ← Finset.sum_mul _ _ _ ] at *;
    let c₀ := cochainEval k c
      (faceSimplex (TopCat.of (RP n)) k 0 (sProj n (k + 1) ρ))
    let cₘ := ∑ i : Fin k, cochainEval k c
      (faceSimplex (TopCat.of (RP n)) k i.castSucc.succ (sProj n (k + 1) ρ))
    let cₗ := cochainEval k c
      (faceSimplex (TopCat.of (RP n)) k (Fin.last (k + 1)) (sProj n (k + 1) ρ))
    let s₀ := sheetParity n (sChart n (k + 1) ρ
      (stdSimplex.vertex (Fin.castSucc (Fin.last k))))
    let s₁ := sheetParity n (sChart n (k + 1) ρ
      (stdSimplex.vertex (Fin.last (k + 1))))
    change c₀ + cₘ + cₗ = 0 at h_sum
    change cₗ * (s₀ + s₁) = c₀ * s₁ + cₘ * s₁ + cₗ * s₀
    have hadd_self (x : ZMod 2) : x + x = 0 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      calc
        x + x = (2 : ZMod 2) * x := by ring
        _ = 0 := by rw [htwo, zero_mul]
    have hrest : c₀ + cₘ = cₗ := by
      have h := congrArg (fun x : ZMod 2 => x + cₗ) h_sum
      simpa only [add_assoc, hadd_self, add_zero, zero_add] using h
    calc
      cₗ * (s₀ + s₁) = cₗ * s₀ + cₗ * s₁ := mul_add _ _ _
      _ = cₗ * s₀ + (c₀ + cₘ) * s₁ := by rw [hrest]
      _ = c₀ * s₁ + cₘ * s₁ + cₗ * s₀ := by ring


end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
