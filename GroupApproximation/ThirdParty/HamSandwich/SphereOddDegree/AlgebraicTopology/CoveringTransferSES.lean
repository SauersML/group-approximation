import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNaturality
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

/-!
# The mod-2 Smith short exact sequence of the double cover `Sⁿ → RPⁿ`

This file builds the **degreewise-split short exact sequence of singular mod-2
chain complexes** underlying the transfer of the double cover `proj n : Sⁿ → RPⁿ`:

```text
0 ⟶ C_•(RPⁿ; F₂) ──tr──▶ C_•(Sⁿ; F₂) ──proj_*──▶ C_•(RPⁿ; F₂) ⟶ 0
```

where `tr = projTransferChainMap n` is the transfer (a simplex of `RPⁿ` goes to
the sum of its two lifts) and `proj_* = chainFunctorZMod2.map (proj n)` is the
ordinary pushforward.  Over `F₂` the free `ℤ/2`-action on the lifts makes this
sequence **degreewise split**: in each degree the chain group of `Sⁿ` decomposes
as two copies of the chain group of `RPⁿ` (the "chosen" lift and its antipode),
`tr` is the diagonal and `proj_*` is the fold map.

The whole point is that this is a genuine geometric construction (Route A); it is
*not* the degenerate ordinary pullback `projPullback`.  Dualizing this sequence
and running the cohomology long exact sequence (in a downstream file) shows that
the cohomology transfer is surjective in the top degree, because
`Hⁿ⁺¹(RPⁿ; F₂) = 0`.

## Index-level combinatorics

On singular `k`-simplices we have the two maps
* `sProj n k : (Sⁿ-simplices) → (RPⁿ-simplices)`, post-composition with `proj n`;
* `sAnti n k : (Sⁿ-simplices) → (Sⁿ-simplices)`, post-composition with the
  antipodal map (a fixed-point-free involution with `sProj ∘ sAnti = sProj`).

The fibers of `sProj` are exactly the two-element orbits `{τ, sAnti τ}`
(`sProj_dichotomy`), and `canLift n k σ` is the chosen lift of `σ` used by
`projTransferOnSimplex` (so `tr` sends the basis simplex `σ` to
`ι (canLift σ) + ι (sAnti (canLift σ))`).
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Index-level maps on singular simplices -/

/-- Post-composition with `proj n`, the index map of the pushforward `proj_*` on
the degree-`k` singular chain group. -/
noncomputable def sProj (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    singularSimplices (TopCat.of (RP n)) k :=
  (TopCat.toSSetObjEquiv _ _).symm ((proj n).comp (TopCat.toSSetObjEquiv _ _ τ))

/-- Post-composition with the antipodal map, the deck-transformation involution on
the degree-`k` singular simplices of `Sⁿ`. -/
noncomputable def sAnti (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    singularSimplices (TopCat.of (Sphere n)) k :=
  (TopCat.toSSetObjEquiv _ _).symm ((antipodal n).comp (TopCat.toSSetObjEquiv _ _ τ))

theorem sAnti_sAnti (n k : ℕ) (τ) : sAnti n k (sAnti n k τ) = τ := by
  unfold sAnti
  simp only [Equiv.apply_symm_apply]
  rw [← ContinuousMap.comp_assoc, antipodal_comp_antipodal]
  simp

theorem sProj_sAnti (n k : ℕ) (τ) : sProj n k (sAnti n k τ) = sProj n k τ := by
  unfold sProj sAnti
  simp only [Equiv.apply_symm_apply]
  congr 1
  rw [← ContinuousMap.comp_assoc]
  congr 1
  apply ContinuousMap.ext; intro x; exact proj_antipodal x

/-- The deck involution is fixed-point-free on singular simplices. -/
theorem sAnti_ne {n k : ℕ} (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    sAnti n k τ ≠ τ := by
  unfold sAnti
  intro hc
  apply_fun (TopCat.toSSetObjEquiv _ _) at hc
  rw [Equiv.apply_symm_apply] at hc
  have hpt := congrFun (congrArg (fun (g : C(_,_)) => (g : _ → _)) hc) (Classical.arbitrary _)
  exact ne_neg_self _ (by simpa [antipodal_apply] using hpt.symm)

/-- Two simplices of `Sⁿ` with the same `proj`-image are equal or antipodal:
the fibers of `sProj` are the two-element orbits `{τ₁, sAnti τ₁}`. -/
theorem sProj_dichotomy {n k : ℕ} (τ₁ τ₂ : singularSimplices (TopCat.of (Sphere n)) k)
    (h : sProj n k τ₁ = sProj n k τ₂) : τ₂ = τ₁ ∨ τ₂ = sAnti n k τ₁ := by
  unfold sProj at h
  have h' : (proj n).comp (TopCat.toSSetObjEquiv _ _ τ₁)
      = (proj n).comp (TopCat.toSSetObjEquiv _ _ τ₂) :=
    (TopCat.toSSetObjEquiv _ _).symm.injective h
  -- two-lift dichotomy at the level of continuous maps
  have twoLift : (TopCat.toSSetObjEquiv _ _ τ₂) = (TopCat.toSSetObjEquiv _ _ τ₁)
      ∨ (TopCat.toSSetObjEquiv _ _ τ₂) = (antipodal n).comp (TopCat.toSSetObjEquiv _ _ τ₁) := by
    set σc₁ := TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) τ₁
    set σc₂ := TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) τ₂
    set v₀ : TopologicalSimplex k := Classical.arbitrary _ with hv
    have hpt : ∀ x, proj n (σc₁ x) = proj n (σc₂ x) := fun x =>
      congrFun (congrArg (fun (g : C(_,_)) => (g : _ → _)) h') x
    have hv0 : σc₂ v₀ = σc₁ v₀ ∨ σc₂ v₀ = - σc₁ v₀ := eq_or_eq_neg_of_proj_eq (hpt v₀).symm
    set σ : C(TopologicalSimplex k, RP n) := (proj n).comp σc₁ with hσ
    have hτ2lift : ⇑(proj n) ∘ ⇑σc₂ = σ := by funext x; exact (hpt x).symm
    rcases hv0 with he | he
    · exact Or.inl (projLiftSimplex_unique σ v₀ (σc₁ v₀) rfl hτ2lift rfl he rfl)
    · refine Or.inr (projLiftSimplex_unique σ v₀ (-(σc₁ v₀)) (by rw [proj_neg]; rfl)
        hτ2lift ?_ he (by simp [antipodal_apply]))
      funext x; show proj n (antipodal n (σc₁ x)) = σ x; rw [proj_antipodal]; rfl
  rcases twoLift with h1 | h1
  · left; exact (TopCat.toSSetObjEquiv _ _).injective h1
  · right; unfold sAnti
    apply (TopCat.toSSetObjEquiv _ _).injective
    rw [Equiv.apply_symm_apply, h1]

/-! ## 2. The chosen lift and the characterisation of `tr` on basis simplices -/

/-- For each singular simplex `σ` of `RPⁿ`, the transfer `projTransferOnSimplex`
sends its basis element to `ι τ + ι (sAnti τ)` for some lift `τ` (the "chosen
lift") with `sProj τ = σ`. -/
theorem projTransferOnSimplex_eq_exists (n k : ℕ)
    (σ : singularSimplices (TopCat.of (RP n)) k) :
    ∃ τ : singularSimplices (TopCat.of (Sphere n)) k, sProj n k τ = σ ∧
      projTransferOnSimplex n k σ
        = Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff) τ
          + Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff)
              (sAnti n k τ) := by
  set σc := TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) σ with hσc
  set v₀ : TopologicalSimplex k := Classical.arbitrary _ with hv₀
  set e : Sphere n := (proj_surjective n (σc v₀)).choose with he_def
  have he : proj n e = σc v₀ := (proj_surjective n (σc v₀)).choose_spec
  set τ₁ : C(TopologicalSimplex k, Sphere n) := projLiftSimplex σc v₀ e he with hτ₁
  refine ⟨(TopCat.toSSetObjEquiv _ _).symm τ₁, ?_, ?_⟩
  · unfold sProj
    rw [Equiv.apply_symm_apply]
    have : (proj n).comp τ₁ = σc := by
      apply ContinuousMap.ext; intro x; exact projLiftSimplex_lifts_apply σc v₀ e he x
    rw [this]; rw [hσc]; exact (Equiv.symm_apply_apply _ _)
  · show _ = _
    rw [projTransferOnSimplex]
    simp only []
    congr 2
    unfold sAnti
    rw [Equiv.apply_symm_apply]
    rw [projLiftSimplex_antipodal]

/-- The chosen lift of a singular simplex `σ` of `RPⁿ`: a lift `canLift σ` with
`sProj (canLift σ) = σ` such that the transfer sends `ι σ` to
`ι (canLift σ) + ι (sAnti (canLift σ))`. -/
noncomputable def canLift (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    singularSimplices (TopCat.of (Sphere n)) k :=
  (projTransferOnSimplex_eq_exists n k σ).choose

theorem sProj_canLift (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    sProj n k (canLift n k σ) = σ :=
  (projTransferOnSimplex_eq_exists n k σ).choose_spec.1

/-- Characterisation of the transfer on a basis simplex `σ`:
`tr (ι σ) = ι (canLift σ) + ι (sAnti (canLift σ))`. -/
theorem projTransferChainDegree_ι_canLift (n k : ℕ)
    (σ : singularSimplices (TopCat.of (RP n)) k) :
    Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) σ
        ≫ projTransferChainDegree n k
      = Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff)
          (canLift n k σ)
        + Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff)
            (sAnti n k (canLift n k σ)) := by
  rw [projTransferChainDegree_ι]
  exact (projTransferOnSimplex_eq_exists n k σ).choose_spec.2

set_option maxHeartbeats 1000000 in
/-- The pushforward `proj_*` on a basis simplex `τ`:
`proj_* (ι τ) = ι (sProj τ)`. -/
theorem projChainMap_ι (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff) τ
        ≫ (chainFunctorZMod2.map (TopCat.ofHom (proj n))).f k
      = Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) (sProj n k τ) := by
  rw [sProj]
  exact singularChainFunctor_map_ι (X := TopCat.of (Sphere n)) (Y := TopCat.of (RP n))
    (proj n) k τ

/-! ## 3. The splitting maps in each degree -/

open Classical in
/-- The degree-`k` section `s : C_k(RPⁿ) → C_k(Sⁿ)` of the pushforward `proj_*`:
it sends a basis simplex `σ` to `ι (sAnti (canLift σ))` (the *antipode* of the
chosen lift, i.e. the inclusion into the "second copy"). -/
noncomputable def chainSec (n k : ℕ) :
    singularChainZMod2 (TopCat.of (RP n)) k ⟶ singularChainZMod2 (TopCat.of (Sphere n)) k :=
  Sigma.desc (fun σ =>
    Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff)
      (sAnti n k (canLift n k σ)))

open Classical in
/-- The degree-`k` retraction `r : C_k(Sⁿ) → C_k(RPⁿ)` of the transfer `tr`:
it sends a basis simplex `τ` to `ι (sProj τ)` when `τ` is the chosen lift of its
image (the "first copy"), and to `0` otherwise. -/
noncomputable def chainRetr (n k : ℕ) :
    singularChainZMod2 (TopCat.of (Sphere n)) k ⟶ singularChainZMod2 (TopCat.of (RP n)) k :=
  Sigma.desc (fun τ =>
    if canLift n k (sProj n k τ) = τ then
      Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) (sProj n k τ)
    else 0)

@[simp] theorem chainSec_ι (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) σ ≫ chainSec n k
      = Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff)
          (sAnti n k (canLift n k σ)) :=
  Sigma.ι_desc _ _

open Classical in
@[simp] theorem chainRetr_ι (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k => transferCoeff) τ ≫ chainRetr n k
      = if canLift n k (sProj n k τ) = τ then
          Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) (sProj n k τ)
        else 0 :=
  Sigma.ι_desc _ _

/-! ## 4. The degreewise splitting relations -/

/-- `tr ≫ r = 𝟙` in each degree (`r` is a retraction of `tr`). -/
theorem chainRetr_f_r (n k : ℕ) :
    projTransferChainDegree n k ≫ chainRetr n k = 𝟙 _ := by
  apply Sigma.hom_ext
  intro σ
  rw [← Category.assoc, projTransferChainDegree_ι_canLift, Preadditive.add_comp,
    chainRetr_ι, chainRetr_ι, sProj_canLift, sProj_sAnti, sProj_canLift,
    if_pos rfl, if_neg (sAnti_ne _).symm, add_zero]
  exact (Category.comp_id _).symm

/-- `s ≫ proj_* = 𝟙` in each degree (`s` is a section of `proj_*`). -/
theorem chainSec_s_g (n k : ℕ) :
    chainSec n k ≫ (chainFunctorZMod2.map (TopCat.ofHom (proj n))).f k = 𝟙 _ := by
  apply Sigma.hom_ext
  intro σ
  rw [← Category.assoc, chainSec_ι, projChainMap_ι, sProj_sAnti, sProj_canLift]
  exact (Category.comp_id _).symm

/-- The completeness relation `r ≫ tr + proj_* ≫ s = 𝟙` in each degree. -/
theorem chain_splitting_id (n k : ℕ) :
    chainRetr n k ≫ projTransferChainDegree n k
        + (chainFunctorZMod2.map (TopCat.ofHom (proj n))).f k ≫ chainSec n k = 𝟙 _ := by
  apply Sigma.hom_ext
  intro τ
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, chainRetr_ι, projChainMap_ι,
    chainSec_ι]
  by_cases h : canLift n k (sProj n k τ) = τ
  · rw [if_pos h, projTransferChainDegree_ι_canLift, h]
    rw [add_assoc, singularChain_add_self, add_zero]
    exact (Category.comp_id _).symm
  · rw [if_neg h, zero_comp, zero_add]
    have hd := sProj_dichotomy (canLift n k (sProj n k τ)) τ (sProj_canLift n k (sProj n k τ))
    rcases hd with h1 | h1
    · exact absurd h1.symm h
    · rw [← h1]; exact (Category.comp_id _).symm

/-- The transfer composed with the pushforward is zero in each degree
(`proj_* ∘ tr = 0`). -/
theorem projTransfer_comp_projChainMap_degree (n k : ℕ) :
    projTransferChainDegree n k ≫ (chainFunctorZMod2.map (TopCat.ofHom (proj n))).f k = 0 := by
  apply Sigma.hom_ext
  intro σ
  rw [comp_zero, ← Category.assoc, projTransferChainDegree_ι_canLift,
    Preadditive.add_comp, projChainMap_ι, projChainMap_ι,
    sProj_canLift, sProj_sAnti, sProj_canLift]
  exact singularChain_add_self _ _ _

/-! ## 5. The chain-level short exact sequence -/

/-- The transfer composed with the pushforward is zero as a chain map. -/
theorem projTransfer_comp_projChainMap (n : ℕ) :
    projTransferChainMap n ≫ chainFunctorZMod2.map (TopCat.ofHom (proj n)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro k
  simpa using projTransfer_comp_projChainMap_degree n k

/-- **The mod-2 Smith short exact sequence of the double cover, as a short
complex of chain complexes.** -/
noncomputable def transferSESChain (n : ℕ) :
    ShortComplex (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) where
  X₁ := singularChainCx (TopCat.of (RP n))
  X₂ := singularChainCx (TopCat.of (Sphere n))
  X₃ := singularChainCx (TopCat.of (RP n))
  f := projTransferChainMap n
  g := chainFunctorZMod2.map (TopCat.ofHom (proj n))
  zero := projTransfer_comp_projChainMap n

/-- The degree-`k` short complex of `transferSESChain n` is split. -/
noncomputable def transferSESChain_degreewiseSplitting (n k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) k).mapShortComplex.obj
      (transferSESChain n)).Splitting where
  r := chainRetr n k
  s := chainSec n k
  f_r := chainRetr_f_r n k
  s_g := chainSec_s_g n k
  id := chain_splitting_id n k

/-- **The mod-2 Smith short exact sequence of the double cover is short exact.** -/
theorem transferSESChain_shortExact (n : ℕ) : (transferSESChain n).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun k => (transferSESChain_degreewiseSplitting n k).shortExact)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

