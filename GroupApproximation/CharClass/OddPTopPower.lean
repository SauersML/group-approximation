import GroupApproximation.CharClass.OddPTopPowerHomotopy
import GroupApproximation.CharClass.OddPRedPow
import GroupApproximation.CharClass.CupOneComm

/-!
# The top power at an odd prime: `[D₀ u] = [u ⌣ ⋯ ⌣ u]`

`OddPCochain.lean` defines `D_j(u)(σ) = ⟨u^{⊗p}, Δ(e_j ⊗ σ)⟩` from the equivariant diagonal `Δ`.  At
`W`-index `0` the generator `e₀ ⊗ σ` has no resolution boundary, so `σ ↦ Δ(e₀ ⊗ σ)` is a natural
chain map `singFreeR (ZMod p) ⟶ tupFunK (ZMod p) p` (`diagE0Nat`), and in degree `0` it is the
constant tuple, exactly as the iterated Alexander–Whitney diagonal.  The comparison of
`OddPTopPowerHomotopy.lean` then gives

* `oddD_zero_class` — **the class of `D₀(u)` is the class of the cup power** `u^{⌣p}`, in every degree
  `q` and on every space; no constant appears;
* `oddDClass_zero` — the same statement for `oddDClass` on the class of `u`.

The degree `p q − 0` of `D₀(u)` and the degree `q p` of the left-nested cup power are identified by
`cochainCast`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace TopPow

/-! ## 1. From evaluations to classes -/

/-- **Classes from evaluations.**  Two cocycles whose values are the evaluations of `u^{⊗r}` on a
natural diagonal `Φ` (agreeing with `awNat` in degree `0`) and on the Alexander–Whitney diagonal have
the same class. -/
theorem class_eq_of_eval (K : Type) [CommRing K] (r : ℕ)
    (hG : AcyclicOnModels stdSimplexTop K (tupFunK K r)) (Φ : singFreeR K ⟶ tupFunK K r)
    (h0 : ∀ X : TopCat.{0}, (Φ.app X).f 0 = ((awNat K r).app X).f 0)
    {X : TopCat.{0}} {q : ℕ} (u : singularCochainGroup K X q)
    (hu : cochainCoboundary K X q u = 0) (m : ℕ) (A B : singularCochainGroup K X m)
    (hA : ∀ σ : singularSimplices X m, cochainEval m A σ
      = tupEval K X r m (fun _ => Pi.single q u) (((Φ.app X).f m).hom (Finsupp.single σ 1)))
    (hB : ∀ σ : singularSimplices X m, cochainEval m B σ
      = tupEval K X r m (fun _ => Pi.single q u) (awTup K X r m σ))
    (hAc : cochainCoboundary K X m A = 0) (hBc : cochainCoboundary K X m B = 0) :
    cocycleClassK K X m A hAc = cocycleClassK K X m B hBc := by
  cases m with
  | zero =>
    refine cocycleClassK_congr K X 0 (cochain_ext fun σ => ?_) hAc hBc
    rw [hA, hB, h0 X, awNat_app_f_single]
  | succ k =>
    obtain ⟨w, hw⟩ := eval_eq_awTup_add_coboundary K r hG Φ h0 u hu k
    have hAB : A = B + cochainCoboundary K X k w := cochain_ext fun σ => by
      rw [cochainEval_add, hA, hB, hw]
    have hδδ := cochainCoboundary_cochainCoboundaryK K X k w
    have hsum : cochainCoboundary K X (k + 1) (B + cochainCoboundary K X k w) = 0 := by
      rw [← hAB]
      exact hAc
    rw [cocycleClassK_congr K X (k + 1) hAB hAc hsum,
      cocycleClassK_add K X (k + 1) B (cochainCoboundary K X k w) hBc hδδ hsum,
      cocycleClassK_coboundary_zero, add_zero]

/-! ## 2. The diagonal at `W`-index `0` -/

section Diag

variable (p : ℕ) [Fact p.Prime]

/-- The generator `e₀ ⊗ σ` of `W ⊗ C(X)`: `W`-index `0`, simplex degree `k`. -/
def e0Gen (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X k) : OddWTensor p k X :=
  Finsupp.single (⟨Fin.last k, simplexEquiv X k σ⟩ : WSIndex k X) (1 : GroupRingZMod p)

/-- **The non-equivariant part `Δ(e₀ ⊗ −)` of the diagonal**, `F_p`-linear. -/
def diagE0Lin (X : TopCat.{0}) (k : ℕ) :
    (singularSimplices X k →₀ ZMod p) →ₗ[ZMod p] tupMod (ZMod p) X p k :=
  Finsupp.linearCombination (ZMod p) fun σ => oddDiagApp p X k (e0Gen p X k σ)

theorem diagE0Lin_single (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X k) :
    diagE0Lin p X k (Finsupp.single σ 1) = oddDiagApp p X k (e0Gen p X k σ) := by
  unfold diagE0Lin
  rw [Finsupp.linearCombination_single, one_smul]

/-- The diagonal as an additive map. -/
def oddDiagHom (X : TopCat.{0}) (k : ℕ) : OddWTensor p k X →+ tupMod (ZMod p) X p k :=
  AddMonoidHom.mk' (oddDiagApp p X k) (oddDiagApp_add p X k)

/-- The boundary of `e₀ ⊗ σ` is `e₀ ⊗ ∂σ`. -/
theorem oddDiff_e0Gen (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X (k + 1)) :
    oddDiff p (oddSingularBoundary p) X k (e0Gen p X (k + 1) σ)
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • e0Gen p X k (faceSimplex X k i σ) := by
  have hS : oddDiffS p (oddSingularBoundary p) X k (Fin.last (k + 1)) (simplexEquiv X (k + 1) σ)
      = ((-1 : GroupRingZMod p) ^ (k - k)) •
          Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
            (fun τ : stdSimplexTop k ⟶ X => (⟨Fin.last k, τ⟩ : WSIndex k X))
            ((oddSingularBoundary p).bd X k (Finsupp.single (simplexEquiv X (k + 1) σ) 1)) :=
    oddDiffS_succ p (oddSingularBoundary p) X k (Fin.last k) (simplexEquiv X (k + 1) σ)
  have hsingle : Finsupp.mapDomain (simplexEquiv X (k + 1)).symm
      (Finsupp.single (simplexEquiv X (k + 1) σ) (1 : GroupRingZMod p)) = Finsupp.single σ 1 := by
    rw [Finsupp.mapDomain_single, Equiv.symm_apply_apply]
  let Ψ : ((singFreeR (GroupRingZMod p)).obj X).X k →+ OddWTensor p k X :=
    ((Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ : stdSimplexTop k ⟶ X => (⟨Fin.last k, τ⟩ : WSIndex k X))).comp
      (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X k))).toAddMonoidHom
  have hd := congrArg Ψ (singFreeR_d_single (GroupRingZMod p) X k σ)
  rw [map_sum] at hd
  rw [e0Gen, oddDiff_single]
  show oddDiffW p X k (Fin.last (k + 1)) (simplexEquiv X (k + 1) σ)
      + oddDiffS p (oddSingularBoundary p) X k (Fin.last (k + 1)) (simplexEquiv X (k + 1) σ) = _
  rw [oddDiffW_last, zero_add, hS, Nat.sub_self, pow_zero, one_smul]
  refine Eq.trans ?_ (hd.trans (Finset.sum_congr rfl fun i _ => ?_))
  · exact congrArg (fun c => Ψ ((((singFreeR (GroupRingZMod p)).obj X).d (k + 1) k).hom c)) hsingle
  · rw [map_zsmul]
    show ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ : stdSimplexTop k ⟶ X => (⟨Fin.last k, τ⟩ : WSIndex k X))
        (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X k)
          (Finsupp.single (faceSimplex X k i σ) 1)) = _
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    rfl

/-- **`Δ(e₀ ⊗ −)` is a chain map.** -/
theorem tupD_diagE0 (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X (k + 1)) :
    tupD (ZMod p) X p k (oddDiagApp p X (k + 1) (e0Gen p X (k + 1) σ))
      = diagE0Lin p X k (chainBd (ZMod p) X k (Finsupp.single σ 1)) := by
  rw [oddDiagApp_d, oddDiff_e0Gen]
  let Θ : ((singFreeR (ZMod p)).obj X).X k →+ tupMod (ZMod p) X p k :=
    (diagE0Lin p X k).toAddMonoidHom
  have hd := congrArg Θ (singFreeR_d_single (ZMod p) X k σ)
  rw [map_sum] at hd
  refine Eq.trans ?_ hd.symm
  show oddDiagHom p X k
      (∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • e0Gen p X k (faceSimplex X k i σ)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  show _ = ((-1 : ℤ) ^ (i : ℕ)) • diagE0Lin p X k (Finsupp.single (faceSimplex X k i σ) 1)
  rw [diagE0Lin_single]
  rfl

theorem tupD_diagE0Lin (X : TopCat.{0}) (k : ℕ) (c : singularSimplices X (k + 1) →₀ ZMod p) :
    tupD (ZMod p) X p k (diagE0Lin p X (k + 1) c) = diagE0Lin p X k (chainBd (ZMod p) X k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod p) by rw [Finsupp.smul_single_one],
      map_smul, map_smul, map_smul, map_smul, diagE0Lin_single, tupD_diagE0]

/-- **`Δ(e₀ ⊗ −)` is natural.** -/
theorem tupMap_diagE0 {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (σ : singularSimplices X k) :
    tupMap (ZMod p) f p k (oddDiagApp p X k (e0Gen p X k σ))
      = oddDiagApp p Y k (e0Gen p Y k (pushSimplex f k σ)) := by
  rw [oddDiagApp_natural, e0Gen, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem tupMap_diagE0Lin {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (c : singularSimplices X k →₀ ZMod p) :
    tupMap (ZMod p) f p k (diagE0Lin p X k c)
      = diagE0Lin p Y k (Finsupp.mapDomain (pushSimplex f k) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Finsupp.mapDomain_add, map_add]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod p) by rw [Finsupp.smul_single_one],
      map_smul, map_smul, Finsupp.mapDomain_smul, map_smul, Finsupp.mapDomain_single,
      diagE0Lin_single, diagE0Lin_single, tupMap_diagE0]

/-- **`Δ(e₀ ⊗ −)` as a natural chain map** `singFreeR (ZMod p) ⟶ tupFunK (ZMod p) p`. -/
def diagE0Nat : singFreeR (ZMod p) ⟶ tupFunK (ZMod p) p where
  app X :=
    { f := fun k => ModuleCat.ofHom (diagE0Lin p X k)
      comm' := by
        rintro i j (rfl : j + 1 = i)
        rw [tupFunK_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
        exact tupD_diagE0Lin p X j c }
  naturality X Y f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    show diagE0Lin p Y k ((((singFreeR (ZMod p)).map f).f k).hom c)
      = tupMap (ZMod p) f p k (diagE0Lin p X k c)
    rw [singFreeR_map_apply, tupMap_diagE0Lin]

end Diag

/-! ## 3. Degree `0` -/

theorem vtx_self {X : TopCat.{0}} {k : ℕ} (σ : singularSimplices X k) :
    vtx σ k id monotone_id = ⟨k, σ⟩ := by
  have h : clampHom k k id monotone_id = 𝟙 _ := by
    ext j : 3
    apply Fin.ext
    show min j.val k = j.val
    have hj : j.val < k + 1 := j.isLt
    rw [min_eq_left (show j.val ≤ k by omega)]
  show (⟨k, (TopCat.toSSet.obj X).map (clampHom k k id monotone_id).op σ⟩ : TagSimp X) = ⟨k, σ⟩
  rw [h]
  simp

/-- **The Alexander–Whitney diagonal of a point is the constant tuple.** -/
theorem awAll_point (K : Type) [CommRing K] {X : TopCat.{0}} (r : ℕ) (x : singularSimplices X 0) :
    awAll K X r ⟨0, x⟩ = Finsupp.single (fun _ => (⟨0, x⟩ : TagSimp X)) 1 := by
  induction r with
  | zero =>
    rw [awAll_zero, if_pos rfl]
    exact congrArg (fun t => Finsupp.single t (1 : K)) (Subsingleton.elim _ _)
  | succ r ih =>
    have hfr : awFront (⟨0, x⟩ : TagSimp X) 0 = ⟨0, x⟩ := vtx_self x
    have hbk : awBack (⟨0, x⟩ : TagSimp X) 0 = ⟨0, x⟩ :=
      (vtx_congr x (addRight_mono 0) monotone_id (show 0 - 0 = 0 from rfl) fun j _ => by
        simp only [id_eq, add_zero]).trans (vtx_self x)
    rw [awAll_succ]
    show (∑ i ∈ Finset.range 1,
        catLin K X r (awAll K X r (awFront (⟨0, x⟩ : TagSimp X) i))
          (Finsupp.single (awBack (⟨0, x⟩ : TagSimp X) i) 1)) = _
    rw [Finset.sum_range_one, hfr, hbk, ih, catLin_single]
    refine congrArg (fun t => Finsupp.single t (1 : K)) (funext fun j => ?_)
    induction j using Fin.lastCases with
    | last => exact Fin.snoc_last (α := fun _ => TagSimp X) _ _
    | cast j => exact Fin.snoc_castSucc (α := fun _ => TagSimp X) _ _ j

theorem diagE0Nat_zero (p : ℕ) [Fact p.Prime] (X : TopCat.{0}) :
    ((diagE0Nat p).app X).f 0 = ((awNat (ZMod p) p).app X).f 0 := by
  apply ModuleCat.hom_ext
  show diagE0Lin p X 0 = awTupLin (ZMod p) X p 0
  refine Finsupp.lhom_ext fun x a => ?_
  rw [← Finsupp.smul_single_one, map_smul, map_smul, diagE0Lin_single, awTupLin_single]
  refine congrArg (a • ·) (tupIncl_injective (ZMod p) X 0 ?_)
  rw [tupIncl_awTup, awAll_point,
    show e0Gen p X 0 x = Finsupp.single (⟨0, simplexEquiv X 0 x⟩ : WSIndex 0 X) 1 from rfl,
    oddDiagApp_zero, tupIncl_single]
  show Finsupp.single (fun _ : Fin p => (⟨0, (simplexEquiv X 0).symm (simplexEquiv X 0 x)⟩ : TagSimp X))
      (1 : ZMod p) = _
  rw [Equiv.symm_apply_apply]

/-! ## 4. The top power -/

theorem topPow_deg (p q : ℕ) : q * p = p * q - 0 := by
  rw [Nat.sub_zero, Nat.mul_comm]

theorem cochainCast_cocycle {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup K X m) (hφ : cochainCoboundary K X m φ = 0) :
    cochainCoboundary K X m' (cochainCast h φ) = 0 := by
  subst h
  have hid : cochainCast (rfl : m = m) φ = φ := by
    unfold cochainCast
    rw [eqToHom_refl, Category.id_comp]
  rw [hid, hφ]

theorem cupPowQ_cocycle (K : Type) [CommRing K] (X : TopCat.{0}) {q : ℕ}
    (u : singularCochainGroup K X q) (hu : cochainCoboundary K X q u = 0) :
    ∀ r : ℕ, cochainCoboundary K X (q * r) (cupPowQ K X u r) = 0
  | 0 => cochainCoboundary_cochainOneK K X
  | r + 1 => cochainCup_respects_cocycles (q * r) q _ u (cupPowQ_cocycle K X u hu r) hu

theorem tupEvalAll_awAll_piSingle_cast (K : Type) [CommRing K] (X : TopCat.{0}) {q r m : ℕ}
    (u : singularCochainGroup K X q) (h : q * r = m) (σ : singularSimplices X m) :
    tupEvalAll K X r (fun _ => Pi.single q u) (awAll K X r ⟨m, σ⟩)
      = cochainEval m (cochainCast h (cupPowQ K X u r)) σ := by
  subst h
  have hid : cochainCast (rfl : q * r = q * r) (cupPowQ K X u r) = cupPowQ K X u r := by
    unfold cochainCast
    rw [eqToHom_refl, Category.id_comp]
  rw [hid, tupEvalAll_awAll_piSingle]

section Top

variable (p : ℕ) [Fact p.Prime]

/-- **The top power at cochain level, as classes**: `[D₀(u)] = [u^{⌣p}]` for every cocycle `u` of every
degree on every space. -/
theorem oddD_zero_class (hp : Odd p) {X : TopCat.{0}} {q : ℕ}
    (u : singularCochainGroup (ZMod p) X q) (hu : cochainCoboundary (ZMod p) X q u = 0) :
    cocycleClassK (ZMod p) X (p * q - 0) (oddD p q 0 u) (oddD_cocycle p hp q 0 (Nat.zero_le _) u hu)
      = cocycleClassK (ZMod p) X (p * q - 0)
          (cochainCast (topPow_deg p q) (cupPowQ (ZMod p) X u p))
          (cochainCast_cocycle (topPow_deg p q) _ (cupPowQ_cocycle (ZMod p) X u hu p)) := by
  have hG : AcyclicOnModels stdSimplexTop (ZMod p) (tupFunK (ZMod p) p) :=
    tupFunK_acyclicOnModels_of (ZMod p) p fun n k y hy =>
      tupD_exists_preimage_stdSimplexTop_zmod p n p k y hy
  refine class_eq_of_eval (ZMod p) p hG (diagE0Nat p) (diagE0Nat_zero p) u hu (p * q - 0) _ _
    (fun σ => ?_) (fun σ => ?_) _ _
  · rw [oddD_eval]
    show _ = tupEval (ZMod p) X p (p * q - 0) (fun _ => Pi.single q u)
      (diagE0Lin p X (p * q - 0) (Finsupp.single σ 1))
    rw [diagE0Lin_single]
    rfl
  · rw [tupEval_eq_tupEvalAll, tupIncl_awTup, tupEvalAll_awAll_piSingle_cast (ZMod p) X u (topPow_deg p q)]

/-- **The top power on classes**: `D₀` of the class of `u` is the class of `u^{⌣p}`. -/
theorem oddDClass_zero (hp : Odd p) {X : TopCat.{0}} {q : ℕ}
    (u : singularCochainGroup (ZMod p) X q) (hu : cochainCoboundary (ZMod p) X q u = 0) :
    oddDClass p hp q 0 (Nat.zero_le _) (cocycleClassK (ZMod p) X q u hu)
      = cocycleClassK (ZMod p) X (p * q - 0)
          (cochainCast (topPow_deg p q) (cupPowQ (ZMod p) X u p))
          (cochainCast_cocycle (topPow_deg p q) _ (cupPowQ_cocycle (ZMod p) X u hu p)) := by
  rw [oddDClass_mk]
  exact oddD_zero_class p hp u hu

#audit_axioms oddD_zero_class
#audit_axioms oddDClass_zero

end Top

end TopPow

end

end GroupApproximation.CharClass
