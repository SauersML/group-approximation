import GroupApproximation.CharClass.MayerVietorisBiproduct

/-!
# The Mayer–Vietoris long exact sequence in element form

For two opens `U ⊔ V = ⊤` of `X`, this file produces the four restriction maps and the
three exactness statements of cohomological Mayer–Vietoris **as statements about
elements**, which is the form every consumer wants:

```text
H^n(X) → H^n(U) ⊕ H^n(V) → H^n(U ∩ V) →^δ H^{n+1}(X) → ⋯
```

* `mvResU`, `mvResV` — restriction to the two pieces;
* `mvResWU`, `mvResWV` — restriction of the pieces to the intersection;
* `coDelta` (from `cc-cohom-api`'s `CharClass/CohomologyMayerVietoris.lean`) — the
  connecting map;
* `mvExactX`, `mvExactSum`, `mvExactW` — exactness at the three spots.

The categorical input is `cc-cohom-api`'s dualized short exact sequence `coSC` with
its three `ShortComplex.Exact` statements; the bridge from those to elements is
`ShortComplex.Exact.moduleCat_range_eq_ker`, and the identification of the middle term
with a sum of two pieces is `MayerVietorisBiproduct.mvH_decompose`.

Signs never appear: the chain-level Mayer–Vietoris map is `biprod.lift ι (-ι')`, and
over `F₂` the minus is invisible (`neg_eq_self_two`), so `mvResWV` really is the
restriction and `mvExactSum` really says the two restrictions to `U ∩ V` agree.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.MV

noncomputable section

variable {X : TopCat.{0}}

/-! ## 0. Two small bridges -/

/-- Exactness of a short complex of `F₂`-modules, in element form. -/
theorem mvExists_of_exact {S : ShortComplex (ModuleCat.{0} (ZMod 2))} (hS : S.Exact)
    {m : S.X₂} (hm : S.g.hom m = 0) : ∃ e : S.X₁, S.f.hom e = m := by
  have hmem : m ∈ LinearMap.ker S.g.hom := hm
  rw [← hS.moduleCat_range_eq_ker] at hmem
  exact LinearMap.mem_range.1 hmem

/-- An isomorphism of `F₂`-modules does not kill anything. -/
theorem eq_zero_of_iso_hom_eq_zero {M N : ModuleCat.{0} (ZMod 2)} (e : M ≅ N) {x : M}
    (h : e.hom.hom x = 0) : x = 0 := by
  have h1 : e.inv.hom (e.hom.hom x) = x := hom_apply_of_comp_eq_id e.hom_inv_id x
  rw [h, map_zero] at h1
  exact h1.symm

theorem iso_inv_hom_apply {M N : ModuleCat.{0} (ZMod 2)} (e : M ≅ N) (x : M) :
    e.inv.hom (e.hom.hom x) = x := hom_apply_of_comp_eq_id e.hom_inv_id x

theorem iso_hom_inv_apply {M N : ModuleCat.{0} (ZMod 2)} (e : M ≅ N) (y : N) :
    e.hom.hom (e.inv.hom y) = y := hom_apply_of_comp_eq_id e.inv_hom_id y

/-! ## 1. The spaces and the two structural maps -/

/-- An open of the cover, as a space. -/
abbrev mvU (U : Opens X) : TopCat.{0} := TopCat.of (U : Set X)

/-- The intersection of the cover, as a space. -/
abbrev mvInter (U V : Opens X) : TopCat.{0} :=
  TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))

/-- `H^n(X) → H^n(C^*(U) ⊕ C^*(V))`, the first map of the dual Mayer–Vietoris
sequence with its source identified. -/
def mvPhi (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 X n ⟶ (coCx (mvCx U ⊞ mvCx V)).homology n :=
  (coAmbientIso U V hUV n).inv ≫ HomologicalComplex.homologyMap (coSC U V hUV).f n

/-- `H^n(C^*(U) ⊕ C^*(V)) → H^n(U ∩ V)`, the second map of the dual Mayer–Vietoris
sequence with its target identified. -/
def mvPsi (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (coCx (mvCx U ⊞ mvCx V)).homology n ⟶ Hmod2 (mvInter U V) n :=
  HomologicalComplex.homologyMap (coSC U V hUV).g n ≫ (coInterIso U V hUV n).hom

theorem mvPsi_mvPhi (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (y : Hmod2 X n) :
    (mvPsi U V hUV n).hom ((mvPhi U V hUV n).hom y) = 0 := by
  have hFG : HomologicalComplex.homologyMap (coSC U V hUV).f n
      ≫ HomologicalComplex.homologyMap (coSC U V hUV).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (coSC U V hUV).zero,
      HomologicalComplex.homologyMap_zero]
  have hpt : ∀ e : (coSC U V hUV).X₁.homology n,
      (HomologicalComplex.homologyMap (coSC U V hUV).g n).hom
        ((HomologicalComplex.homologyMap (coSC U V hUV).f n).hom e) = 0 := by
    intro e
    have h := hom_apply_of_comp_eq hFG e
    rw [h]; rfl
  show (coInterIso U V hUV n).hom.hom
    ((HomologicalComplex.homologyMap (coSC U V hUV).g n).hom
      ((HomologicalComplex.homologyMap (coSC U V hUV).f n).hom
        ((coAmbientIso U V hUV n).inv.hom y))) = 0
  rw [hpt, map_zero]

/-- The Mayer–Vietoris connecting map, under the name published in
`notes/lix-lane-reports/cc-thom.md`. -/
abbrev mvDelta (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (mvInter U V) n ⟶ Hmod2 X (n + 1) := MV.coDelta U V hUV n

/-! ## 2. The four restrictions -/

/-- Restriction `H^n(X) → H^n(U)`. -/
def mvResU (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) : Hmod2 X n ⟶ Hmod2 (mvU U) n :=
  mvPhi U V hUV n ≫ mvHProjU U V n ≫ (coSubHomologyIso (U : Set X) n).hom

/-- Restriction `H^n(X) → H^n(V)`. -/
def mvResV (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) : Hmod2 X n ⟶ Hmod2 (mvU V) n :=
  mvPhi U V hUV n ≫ mvHProjV U V n ≫ (coSubHomologyIso (V : Set X) n).hom

/-- Restriction `H^n(U) → H^n(U ∩ V)`. -/
def mvResWU (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (mvU U) n ⟶ Hmod2 (mvInter U V) n :=
  (coSubHomologyIso (U : Set X) n).inv ≫ mvHInclU U V n ≫ mvPsi U V hUV n

/-- Restriction `H^n(V) → H^n(U ∩ V)`. -/
def mvResWV (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (mvU V) n ⟶ Hmod2 (mvInter U V) n :=
  (coSubHomologyIso (V : Set X) n).inv ≫ mvHInclV U V n ≫ mvPsi U V hUV n

theorem mvResU_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod2 X n) :
    (mvResU U V hUV n).hom x
      = (coSubHomologyIso (U : Set X) n).hom.hom
          ((mvHProjU U V n).hom ((mvPhi U V hUV n).hom x)) := rfl

theorem mvResV_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod2 X n) :
    (mvResV U V hUV n).hom x
      = (coSubHomologyIso (V : Set X) n).hom.hom
          ((mvHProjV U V n).hom ((mvPhi U V hUV n).hom x)) := rfl

theorem mvResWU_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (a : Hmod2 (mvU U) n) :
    (mvResWU U V hUV n).hom a
      = (mvPsi U V hUV n).hom
          ((mvHInclU U V n).hom ((coSubHomologyIso (U : Set X) n).inv.hom a)) := rfl

theorem mvResWV_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (b : Hmod2 (mvU V) n) :
    (mvResWV U V hUV n).hom b
      = (mvPsi U V hUV n).hom
          ((mvHInclV U V n).hom ((coSubHomologyIso (V : Set X) n).inv.hom b)) := rfl

/-- The two components of `mvPhi x` are the two restrictions of `x`. -/
theorem mvPhi_eq_zero_iff (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod2 X n) :
    (mvPhi U V hUV n).hom x = 0
      ↔ ((mvResU U V hUV n).hom x = 0 ∧ (mvResV U V hUV n).hom x = 0) := by
  rw [mvH_eq_zero_iff U V n]
  constructor
  · rintro ⟨hU, hV⟩
    refine ⟨?_, ?_⟩
    · rw [mvResU_apply, hU, map_zero]
    · rw [mvResV_apply, hV, map_zero]
  · rintro ⟨hU, hV⟩
    rw [mvResU_apply] at hU
    rw [mvResV_apply] at hV
    exact ⟨eq_zero_of_iso_hom_eq_zero _ hU, eq_zero_of_iso_hom_eq_zero _ hV⟩

/-! ## 3. Exactness at the three spots -/

/-- **Exactness at `H^{n+1}(X)`.**  A class restricting to zero on both pieces is in the
image of the connecting map. -/
theorem mvExactX (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod2 X (n + 1)) :
    ((mvResU U V hUV (n + 1)).hom x = 0 ∧ (mvResV U V hUV (n + 1)).hom x = 0)
      ↔ ∃ w, (coDelta U V hUV n).hom w = x := by
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by simp
  rw [← mvPhi_eq_zero_iff]
  constructor
  · intro hx
    have hker : (HomologicalComplex.homologyMap (coSC U V hUV).f (n + 1)).hom
        ((coAmbientIso U V hUV (n + 1)).inv.hom x) = 0 := hx
    obtain ⟨d, hd⟩ := mvExists_of_exact (coExact_ambient U V hUV n) hker
    refine ⟨(coInterIso U V hUV n).hom.hom d, ?_⟩
    show (coAmbientIso U V hUV (n + 1)).hom.hom
      (((coSC_shortExact U V hUV).δ n (n + 1) hrel).hom
        ((coInterIso U V hUV n).inv.hom ((coInterIso U V hUV n).hom.hom d))) = x
    rw [iso_inv_hom_apply, hd, iso_hom_inv_apply]
  · rintro ⟨w, rfl⟩
    have hzero : ((coSC_shortExact U V hUV).δ n (n + 1) hrel)
        ≫ HomologicalComplex.homologyMap (coSC U V hUV).f (n + 1) = 0 :=
      (coSC_shortExact U V hUV).δ_comp n (n + 1) hrel
    show (HomologicalComplex.homologyMap (coSC U V hUV).f (n + 1)).hom
      ((coAmbientIso U V hUV (n + 1)).inv.hom
        ((coAmbientIso U V hUV (n + 1)).hom.hom
          (((coSC_shortExact U V hUV).δ n (n + 1) hrel).hom
            ((coInterIso U V hUV n).inv.hom w)))) = 0
    rw [iso_inv_hom_apply, hom_apply_of_comp_eq hzero]
    rfl

/-- **Exactness at `H^n(U) ⊕ H^n(V)`.**  Two classes agreeing on the intersection come
from a global class. -/
theorem mvExactSum (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (a : Hmod2 (mvU U) n) (b : Hmod2 (mvU V) n) :
    (mvResWU U V hUV n).hom a = (mvResWV U V hUV n).hom b
      ↔ ∃ x : Hmod2 X n, (mvResU U V hUV n).hom x = a ∧ (mvResV U V hUV n).hom x = b := by
  set m : (coCx (mvCx U ⊞ mvCx V)).homology n :=
    (mvHInclU U V n).hom ((coSubHomologyIso (U : Set X) n).inv.hom a)
      + (mvHInclV U V n).hom ((coSubHomologyIso (V : Set X) n).inv.hom b) with hm
  have hpsi : (mvPsi U V hUV n).hom m
      = (mvResWU U V hUV n).hom a + (mvResWV U V hUV n).hom b := by
    rw [hm, map_add, mvResWU_apply, mvResWV_apply]
  have hprojU : (mvHProjU U V n).hom m = (coSubHomologyIso (U : Set X) n).inv.hom a := by
    rw [hm, map_add, mvH_inclU_projU, mvH_inclV_projU, add_zero]
  have hprojV : (mvHProjV U V n).hom m = (coSubHomologyIso (V : Set X) n).inv.hom b := by
    rw [hm, map_add, mvH_inclU_projV, mvH_inclV_projV, zero_add]
  constructor
  · intro hab
    have hzero : (mvPsi U V hUV n).hom m = 0 := by
      rw [hpsi, hab]; exact add_self_eq_zero_two _
    have hg : (HomologicalComplex.homologyMap (coSC U V hUV).g n).hom m = 0 :=
      eq_zero_of_iso_hom_eq_zero (coInterIso U V hUV n) hzero
    obtain ⟨e, he⟩ := mvExists_of_exact (coExact_sum U V hUV n) hg
    refine ⟨(coAmbientIso U V hUV n).hom.hom e, ?_, ?_⟩
    · rw [mvResU_apply]
      show (coSubHomologyIso (U : Set X) n).hom.hom ((mvHProjU U V n).hom
        ((HomologicalComplex.homologyMap (coSC U V hUV).f n).hom
          ((coAmbientIso U V hUV n).inv.hom ((coAmbientIso U V hUV n).hom.hom e)))) = a
      rw [iso_inv_hom_apply, he, hprojU, iso_hom_inv_apply]
    · rw [mvResV_apply]
      show (coSubHomologyIso (V : Set X) n).hom.hom ((mvHProjV U V n).hom
        ((HomologicalComplex.homologyMap (coSC U V hUV).f n).hom
          ((coAmbientIso U V hUV n).inv.hom ((coAmbientIso U V hUV n).hom.hom e)))) = b
      rw [iso_inv_hom_apply, he, hprojV, iso_hom_inv_apply]
  · rintro ⟨x, hxa, hxb⟩
    have hU : (mvHProjU U V n).hom ((mvPhi U V hUV n).hom x)
        = (coSubHomologyIso (U : Set X) n).inv.hom a := by
      rw [← hxa, mvResU_apply, iso_inv_hom_apply]
    have hV : (mvHProjV U V n).hom ((mvPhi U V hUV n).hom x)
        = (coSubHomologyIso (V : Set X) n).inv.hom b := by
      rw [← hxb, mvResV_apply, iso_inv_hom_apply]
    have hdec : (mvPhi U V hUV n).hom x = m := by
      rw [hm, ← hU, ← hV, mvH_decompose]
    have h0 : (mvResWU U V hUV n).hom a + (mvResWV U V hUV n).hom b = 0 := by
      rw [← hpsi, ← hdec]; exact mvPsi_mvPhi U V hUV n x
    exact eq_of_add_eq_zero_two h0

/-- **Exactness at `H^n(U ∩ V)`.**  A class killed by the connecting map is a sum of
restrictions. -/
theorem mvExactW (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) (w : Hmod2 (mvInter U V) n) :
    (coDelta U V hUV n).hom w = 0
      ↔ ∃ (a : Hmod2 (mvU U) n) (b : Hmod2 (mvU V) n),
          (mvResWU U V hUV n).hom a + (mvResWV U V hUV n).hom b = w := by
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by simp
  constructor
  · intro hw
    have hd : ((coSC_shortExact U V hUV).δ n (n + 1) hrel).hom
        ((coInterIso U V hUV n).inv.hom w) = 0 :=
      eq_zero_of_iso_hom_eq_zero (coAmbientIso U V hUV (n + 1)) hw
    obtain ⟨m, hmm⟩ := mvExists_of_exact (coExact_inter U V hUV n) hd
    refine ⟨(coSubHomologyIso (U : Set X) n).hom.hom ((mvHProjU U V n).hom m),
      (coSubHomologyIso (V : Set X) n).hom.hom ((mvHProjV U V n).hom m), ?_⟩
    rw [mvResWU_apply, mvResWV_apply, iso_inv_hom_apply, iso_inv_hom_apply,
      ← map_add, mvH_decompose]
    show (coInterIso U V hUV n).hom.hom
      ((HomologicalComplex.homologyMap (coSC U V hUV).g n).hom m) = w
    rw [hmm, iso_hom_inv_apply]
  · rintro ⟨a, b, hab⟩
    set m : (coCx (mvCx U ⊞ mvCx V)).homology n :=
      (mvHInclU U V n).hom ((coSubHomologyIso (U : Set X) n).inv.hom a)
        + (mvHInclV U V n).hom ((coSubHomologyIso (V : Set X) n).inv.hom b) with hm
    have hpsi : (mvPsi U V hUV n).hom m = w := by
      rw [hm, map_add, ← mvResWU_apply, ← mvResWV_apply]
      exact hab
    have hg : (HomologicalComplex.homologyMap (coSC U V hUV).g n).hom m
        = (coInterIso U V hUV n).inv.hom w := by
      rw [← hpsi]
      show _ = (coInterIso U V hUV n).inv.hom ((coInterIso U V hUV n).hom.hom
        ((HomologicalComplex.homologyMap (coSC U V hUV).g n).hom m))
      rw [iso_inv_hom_apply]
    have hzero : ((coSC_shortExact U V hUV).δ n (n + 1) hrel).hom
        ((coInterIso U V hUV n).inv.hom w) = 0 := by
      rw [← hg]
      have hcomp : HomologicalComplex.homologyMap (coSC U V hUV).g n
          ≫ ((coSC_shortExact U V hUV).δ n (n + 1) hrel) = 0 :=
        (coSC_shortExact U V hUV).comp_δ n (n + 1) hrel
      rw [hom_apply_of_comp_eq hcomp]; rfl
    show (coAmbientIso U V hUV (n + 1)).hom.hom
      (((coSC_shortExact U V hUV).δ n (n + 1) hrel).hom
        ((coInterIso U V hUV n).inv.hom w)) = 0
    rw [hzero, map_zero]

end

end GroupApproximation.CharClass
