import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoordinateProjection
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SmallChainsQuasiIso
import Mathlib

/-!
# The singular Mayer–Vietoris short exact sequence for a two-set open cover

For a topological space `X` and open sets `U V : Opens X` with `U ⊔ V = ⊤`, this
file constructs the **short exact sequence of singular chain complexes**

```text
0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C_*^{U,V}(X) → 0
```

where `C_*(S)` denotes the singular chains of `X` supported in `S`
(`subChainComplex`), the middle term is the categorical biproduct, and
`C_*^{U,V}(X)` is the small-chain complex for the cover `{U, V}`
(`twoOpenCoverSmallChains`).  The first map is `c ↦ (c, -c)` and the second is
`(a, b) ↦ a + b`.

The sequence is **degreewise split**: a small simplex lies in `U` or in `V`, so
a small chain can be split coordinate-wise (`keepHom`).  Degreewise splitting
gives short exactness of the chain complexes
(`mvShortComplex_shortExact`), which feeds the homology long exact sequence in
`MayerVietoris.lean`.
-/

open CategoryTheory AlgebraicTopology Limits TopologicalSpace
open AffineBarycentricSubdivision

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


open Classical

variable (R : Type) [CommRing R] {X : TopCat.{0}}

/-! ## 1. The two-set open cover -/

/-- The open cover `{U, V}` of `X` associated to two opens with `U ⊔ V = ⊤`. -/
def twoSetCover (U V : Opens X) (hUV : U ⊔ V = ⊤) : OpenCoverData X where
  sets := {(U : Set X), (V : Set X)}
  isOpen_mem := by
    rintro S (rfl | rfl)
    · exact U.isOpen
    · exact V.isOpen
  covers := by
    intro x
    have hx : x ∈ ((U ⊔ V : Opens X) : Set X) := by rw [hUV]; trivial
    rw [Opens.coe_sup] at hx
    rcases hx with hxU | hxV
    · exact ⟨(U : Set X), Set.mem_insert _ _, hxU⟩
    · exact ⟨(V : Set X), Set.mem_insert_of_mem _ rfl, hxV⟩

theorem twoSetCover_memU (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (U : Set X) ∈ (twoSetCover U V hUV).sets :=
  Set.mem_insert _ _

theorem twoSetCover_memV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (V : Set X) ∈ (twoSetCover U V hUV).sets :=
  Set.mem_insert_of_mem _ rfl

/-- **The two-set small-chain complex** `C_*^{U,V}(X)`: the small-chain complex
for the cover `{U, V}`. -/
noncomputable def twoOpenCoverSmallChains (R : Type) [CommRing R]
    {X : TopCat.{0}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  smallChainComplex R X (twoSetCover U V hUV)

/-! ## 2. The chain maps of the short exact sequence -/

/-- The inclusion chain map `C_*(U ∩ V) ⟶ C_*(U)`. -/
noncomputable def mvInclUV_U (U V : Opens X) :
    subChainComplex R X ((U : Set X) ∩ (V : Set X)) ⟶ subChainComplex R X (U : Set X) :=
  subChainInclusion _ _ Set.inter_subset_left

/-- The inclusion chain map `C_*(U ∩ V) ⟶ C_*(V)`. -/
noncomputable def mvInclUV_V (U V : Opens X) :
    subChainComplex R X ((U : Set X) ∩ (V : Set X)) ⟶ subChainComplex R X (V : Set X) :=
  subChainInclusion _ _ Set.inter_subset_right

/-- The inclusion chain map `C_*(U) ⟶ C_*^{U,V}(X)`. -/
noncomputable def mvInclU_small (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainComplex R X (U : Set X) ⟶ twoOpenCoverSmallChains R U V hUV :=
  subChainToSmall (twoSetCover U V hUV) _ (twoSetCover_memU U V hUV)

/-- The inclusion chain map `C_*(V) ⟶ C_*^{U,V}(X)`. -/
noncomputable def mvInclV_small (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainComplex R X (V : Set X) ⟶ twoOpenCoverSmallChains R U V hUV :=
  subChainToSmall (twoSetCover U V hUV) _ (twoSetCover_memV U V hUV)

/-- The two inclusions of `C_*(U ∩ V)` into the small chains agree. -/
theorem mvIncl_comp_eq (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvInclUV_U R U V ≫ mvInclU_small R U V hUV
      = mvInclUV_V R U V ≫ mvInclV_small R U V hUV := by
  apply HomologicalComplex.hom_ext
  intro k
  ext c
  apply Subtype.ext
  rfl

/-- **The left map** `C_*(U ∩ V) ⟶ C_*(U) ⊕ C_*(V)`, `c ↦ (c, -c)`. -/
noncomputable def mvLeftChainMap (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainComplex R X ((U : Set X) ∩ (V : Set X)) ⟶
      subChainComplex R X (U : Set X) ⊞ subChainComplex R X (V : Set X) :=
  biprod.lift (mvInclUV_U R U V) (-(mvInclUV_V R U V))

/-- **The right map** `C_*(U) ⊕ C_*(V) ⟶ C_*^{U,V}(X)`, `(a, b) ↦ a + b`. -/
noncomputable def mvRightChainMap (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainComplex R X (U : Set X) ⊞ subChainComplex R X (V : Set X) ⟶
      twoOpenCoverSmallChains R U V hUV :=
  biprod.desc (mvInclU_small R U V hUV) (mvInclV_small R U V hUV)

/-- The composition `left ≫ right` is zero. -/
theorem mvLeft_comp_mvRight (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvLeftChainMap R U V hUV ≫ mvRightChainMap R U V hUV = 0 := by
  rw [mvLeftChainMap, mvRightChainMap, biprod.lift_desc, mvIncl_comp_eq R U V hUV]
  simp [Preadditive.neg_comp]

/-- **The Mayer–Vietoris short complex** of chain complexes. -/
noncomputable def mvShortComplex (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) where
  X₁ := subChainComplex R X ((U : Set X) ∩ (V : Set X))
  X₂ := subChainComplex R X (U : Set X) ⊞ subChainComplex R X (V : Set X)
  X₃ := twoOpenCoverSmallChains R U V hUV
  f := mvLeftChainMap R U V hUV
  g := mvRightChainMap R U V hUV
  zero := mvLeft_comp_mvRight R U V hUV

/-! ## 3. The coordinate routing maps in a fixed degree -/

/-- Build a degreewise map between subordinate-chain objects by keeping the
simplices satisfying `P`. -/
noncomputable def restrictKeep {n : ℕ} (P : singularSimplices X n → Prop) [DecidablePred P]
    (p q : Submodule R (singularChainGroup R X n))
    (hmaps : ∀ c ∈ p, (keepHom R X P).hom c ∈ q) :
    ModuleCat.of R p ⟶ ModuleCat.of R q :=
  ModuleCat.ofHom (LinearMap.codRestrict q ((keepHom R X P).hom.comp p.subtype)
    (fun c => hmaps c.1 c.2))

@[simp] theorem restrictKeep_val {n : ℕ} (P : singularSimplices X n → Prop) [DecidablePred P]
    (p q : Submodule R (singularChainGroup R X n))
    (hmaps : ∀ c ∈ p, (keepHom R X P).hom c ∈ q) (c : p) :
    (((restrictKeep R P p q hmaps).hom c) : singularChainGroup R X n)
      = (keepHom R X P).hom (c : singularChainGroup R X n) :=
  rfl

/-- The predicate "subordinate to `V` but not to `U`". -/
def IsSubVnotU (U V : Opens X) {n : ℕ} (σ : singularSimplices X n) : Prop :=
  IsSubordinate (V : Set X) σ ∧ ¬ IsSubordinate (U : Set X) σ

/-
Keeping `U`-subordinate simplices sends small chains into `C_*(U)`.
-/
theorem keepHom_small_mem_U (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ)
    (c : singularChainGroup R X k)
    (hc : c ∈ smallChainSubmodule R X (twoSetCover U V hUV) k) :
    (keepHom R X (IsSubordinate (U : Set X))).hom c ∈ subChainSubmodule R X (U : Set X) k := by
  refine' Submodule.span_induction _ _ _ _ hc;
  · simp +zetaDelta at *;
    intro σ hσ; rw [ keepHom_generator ] ; split_ifs <;> simp_all +decide [ IsSubordinate ] ;
    exact chainGenerator_mem_subChainSubmodule ‹_›;
  · simp +decide [ keepHom ];
  · intro x y hx hy hx' hy'; rw [ map_add ] ; exact Submodule.add_mem _ hx' hy';
  · simp +contextual [ map_smul ];
    exact fun a x hx hx' => Submodule.smul_mem _ _ hx'

/-
Keeping the "in `V` not `U`" simplices sends small chains into `C_*(V)`.
-/
theorem keepHom_small_mem_V (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ)
    (c : singularChainGroup R X k)
    (hc : c ∈ smallChainSubmodule R X (twoSetCover U V hUV) k) :
    (keepHom R X (IsSubVnotU U V)).hom c ∈ subChainSubmodule R X (V : Set X) k := by
  refine' Submodule.span_induction _ _ _ _ hc;
  · simp +zetaDelta at *;
    intro σ hσ; rw [ keepHom_generator ] ; split_ifs <;> simp_all +decide [ IsSubVnotU ] ;
    exact chainGenerator_mem_subChainSubmodule ( by tauto );
  · simp +decide [ keepHom ];
  · aesop;
  · intro a x hx hx'; rw [ map_smul ] ; exact Submodule.smul_mem _ _ hx';

/-
Splitting identity on a small chain: keeping `U` plus keeping "`V` not `U`"
recovers the chain.
-/
theorem keepHom_split_small (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ)
    (c : singularChainGroup R X k)
    (hc : c ∈ smallChainSubmodule R X (twoSetCover U V hUV) k) :
    (keepHom R X (IsSubordinate (U : Set X))).hom c
      + (keepHom R X (IsSubVnotU U V)).hom c = c := by
  refine' Submodule.span_induction _ _ _ _ hc;
  · rintro _ ⟨ σ, hσ, rfl ⟩;
    rw [ keepHom_generator, keepHom_generator ] ; split_ifs <;> simp_all +decide [ IsSubordinate, IsSubVnotU ] ;
    contrapose! hσ; simp_all +decide [ IsSmallSimplex ] ;
    simp_all +decide [ twoSetCover ];
  · aesop;
  · intro x y hx hy hx' hy'; rw [ map_add, map_add ] ; rw [ ← add_add_add_comm ] ; rw [ hx', hy' ] ;
  · intro a x hx hx'; rw [ map_smul, map_smul ] ; rw [ ← smul_add ] ; aesop;

/-- Keeping `U`-subordinate simplices sends `V`-chains into `C_*(U ∩ V)`. -/
theorem keepHom_V_mem_UV (U V : Opens X) (k : ℕ)
    (c : singularChainGroup R X k)
    (hc : c ∈ subChainSubmodule R X (V : Set X) k) :
    (keepHom R X (IsSubordinate (U : Set X))).hom c
      ∈ subChainSubmodule R X ((U : Set X) ∩ (V : Set X)) k := by
  have := keepHom_mem_subChainSubmodule (S := (U : Set X)) (T := (V : Set X)) hc
  simpa using this

/-! ## 4. The degreewise splitting -/

/-- Degree-`k` route of a small chain to its `U`-part. -/
noncomputable def routeU (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ModuleCat.of R (smallChainSubmodule R X (twoSetCover U V hUV) k) ⟶
      ModuleCat.of R (subChainSubmodule R X (U : Set X) k) :=
  restrictKeep R (IsSubordinate (U : Set X)) _ _ (keepHom_small_mem_U R U V hUV k)

/-- Degree-`k` route of a small chain to its `V`-only part. -/
noncomputable def routeV (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ModuleCat.of R (smallChainSubmodule R X (twoSetCover U V hUV) k) ⟶
      ModuleCat.of R (subChainSubmodule R X (V : Set X) k) :=
  restrictKeep R (IsSubVnotU U V) _ _ (keepHom_small_mem_V R U V hUV k)

/-- Degree-`k` projection of a `V`-chain to its `U ∩ V`-part. -/
noncomputable def projVtoUV (U V : Opens X) (k : ℕ) :
    ModuleCat.of R (subChainSubmodule R X (V : Set X) k) ⟶
      ModuleCat.of R (subChainSubmodule R X ((U : Set X) ∩ (V : Set X)) k) :=
  restrictKeep R (IsSubordinate (U : Set X)) _ _ (keepHom_V_mem_UV R U V k)

/-
Keeping the "`V` not `U`" simplices kills a chain supported in `U`.
-/
theorem keepHom_PV_eq_zero_of_mem_U (U V : Opens X) (k : ℕ)
    (c : singularChainGroup R X k) (hc : c ∈ subChainSubmodule R X (U : Set X) k) :
    (keepHom R X (IsSubVnotU U V)).hom c = 0 := by
  induction' hc using Submodule.span_induction with c hc;
  · obtain ⟨ σ, hσ, rfl ⟩ := hc; simp +decide [ keepHom_generator, hσ, IsSubVnotU ] ;
  · exact map_zero _;
  · aesop;
  · simp_all +decide [ ModuleCat.Hom.hom ]

/-
Component identity `i_U ≫ routeU = id`.
-/
theorem mvInclU_small_comp_routeU (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvInclU_small R U V hUV).f k ≫ routeU R U V hUV k = 𝟙 _ := by
  ext c;
  convert keepHom_eq_self_of_mem c.2 using 1

/-
Component identity `i_U ≫ routeV = 0`.
-/
theorem mvInclU_small_comp_routeV (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvInclU_small R U V hUV).f k ≫ routeV R U V hUV k = 0 := by
  ext c;
  convert keepHom_PV_eq_zero_of_mem_U R U V k _ c.2 using 1

/-
Component identity `i_V ≫ routeU = projVtoUV ≫ i_{U∩V→U}`.
-/
theorem mvInclV_small_comp_routeU (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvInclV_small R U V hUV).f k ≫ routeU R U V hUV k
      = projVtoUV R U V k ≫ (mvInclUV_U R U V).f k := by
  convert rfl using 1

/-
Element-level splitting on a `V`-chain: keeping `U` plus keeping "`V` not
`U`" recovers the chain (a special case of `keepHom_split_small`).
-/
theorem keepHom_split_subV (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ)
    (c : singularChainGroup R X k) (hc : c ∈ subChainSubmodule R X (V : Set X) k) :
    (keepHom R X (IsSubordinate (U : Set X))).hom c
      + (keepHom R X (IsSubVnotU U V)).hom c = c := by
  have := keepHom_split_small R U V hUV k c ( subChainSubmodule_le_smallChainSubmodule ( twoSetCover_memV U V hUV ) k hc ) ; aesop;

/-
Component identity `i_{U∩V→V} ≫ projVtoUV = id`.
-/
theorem mvInclUV_V_comp_projVtoUV (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvInclUV_V R U V).f k ≫ projVtoUV R U V k = 𝟙 _ := by
  ext c;
  convert keepHom_eq_self_of_mem _;
  convert Submodule.coe_mem ( Submodule.inclusion ( subChainSubmodule_mono Set.inter_subset_left k ) c ) using 1

/-- The degree-`k` "split" short complex with the genuine `ModuleCat` biproduct
in the middle. -/
noncomputable def mvSplitSC (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk
    (biprod.lift ((mvInclUV_U R U V).f k) (-(mvInclUV_V R U V).f k))
    (biprod.desc ((mvInclU_small R U V hUV).f k) ((mvInclV_small R U V hUV).f k))
    (by
      rw [biprod.lift_desc]
      have : (mvInclUV_U R U V).f k ≫ (mvInclU_small R U V hUV).f k
          = (mvInclUV_V R U V).f k ≫ (mvInclV_small R U V hUV).f k := by
        ext c; apply Subtype.ext; rfl
      rw [this]; simp [Preadditive.neg_comp])

/-- The retraction for the degreewise splitting. -/
noncomputable def mvSplit_r (U V : Opens X) (k : ℕ) :
    ModuleCat.of R (subChainSubmodule R X (U : Set X) k)
        ⊞ ModuleCat.of R (subChainSubmodule R X (V : Set X) k) ⟶
      ModuleCat.of R (subChainSubmodule R X ((U : Set X) ∩ (V : Set X)) k) :=
  -(biprod.snd ≫ projVtoUV R U V k)

/-- The section for the degreewise splitting. -/
noncomputable def mvSplit_s (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ModuleCat.of R (smallChainSubmodule R X (twoSetCover U V hUV) k) ⟶
      ModuleCat.of R (subChainSubmodule R X (U : Set X) k)
        ⊞ ModuleCat.of R (subChainSubmodule R X (V : Set X) k) :=
  biprod.lift (routeU R U V hUV k) (routeV R U V hUV k)

/-
`r` is a retraction of `f`.
-/
theorem mvSplit_f_r (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvSplitSC R U V hUV k).f ≫ mvSplit_r R U V k = 𝟙 _ := by
  convert mvInclUV_V_comp_projVtoUV R U V hUV k using 1;
  convert congr_arg ( fun f => f ≫ projVtoUV R U V k ) ( biprod.lift_snd _ _ ) using 1;
  rotate_left;
  exact ModuleCat.of R ( subChainSubmodule R X ( U : Set X ) k );
  exact 0;
  convert congr_arg ( fun f => -f ≫ projVtoUV R U V k ) ( biprod.lift_snd _ _ ) using 1;
  simp +decide [ neg_neg ]

/-
`s` is a section of `g`.
-/
theorem mvSplit_s_g (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    mvSplit_s R U V hUV k ≫ (mvSplitSC R U V hUV k).g = 𝟙 _ := by
  ext x;
  apply Subtype.ext;
  convert keepHom_split_small R U V hUV k x.val x.2 using 1;
  erw [ biprod.lift_desc ] ; aesop;

/-
The element-level splitting identity on `V`-chains: the `U`-part (routed back
through `U ∩ V`) plus the "`V` not `U`"-part recovers the chain.
-/
theorem projVtoUV_inclUV_V_add_inclV_routeV (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((projVtoUV R U V k ≫ (mvInclUV_V R U V).f k :
        ModuleCat.of R (subChainSubmodule R X (V : Set X) k)
          ⟶ ModuleCat.of R (subChainSubmodule R X (V : Set X) k))
      + ((mvInclV_small R U V hUV).f k ≫ routeV R U V hUV k :
        ModuleCat.of R (subChainSubmodule R X (V : Set X) k)
          ⟶ ModuleCat.of R (subChainSubmodule R X (V : Set X) k)))
      = 𝟙 (ModuleCat.of R (subChainSubmodule R X (V : Set X) k)) := by
  ext c
  have h := keepHom_split_subV R U V hUV k c.1 c.2
  convert h using 1

/-- The splitting identity `r ≫ f + g ≫ s = 𝟙`. -/
theorem mvSplit_id (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((mvSplit_r R U V k ≫ (mvSplitSC R U V hUV k).f :
        (mvSplitSC R U V hUV k).X₂ ⟶ (mvSplitSC R U V hUV k).X₂)
      + ((mvSplitSC R U V hUV k).g ≫ mvSplit_s R U V hUV k :
        (mvSplitSC R U V hUV k).X₂ ⟶ (mvSplitSC R U V hUV k).X₂))
      = 𝟙 (mvSplitSC R U V hUV k).X₂ := by
  have hf : (mvSplitSC R U V hUV k).f
      = biprod.lift ((mvInclUV_U R U V).f k) (-(mvInclUV_V R U V).f k) := rfl
  have hg : (mvSplitSC R U V hUV k).g
      = biprod.desc ((mvInclU_small R U V hUV).f k) ((mvInclV_small R U V hUV).f k) := rfl
  rw [hf, hg, mvSplit_r, mvSplit_s]
  rw [show 𝟙 (mvSplitSC R U V hUV k).X₂
      = 𝟙 (ModuleCat.of R (subChainSubmodule R X (U : Set X) k)
          ⊞ ModuleCat.of R (subChainSubmodule R X (V : Set X) k)) from rfl]
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · simp [mvInclU_small_comp_routeU]
  · simp [mvInclU_small_comp_routeV]
  · simp [mvInclV_small_comp_routeU]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_neg,
      Preadditive.neg_comp]
    simpa using projVtoUV_inclUV_V_add_inclV_routeV R U V hUV k

/-- The splitting of the degree-`k` split short complex. -/
noncomputable def mvSplitting (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvSplitSC R U V hUV k).Splitting where
  r := mvSplit_r R U V k
  s := mvSplit_s R U V hUV k
  f_r := mvSplit_f_r R U V hUV k
  s_g := mvSplit_s_g R U V hUV k
  id := mvSplit_id R U V hUV k

theorem mvSplitSC_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (mvSplitSC R U V hUV k).ShortExact :=
  (mvSplitting R U V hUV k).shortExact

/-! ## 5. Degreewise short exactness and the chain-level short exact sequence -/

/-
`(biprod.lift a b).f k ≫ biprodXIso = biprod.lift (a.f k) (b.f k)`.
-/
theorem biprodXIso_lift_f
    {K L M : ChainComplex (ModuleCat.{0} R) ℕ} (a : K ⟶ L) (b : K ⟶ M) (k : ℕ) :
    (biprod.lift a b).f k ≫ (HomologicalComplex.biprodXIso L M k).hom
      = biprod.lift (a.f k) (b.f k) := by
  apply biprod.hom_ext;
  · simp +decide [ Category.assoc, HomologicalComplex.biprodXIso ];
  · simp +decide [ HomologicalComplex.biprodXIso, biprod.lift ]

/-
`biprodXIso.inv ≫ (biprod.desc a b).f k = biprod.desc (a.f k) (b.f k)`.
-/
theorem biprodXIso_desc_f
    {K L M : ChainComplex (ModuleCat.{0} R) ℕ} (a : L ⟶ K) (b : M ⟶ K) (k : ℕ) :
    (HomologicalComplex.biprodXIso L M k).inv ≫ (biprod.desc a b).f k
      = biprod.desc (a.f k) (b.f k) := by
  apply biprod.hom_ext';
  · simp +decide [ HomologicalComplex.biprodXIso, biprod.inl_desc ];
  · simp +decide [ ← Category.assoc, HomologicalComplex.biprodXIso ]

/-
The degree-`k` mapped short complex is isomorphic to the split short complex.
-/
noncomputable def mvEvalIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.down ℕ) k).mapShortComplex.obj
      (mvShortComplex R U V hUV)) ≅ mvSplitSC R U V hUV k :=
  ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso _ _ k) (Iso.refl _)
    (by
    simp +decide [ mvSplitSC, mvShortComplex, mvLeftChainMap ];
    rw [ biprodXIso_lift_f ];
    congr)
    (by
      simp only [Iso.refl_hom, Category.comp_id]
      rw [show ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.down ℕ) k).mapShortComplex.obj
            (mvShortComplex R U V hUV)).g
          = (mvRightChainMap R U V hUV).f k from rfl,
        show (mvSplitSC R U V hUV k).g
          = biprod.desc ((mvInclU_small R U V hUV).f k) ((mvInclV_small R U V hUV).f k) from rfl,
        show (mvRightChainMap R U V hUV)
          = biprod.desc (mvInclU_small R U V hUV) (mvInclV_small R U V hUV) from rfl,
        ← biprodXIso_desc_f, Iso.hom_inv_id_assoc])
        -- placeholder

/-- **Degreewise short exactness** of the Mayer–Vietoris short complex. -/
theorem mvShortComplex_degreewise_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.down ℕ) k).mapShortComplex.obj
      (mvShortComplex R U V hUV)).ShortExact :=
  ShortComplex.shortExact_of_iso (mvEvalIso R U V hUV k).symm (mvSplitSC_shortExact R U V hUV k)

/-- **The Mayer–Vietoris short exact sequence of chain complexes.** -/
theorem mvShortComplex_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvShortComplex R U V hUV).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun k => mvShortComplex_degreewise_shortExact R U V hUV k)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
