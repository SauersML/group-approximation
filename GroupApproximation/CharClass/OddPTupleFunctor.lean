import GroupApproximation.CharClass.OddPTupleAction
import GroupApproximation.CharClass.OddPModule
import GroupApproximation.CharClass.CartanTargetFunctorial

/-!
# The flat `r`-fold tensor power as a functor into complexes over `F_p[ℤ/p]`

The target of the odd-primary acyclic-models comparison: `X ↦ C(X)^{⊗r}` with the group ring
`Λ = F_p[ℤ/p]` acting through `T ^ s`, where `T` is `OddPTupleAction.lean`'s cyclic operator and
`r ∣ s · p` (at the Steenrod arity `r = p` the generator is `T` itself, `s = 1`; at the Cartan arity
`r = 2p` it is the block shift `T ^ 2`).

## Main results

* `tupMap_tupD`, `tupMap_tupT` — the pushforward along a map of spaces commutes with `d` and `T`.
* `galAlgHomP_comm` — an `F_p`-linear map intertwining two automorphisms of order `p` is linear
  over the group ring for the two induced structures.
* `oddTgt p r s hs` — **the target functor** `TopCat ⥤ ChainComplex (ModuleCat Λ) ℕ`.

The group-ring structure depends on `s`, so it is never a global instance: every object is built as
`@ModuleCat.of Λ _ V _ (tupModule p X r k s hs)`, and the two structures on the source and target of
a map are named explicitly.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Pushing tuples forward -/

section Push

variable {X Y Z : TopCat.{0}} {r : ℕ}

/-- Push a tagged simplex forward; the degree is untouched. -/
def tagPush (f : X ⟶ Y) (τ : TagSimp X) : TagSimp Y := ⟨τ.1, pushSimplex f τ.1 τ.2⟩

/-- Push every slot of a tuple forward. -/
def tupPush (f : X ⟶ Y) (t : TupAll X r) : TupAll Y r := fun j => tagPush f (t j)

theorem tupPush_update (f : X ⟶ Y) (t : TupAll X r) (j : Fin r) (τ : TagSimp X) :
    tupPush f (Function.update t j τ) = Function.update (tupPush f t) j (tagPush f τ) :=
  Function.comp_update (tagPush f) t j τ

theorem tagPush_id (τ : TagSimp X) : tagPush (𝟙 X) τ = τ := by
  obtain ⟨n, σ⟩ := τ
  show (⟨n, pushSimplex (𝟙 X) n σ⟩ : TagSimp X) = ⟨n, σ⟩
  rw [pushSimplex_id]

theorem tagPush_comp (f : X ⟶ Y) (g : Y ⟶ Z) (τ : TagSimp X) :
    tagPush (f ≫ g) τ = tagPush g (tagPush f τ) := by
  obtain ⟨n, σ⟩ := τ
  show (⟨n, pushSimplex (f ≫ g) n σ⟩ : TagSimp Z) = ⟨n, pushSimplex g n (pushSimplex f n σ)⟩
  rw [pushSimplex_comp]

variable (K : Type) [CommRing K]

/-- Naturality of the signed boundary, typed at the bare `Finsupp`s. -/
theorem chainBd_natural (f : X ⟶ Y) (n : ℕ) (c : singularSimplices X (n + 1) →₀ K) :
    chainBd K Y n (Finsupp.mapDomain (pushSimplex f (n + 1)) c)
      = Finsupp.mapDomain (pushSimplex f n) (chainBd K X n c) :=
  singFreeR_d_natural K f n c

/-- **The slot boundary is natural.** -/
theorem tagBd_natural (f : X ⟶ Y) (τ : TagSimp X) :
    Finsupp.mapDomain (tagPush f) (tagBd K X τ) = tagBd K Y (tagPush f τ) := by
  obtain ⟨n, σ⟩ := τ
  cases n with
  | zero =>
    show Finsupp.mapDomain (tagPush f) (tagBd K X ⟨0, σ⟩) = tagBd K Y ⟨0, pushSimplex f 0 σ⟩
    rw [tagBd_zero, tagBd_zero, Finsupp.mapDomain_zero]
  | succ n =>
    show Finsupp.mapDomain (tagPush f) (tagBd K X ⟨n + 1, σ⟩)
      = tagBd K Y ⟨n + 1, pushSimplex f (n + 1) σ⟩
    rw [tagBd_succ_eq, tagBd_succ_eq, ← Finsupp.mapDomain_comp,
      show Finsupp.single (pushSimplex f (n + 1) σ) (1 : K)
        = Finsupp.mapDomain (pushSimplex f (n + 1)) (Finsupp.single σ (1 : K)) from
        Finsupp.mapDomain_single.symm,
      chainBd_natural, ← Finsupp.mapDomain_comp]
    rfl

/-- The pushforward on the full model. -/
def tupAllMap (f : X ⟶ Y) (r : ℕ) : tupAllMod K X r →ₗ[K] tupAllMod K Y r :=
  Finsupp.lmapDomain K K (tupPush f)

theorem tupAllMap_single (f : X ⟶ Y) (t : TupAll X r) :
    tupAllMap K f r (Finsupp.single t (1 : K)) = Finsupp.single (tupPush f t) (1 : K) := by
  rw [tupAllMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tupAllMap_slotBd_single (f : X ⟶ Y) (j : Fin r) (t : TupAll X r) :
    tupAllMap K f r (slotBd K X j (Finsupp.single t (1 : K)))
      = slotBd K Y j (tupAllMap K f r (Finsupp.single t (1 : K))) := by
  rw [tupAllMap_single, slotBd_single, slotBd_single, slotBdGen, slotBdGen, map_smul,
    Finsupp.apply_linearCombination]
  have hpre : tupPre (tupPush f t) j = tupPre t j := rfl
  rw [hpre, show tupPush f t j = tagPush f (t j) from rfl, ← tagBd_natural,
    Finsupp.linearCombination_mapDomain]
  congr 1
  refine tupLC_congr_fun K (fun τ => ?_) _
  show tupAllMap K f r (Finsupp.single (Function.update t j τ) (1 : K))
    = Finsupp.single (Function.update (tupPush f t) j (tagPush f τ)) (1 : K)
  rw [tupAllMap_single, tupPush_update]

theorem tupAllMap_comp_tupDAll (f : X ⟶ Y) :
    (tupAllMap K f r).comp (tupDAll K X r) = (tupDAll K Y r).comp (tupAllMap K f r) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, tupDAll, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => tupAllMap_slotBd_single K f j t

theorem tupAllMap_comp_tupTAll (f : X ⟶ Y) :
    (tupAllMap K f r).comp (tupTAll K X r) = (tupTAll K Y r).comp (tupAllMap K f r) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupTAll_single, map_smul, tupAllMap_single, tupAllMap_single, tupTAll_single]
  rfl

/-- Push a degree-`k` index forward. -/
def tupPushIdx (f : X ⟶ Y) {k : ℕ} (t : TupIdx X r k) : TupIdx Y r k := ⟨tupPush f t.1, t.2⟩

/-- **The pushforward on the degree-`k` carrier.** -/
def tupMap (f : X ⟶ Y) (r k : ℕ) : tupMod K X r k →ₗ[K] tupMod K Y r k :=
  Finsupp.lmapDomain K K (tupPushIdx f)

theorem tupMap_single (f : X ⟶ Y) {k : ℕ} (t : TupIdx X r k) :
    tupMap K f r k (Finsupp.single t (1 : K)) = Finsupp.single (tupPushIdx f t) (1 : K) := by
  rw [tupMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tupIncl_comp_tupMap (f : X ⟶ Y) (k : ℕ) :
    (tupIncl K Y r k).comp (tupMap K f r k) = (tupAllMap K f r).comp (tupIncl K X r k) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupMap_single, tupIncl_single, tupIncl_single, tupAllMap_single]
  rfl

/-- **The pushforward is a chain map.** -/
theorem tupMap_tupD (f : X ⟶ Y) (k : ℕ) (x : tupMod K X r (k + 1)) :
    tupMap K f r k (tupD K X r k x) = tupD K Y r k (tupMap K f r (k + 1) x) := by
  apply tupIncl_injective K Y k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupMap K f k) (tupD K X r k x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) x
  have h3 := LinearMap.congr_fun (tupIncl_comp_tupD K Y k) (tupMap K f r (k + 1) x)
  have h4 := LinearMap.congr_fun (tupIncl_comp_tupMap K f (k + 1)) x
  simp only [LinearMap.comp_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact LinearMap.congr_fun (tupAllMap_comp_tupDAll K f) (tupIncl K X r (k + 1) x)

/-- **The pushforward commutes with the cyclic action.** -/
theorem tupMap_tupT (f : X ⟶ Y) (k : ℕ) (x : tupMod K X r k) :
    tupMap K f r k (tupT K X r k x) = tupT K Y r k (tupMap K f r k x) := by
  apply tupIncl_injective K Y k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupMap K f k) (tupT K X r k x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupT K X k) x
  have h3 := LinearMap.congr_fun (tupIncl_comp_tupT K Y k) (tupMap K f r k x)
  have h4 := LinearMap.congr_fun (tupIncl_comp_tupMap K f k) x
  simp only [LinearMap.comp_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact LinearMap.congr_fun (tupAllMap_comp_tupTAll K f) (tupIncl K X r k x)

theorem tupMap_id (k : ℕ) (x : tupMod K X r k) : tupMap K (𝟙 X) r k x = x := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add u v hu hv => rw [map_add, hu, hv]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, tupMap_single]
    congr 2
    exact Subtype.ext (funext fun j => tagPush_id (t.1 j))

theorem tupMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ) (x : tupMod K X r k) :
    tupMap K (f ≫ g) r k x = tupMap K g r k (tupMap K f r k x) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, tupMap_single, tupMap_single,
      tupMap_single]
    congr 2
    exact Subtype.ext (funext fun j => tagPush_comp f g (t.1 j))

end Push

end

end GroupApproximation.CharClass
