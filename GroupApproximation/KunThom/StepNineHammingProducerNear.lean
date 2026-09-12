import GroupApproximation.KunThom.StepNineHammingFrame
import GroupApproximation.KunThom.StepNineNear
import GroupApproximation.KunThom.CountingEndgameProps

/-!
# Step 9 over a cluster frame: the near bound at the selected objects

The hypothesis `hhamming` of the per-compressor assembly of Kun--Thom Theorem 4.1
(arXiv:2608.06222v3) starts from `CountingEndgame.CompressorRelativeData.Transported`.
At every selected retained object `X`, the lifted bisection `b` carries a preimage under
the relative functor of the arrow of `a` at the image `i` of `X`.  With estimate (7) of the
functor and an error at most three times the scale of `i`, this gives the near bound
`hnear` of `BlockPatching.BlockArrows.card_hammingDisagreement_patch_conj_le_stepNine`
at `i`, for the raw map of `b_{π i}`.

* `relativeClusterFunctor_π_obj`: a relative cluster functor sends a retained object to an
  object whose match is the retained object.
* `card_disagreement_sandwich_lt_of_transported`: the near bound at `i` with `sc := 3 · scale i`,
  through `BlockPatching.card_disagreement_sandwich_lt_of_lift`.
-/

namespace GroupApproximation
namespace StepNineHammingProducer

open CategoryTheory FinitePartialBijection GroupoidPresentation BlockPatching
  CompressorNormalizationAssembly

universe u v

/-- **The match of an image.**  A bundled relative cluster functor sends a retained object
`X` to an object whose match under `π` is `X`. -/
theorem relativeClusterFunctor_π_obj {I : Type u} {P : GroupoidPresentation.{u, v} I}
    {R D : Finset I} (𝓕 : P.RelativeClusterFunctor R D) (X : (R : Set I)) :
    𝓕.π (𝓕.F.obj X).1 = X.1 := by
  obtain ⟨j, hj, hjX⟩ := 𝓕.surjOn X.2
  have hX : X = ⟨𝓕.π j, 𝓕.mapsTo hj⟩ := Subtype.ext hjX.symm
  subst hX
  rw [𝓕.obj_π j (Finset.mem_coe.mp hj)]

open Classical in
/-- **The near bound at a selected object.**  Let the relative functor of `t` satisfy
estimate (7) for the bridges realized by `A(t)⁻¹`, with an error `ε` at most three times
the scale of the image object.  If the bisection `b` lifts the bisection `a` at the retained
object `X`, then on the image object `i` of `X` the arrow of `a` disagrees with the raw map
of `b_{π i}` on fewer than `2 · (3 · scale i)` points. -/
theorem card_disagreement_sandwich_lt_of_transported {G : Type} [Group G]
    {A : SoficApproximation G} {K : Type} [Group K] {ι : K →* G}
    {R : RetainedComponents A K ι} (F : ClusterFrame R) {t : G}
    (M : CountingEndgame.CompressorRelativeData t F) (n : ℕ)
    (ε : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj → ℕ)
    (h7 : ∀ {X Z : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
      (c : (F.system n).clusterData.presentation.Rep X.val.1 Z.val.1)
      (θ : (F.system n).clusterData.presentation.Rep
        ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1
        ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1),
      ((F.system n).clusterData.presentation.restrict (M.matched t n : Set (F.Obj n))).ofRep
          (X := (M.functor t M.mem_compressors n).F.toFunctor.obj X)
          (Y := (M.functor t M.mem_compressors n).F.toFunctor.obj Z) θ =
        (M.functor t M.mem_compressors n).F.toFunctor.map
          (((F.system n).clusterData.presentation.restrict (M.retained t n : Set (F.Obj n))).ofRep
            (X := X) (Y := Z) c) →
      ((F.system n).clusterData.clusterMetric.val θ).twoSidedDisagreement
        (sandwich ((F.embedding n).bridge (A.map n t)⁻¹ X.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
          ((F.embedding n).bridge (A.map n t)⁻¹ Z.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1)
          ((F.system n).clusterData.clusterMetric.val c)) < ε X Z)
    (hε : ∀ X Z, ε X Z ≤
      3 * (F.system n).scale ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
    (a b : F.Bis n)
    {X : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
    {S : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
    (hsel : (M.liftFunctor n).obj S = a.objEquiv ((M.liftFunctor n).obj X))
    (g : X ⟶ S)
    (hg : (M.liftFunctor n).map g = a.hom ((M.liftFunctor n).obj X) ≫ eqToHom hsel.symm)
    (e : b.objEquiv ((M.inclusion n).obj X) = (M.inclusion n).obj S)
    (he : b.hom ((M.inclusion n).obj X) ≫ eqToHom e = (M.inclusion n).map g) :
    (((F.arrows n a).arrow ((M.liftFunctor n).obj X).val).disagreement
      (sandwich ((F.embedding n).bridge (A.map n t)⁻¹
          ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val)
          ((M.liftFunctor n).obj X).val)
        ((F.embedding n).bridge (A.map n t)⁻¹
          ((F.arrows n b).objEquiv
            ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val))
          ((F.arrows n a).objEquiv ((M.liftFunctor n).obj X).val))
        ((F.arrows n b).arrow
          ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val)))).card <
      2 * (3 * (F.system n).scale ((M.liftFunctor n).obj X).val) := by
  have hπ : (M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val = X.val.1 :=
    relativeClusterFunctor_π_obj (M.functor t M.mem_compressors n) X.val
  have hsc : ∀ (Z : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
      (j : F.Obj n), (F.system n).clusterData.clusterMetric.radius
          ((M.liftFunctor n).obj X).val j + ε X Z ≤
        2 * (3 * (F.system n).scale ((M.liftFunctor n).obj X).val) := by
    intro Z j
    have hr : (F.system n).clusterData.clusterMetric.radius ((M.liftFunctor n).obj X).val j =
        2 * min ((F.system n).scale ((M.liftFunctor n).obj X).val) ((F.system n).scale j) :=
      rfl
    have hεX := hε X Z
    have hm := min_le_left ((F.system n).scale ((M.liftFunctor n).obj X).val)
      ((F.system n).scale j)
    have hobj : ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1 =
        ((M.liftFunctor n).obj X).val :=
      rfl
    rw [hobj] at hεX
    omega
  exact card_disagreement_sandwich_lt_of_lift (F.system n).clusterData (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n) (A.map n t)
    (M.functor t M.mem_compressors n).F.toFunctor ε h7 a b X.val.2 g hsel.symm hg e he
    (M.functor t M.mem_compressors n).π rfl hπ hsc

end StepNineHammingProducer
end GroupApproximation
