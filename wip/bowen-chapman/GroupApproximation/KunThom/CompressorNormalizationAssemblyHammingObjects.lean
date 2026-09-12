import GroupApproximation.KunThom.CountingEndgameProps
import GroupApproximation.KunThom.StepNineNear

/-!
# Step 9 over cluster frames: the objects covered by a transported bisection

`CountingEndgame.CompressorRelativeData.Transported a b` gives, at every selected retained
object `X`, a target `sel X` and an arrow `g : X ⟶ sel X`.  The relative functor sends `g`
to the arrow of `a` at `F X`, and the bisection `b` carries `g` at `X`.  This file reads off
the three facts the step 9 Hamming estimate of Kun and Thom (arXiv:2608.06222v3, proof of
Theorem 4.1) needs on the object `i = F X`, with `π` the matching of the relative functor.

* `matching_liftFunctor_obj`: `π i = X`, from `F (π j) = j` and the surjectivity of `π`
  onto the retained objects.
* `transported_objEquiv`: the image block of `π i` under `b` is `π` of the image block of
  `i` under `a`, and the latter is a matched object.  This identifies the bridge realized by
  `A(t)⁻¹` between the two image blocks as a bridge of the matching.
* `card_disagreement_lt_of_transported`: the arrow of `a` at `i` disagrees with the raw map
  of the relative functor on the arrow of `b` at `π i` on fewer than `6 · scale i` points,
  given estimate (7) with error at most `3 · scale i`.  This is the hypothesis `hnear`
  of `BlockPatching.vanishing_hammingDistance_patch_conj`, through
  `BlockPatching.card_disagreement_sandwich_lt_of_lift`.
-/

namespace GroupApproximation
namespace CompressorHamming

open CategoryTheory CompressorNormalizationAssembly CountingEndgame GroupoidPresentation
open FinitePartialBijection

variable {G : Type} [Group G] {A : SoficApproximation G} {K : Type} [Group K] {ι : K →* G}
  {R : RetainedComponents A K ι} {F : ClusterFrame R} {t : G}

/-- **The matching inverts the functor on objects.**  For a retained object `X`, the
matching of the relative functor sends the object of `F X` back to `X`. -/
theorem matching_liftFunctor_obj (M : CompressorRelativeData t F) (n : ℕ)
    (X : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj) :
    (M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val = X.val.1 := by
  obtain ⟨j, hj, hjx⟩ := (M.functor t M.mem_compressors n).surjOn X.val.2
  have hval : X.val = ⟨(M.functor t M.mem_compressors n).π j,
      (M.functor t M.mem_compressors n).mapsTo hj⟩ := Subtype.ext hjx.symm
  have hobj := (M.functor t M.mem_compressors n).obj_π j (Finset.mem_coe.mp hj)
  have hlift : ((M.liftFunctor n).obj X).val = j := by
    show ((M.functor t M.mem_compressors n).F.obj X.val).1 = j
    rw [hval, hobj]
  rw [hlift, hjx]

/-- **Image blocks of a transported bisection.**  If `F (sel)` is the target of the arrow of
`a` at `F X`, and `b` carries `X` to `sel`, then the image of `π (F X)` under `b` is `π` of
the image of `F X` under `a`, and the latter is a matched object. -/
theorem transported_objEquiv (M : CompressorRelativeData t F) (a b : ∀ n, F.Bis n) (n : ℕ)
    (X sel : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
    (hsel : (M.liftFunctor n).obj sel = (a n).objEquiv ((M.liftFunctor n).obj X))
    (e : (b n).objEquiv ((M.inclusion n).obj X) = (M.inclusion n).obj sel) :
    (F.arrows n (b n)).objEquiv
        ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val) =
        (M.functor t M.mem_compressors n).π
          ((F.arrows n (a n)).objEquiv ((M.liftFunctor n).obj X).val) ∧
      (F.arrows n (a n)).objEquiv ((M.liftFunctor n).obj X).val ∈ M.matched t n := by
  have h₁ := matching_liftFunctor_obj M n X
  have h₂ := matching_liftFunctor_obj M n sel
  have hb : (F.arrows n (b n)).objEquiv X.val.1 = sel.val.1 :=
    congrArg GroupoidPresentation.Obj.val e
  have ha : (F.arrows n (a n)).objEquiv ((M.liftFunctor n).obj X).val =
      ((M.liftFunctor n).obj sel).val :=
    (congrArg GroupoidPresentation.Obj.val hsel).symm
  refine ⟨?_, ?_⟩
  · rw [h₁, hb, ha, h₂]
  · rw [ha]
    exact Finset.mem_coe.mp ((M.functor t M.mem_compressors n).F.obj sel.val).2

/-- **The near bound at a covered object.**  Given estimate (7) for `t` at index `n` with
error `ε` at most three times the scale of the image, the arrow of `a` at `i = F X`
disagrees with the raw map of the relative functor on the arrow of `b` at `π i` on fewer
than `6 · scale i` points. -/
theorem card_disagreement_lt_of_transported (M : CompressorRelativeData t F) (n : ℕ)
    (ε : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj → ℕ)
    (h7 : ∀ {X Z : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
      (c : (F.system n).presentation.Rep X.val.1 Z.val.1)
      (θ : (F.system n).presentation.Rep
        ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1
        ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1),
      ((F.system n).presentation.restrict (M.matched t n : Set (F.Obj n))).ofRep
          (X := (M.functor t M.mem_compressors n).F.toFunctor.obj X)
          (Y := (M.functor t M.mem_compressors n).F.toFunctor.obj Z) θ =
        (M.functor t M.mem_compressors n).F.toFunctor.map
          (((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).ofRep
            (X := X) (Y := Z) c) →
      ((F.system n).clusterMetric.val θ).twoSidedDisagreement
        (sandwich
          ((F.embedding n).bridge (A.map n t)⁻¹ X.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
          ((F.embedding n).bridge (A.map n t)⁻¹ Z.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1)
          ((F.system n).clusterMetric.val c)) < ε X Z)
    (hε : ∀ X Z, ε X Z ≤
      3 * (F.system n).scale ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
    (a b : F.Bis n)
    (X sel : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
    (hsel : (M.liftFunctor n).obj sel = a.objEquiv ((M.liftFunctor n).obj X))
    (g : X ⟶ sel)
    (hg₁ : (M.liftFunctor n).map g = a.hom ((M.liftFunctor n).obj X) ≫ eqToHom hsel.symm)
    (e : b.objEquiv ((M.inclusion n).obj X) = (M.inclusion n).obj sel)
    (hg₂ : b.hom ((M.inclusion n).obj X) ≫ eqToHom e = (M.inclusion n).map g) :
    ((F.arrows n a).arrow ((M.liftFunctor n).obj X).val).disagreement
      (sandwich
        ((F.embedding n).bridge (A.map n t)⁻¹
          ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val)
          ((M.liftFunctor n).obj X).val)
        ((F.embedding n).bridge (A.map n t)⁻¹
          ((F.arrows n b).objEquiv
            ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val))
          ((F.arrows n a).objEquiv ((M.liftFunctor n).obj X).val))
        ((F.arrows n b).arrow
          ((M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val))).card <
      2 * (3 * (F.system n).scale ((M.liftFunctor n).obj X).val) := by
  obtain ⟨⟨x, hx⟩⟩ := X
  refine BlockPatching.card_disagreement_sandwich_lt_of_lift (F.system n).clusterData
    (F.embedAt n) (F.embedAt_injective n) (F.embedAt_disjoint n) (A.map n t)
    (M.functor t M.mem_compressors n).F.toFunctor ε h7 a b hx g hsel.symm hg₁ e hg₂
    (M.functor t M.mem_compressors n).π rfl (matching_liftFunctor_obj M n ⟨⟨x, hx⟩⟩)
    fun Z j ↦ ?_
  show (F.system n).clusterData.clusterMetric.radius
      ((M.functor t M.mem_compressors n).F.toFunctor.obj ⟨⟨x, hx⟩⟩).val.1 j +
        ε ⟨⟨x, hx⟩⟩ Z ≤
      2 * (3 * (F.system n).scale
        ((M.functor t M.mem_compressors n).F.toFunctor.obj ⟨⟨x, hx⟩⟩).val.1)
  have hr : (F.system n).clusterData.clusterMetric.radius
      ((M.functor t M.mem_compressors n).F.toFunctor.obj ⟨⟨x, hx⟩⟩).val.1 j =
      2 * min ((F.system n).scale
        ((M.functor t M.mem_compressors n).F.toFunctor.obj ⟨⟨x, hx⟩⟩).val.1)
        ((F.system n).scale j) := rfl
  have hmin := Nat.min_le_left ((F.system n).scale
    ((M.functor t M.mem_compressors n).F.toFunctor.obj ⟨⟨x, hx⟩⟩).val.1)
    ((F.system n).scale j)
  have hεZ := hε ⟨⟨x, hx⟩⟩ Z
  omega

end CompressorHamming
end GroupApproximation
