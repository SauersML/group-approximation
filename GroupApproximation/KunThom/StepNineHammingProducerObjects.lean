import GroupApproximation.KunThom.StepNineHammingProducerNear

/-!
# Step 9 over cluster frames: the objects covered by a transported bisection

`CountingEndgame.CompressorRelativeData.Transported a b` gives, at every selected retained
object `X`, a target `sel X` and an arrow `g : X ⟶ sel X`.  This file reads off the facts
on the object `i = F X` that the step 9 Hamming estimate of Kun and Thom
(arXiv:2608.06222v3, proof of Theorem 4.1) needs for its budget, with `π` the matching of
the relative functor.  The proofs follow the drafts of lane kt41-alt-route.

* `matching_liftFunctor_obj`: `π i = X`.
* `transported_objEquiv`: the image block of `π i` under `b` is `π` of the image block of
  `i` under `a`, and the latter is a matched object.  This identifies the bridge realized by
  `A(t)⁻¹` between the two image blocks as a bridge of the matching.
-/

namespace GroupApproximation
namespace StepNineHammingProducer

open CategoryTheory CompressorNormalizationAssembly CountingEndgame GroupoidPresentation

open Classical in
/-- **The matching inverts the functor on objects.**  For a retained object `X`, the
matching of the relative functor sends the object of `F X` back to `X`. -/
theorem matching_liftFunctor_obj {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {F : ClusterFrame R} {t : G}
    (M : CompressorRelativeData t F) (n : ℕ)
    (X : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj) :
    (M.functor t M.mem_compressors n).π ((M.liftFunctor n).obj X).val = X.val.1 :=
  relativeClusterFunctor_π_obj (M.functor t M.mem_compressors n) X.val

open Classical in
/-- **Image blocks of a transported bisection.**  If `F (sel)` is the target of the arrow of
`a` at `F X`, and `b` carries `X` to `sel`, then the image of `π (F X)` under `b` is `π` of
the image of `F X` under `a`, and the latter is a matched object. -/
theorem transported_objEquiv {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {F : ClusterFrame R} {t : G}
    (M : CompressorRelativeData t F) (a b : ∀ n, F.Bis n) (n : ℕ)
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

end StepNineHammingProducer
end GroupApproximation
