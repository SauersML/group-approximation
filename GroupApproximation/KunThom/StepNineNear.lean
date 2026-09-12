import GroupApproximation.KunThom.RelativeFunctorMetric
import GroupApproximation.KunThom.CountingEndgameRestrict
import GroupApproximation.KunThom.FixedPointNormalizationScaledBisection
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBridges

/-!
# Step 9: the near bound from the counting lift and estimate (7)

`BlockPatching.BlockArrows.card_hammingDisagreement_patch_conj_le_stepNine` re-separates,
on every retained object `i`, the arrow `a_i` of the patched bisection `â` from the raw
map of the relative functor on `b_{π i}`.  Its hypothesis `hnear` asks that the two
disagree on fewer than `2 * sc i` points.  In Kun and Thom (arXiv:2608.06222v3, proof of
Theorem 4.1) this comes from three facts:
* the counting endgame lifts `â` to a bisection `b` whose arrow at `π i` is sent by the
  relative functor to the arrow of `â` at `i`;
* estimate (7) puts every representative of that image within the target radius plus
  the improvement radius of the raw map;
* the distance gap of the cluster groupoid puts the chosen representative `a_i` within
  the radius of any other representative of its class.

* `FinitePartialBijection.card_disagreement_le_twoSidedDisagreement`: the one-sided
  disagreement is at most the two-sided one.
* `GroupoidPresentation.ClusterMetric.twoSidedDisagreement_lt_of_heq_ofRep`: a
  representative of a class equal, after an equality of target objects, to the class of
  a near representative is near up to one more radius.
* `BlockPatching.card_disagreement_sandwich_lt_of_lift`: the near bound of step 9 at one
  object, from the output of `CountingEndgame.exists_bisection_lift_restrict` at a
  retained object and estimate (7) along the functor.  For the relative functor of
  `RelativeFunctorAssembly`, the hypothesis `h7` is
  `GroupoidPresentation.ClusterMetric.twoSidedDisagreement_sandwich_lt_of_ofRep_eq` with
  `ε X Z := radius (obj X.val).1 (obj Z.val).1 + ρ X.val Z.val`.
-/

namespace GroupApproximation

universe u v

open CategoryTheory FinitePartialBijection

namespace FinitePartialBijection

/-- The one-sided disagreement is at most the two-sided disagreement. -/
theorem card_disagreement_le_twoSidedDisagreement {Y Z : FiniteModel}
    (b c : FinitePartialBijection Y Z) : (b.disagreement c).card ≤ b.twoSidedDisagreement c :=
  Nat.le_add_right _ _

end FinitePartialBijection

namespace GroupoidPresentation
namespace ClusterMetric

/-- **Transport of nearness along equal target objects.**  Let `θ` and `θ'` be
representatives from `i` to `j` and to `j'`, with `j = j'`, whose classes agree after that
equality.  If `θ` is within `B` of a family `w` at `j`, then `θ'` is within the radius plus
`B` of `w` at `j'`. -/
theorem twoSidedDisagreement_lt_of_heq_ofRep {I : Type u} {P : GroupoidPresentation.{u, v} I}
    (MP : P.ClusterMetric) {i j j' : I} (hj : j = j') (θ : P.Rep i j) (θ' : P.Rep i j')
    (hcls : HEq (P.ofRep (X := ⟨i⟩) (Y := ⟨j⟩) θ) (P.ofRep (X := ⟨i⟩) (Y := ⟨j'⟩) θ'))
    (w : ∀ k, FinitePartialBijection (MP.model i) (MP.model k)) {B : ℕ}
    (hB : (MP.val θ).twoSidedDisagreement (w j) < B) :
    (MP.val θ').twoSidedDisagreement (w j') < MP.radius i j' + B := by
  subst hj
  have hrel : P.rel i j θ' θ := Quotient.exact (eq_of_heq hcls).symm
  have hd := MP.lt_of_rel hrel
  have htri := FinitePartialBijection.twoSidedDisagreement_le (MP.val θ') (MP.val θ) (w j)
  omega

end ClusterMetric
end GroupoidPresentation

namespace BlockPatching

/-- **The near bound of step 9 at one object.**  Let `F` be a functor between the cluster
groupoid restricted to the retained objects `R` and to their images `D'`, along which
estimate (7) holds with bound `ε`, for the bridges realized by `q⁻¹`.  Suppose the counting
endgame lifts the bisection `â` at the retained object `x`: an arrow `g` out of `x` is sent
by `F` to the arrow of `â` at the image of `x`, and the bisection `b` carries `g` at `x`.
Then on the object `i` of `x`, and for any `π` with `π i = x`, the arrow of `â` disagrees
with the raw map of `b_{π i}` on fewer than `2 * sc` points, once `2 * sc` exceeds a radius
at `i` plus `ε`. -/
theorem card_disagreement_sandwich_lt_of_lift {I : Type u} [Fintype I]
    (D : ScaledFinitePartialClusterData I) {M : FiniteModel} (ι : ∀ X, D.model X → M)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm M) {R D' : Set I}
    (F : (D.presentation.restrict R).Obj ⥤ (D.presentation.restrict D').Obj)
    (ε : (D.presentation.restrict R).Obj → (D.presentation.restrict R).Obj → ℕ)
    (h7 : ∀ {X Z : (D.presentation.restrict R).Obj} (c : D.presentation.Rep X.val.1 Z.val.1)
      (θ : D.presentation.Rep (F.obj X).val.1 (F.obj Z).val.1),
      (D.presentation.restrict D').ofRep (X := F.obj X) (Y := F.obj Z) θ =
          F.map ((D.presentation.restrict R).ofRep (X := X) (Y := Z) c) →
        (D.clusterMetric.val θ).twoSidedDisagreement
          (sandwich ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹ X.val.1
              (F.obj X).val.1)
            ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹ Z.val.1 (F.obj Z).val.1)
            (D.clusterMetric.val c)) < ε X Z)
    (â b : FiniteGroupoid.Bisection D.presentation.Obj) {x : I} (hx : x ∈ R)
    {S : (D.presentation.restrict R).Obj}
    (g : (⟨⟨x, hx⟩⟩ : (D.presentation.restrict R).Obj) ⟶ S)
    (h₁ : â.objEquiv ((F ⋙ D.presentation.restrictInclusionFunctor D').obj ⟨⟨x, hx⟩⟩) =
      (F ⋙ D.presentation.restrictInclusionFunctor D').obj S)
    (hg₁ : (F ⋙ D.presentation.restrictInclusionFunctor D').map g =
      â.hom ((F ⋙ D.presentation.restrictInclusionFunctor D').obj ⟨⟨x, hx⟩⟩) ≫ eqToHom h₁)
    (e : b.objEquiv ((D.presentation.restrictInclusionFunctor R).obj ⟨⟨x, hx⟩⟩) =
      (D.presentation.restrictInclusionFunctor R).obj S)
    (hg₂ : b.hom ((D.presentation.restrictInclusionFunctor R).obj ⟨⟨x, hx⟩⟩) ≫ eqToHom e =
      (D.presentation.restrictInclusionFunctor R).map g)
    (π : I → I) {i : I} (hi : (F.obj ⟨⟨x, hx⟩⟩).val.1 = i) (hπ : π i = x) {sc : ℕ}
    (hsc : ∀ (Z : (D.presentation.restrict R).Obj) (j : I),
      D.clusterMetric.radius i j + ε ⟨⟨x, hx⟩⟩ Z ≤ 2 * sc) :
    (((scaledBisectionArrows (D := D) ι hinj hdisj â).arrow i).disagreement
      (sandwich ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹ (π i) i)
        ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹
          ((scaledBisectionArrows (D := D) ι hinj hdisj b).objEquiv (π i))
          ((scaledBisectionArrows (D := D) ι hinj hdisj â).objEquiv i))
        ((scaledBisectionArrows (D := D) ι hinj hdisj b).arrow (π i)))).card < 2 * sc := by
  rw [hπ]
  subst hi
  rcases S with ⟨⟨y, hy⟩⟩
  have ey : scaledBisectionIndexEquiv (D := D) b x = y :=
    congrArg GroupoidPresentation.Obj.val e
  subst ey
  induction g using Quotient.inductionOn with
  | _ ρ₀ =>
    -- the chosen representative of `b` at `x` represents the lifted arrow
    have hheq₂ := (comp_eqToHom_heq
      (b.hom ((D.presentation.restrictInclusionFunctor R).obj ⟨⟨x, hx⟩⟩)) e).symm.trans
        (heq_of_eq hg₂)
    have hb : (b.hom ((D.presentation.restrictInclusionFunctor R).obj ⟨⟨x, hx⟩⟩) :
        Quotient (D.presentation.rel x (scaledBisectionIndexEquiv (D := D) b x))) =
        Quotient.mk _ ρ₀ :=
      eq_of_heq hheq₂
    have hrelb : D.presentation.rel x (scaledBisectionIndexEquiv (D := D) b x)
        (scaledBisectionRep (D := D) b x) ρ₀ :=
      Quotient.exact ((Quotient.out_eq _).trans hb)
    have hcθ : (D.presentation.restrict R).ofRep (X := ⟨⟨x, hx⟩⟩)
        (Y := ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩)
        (scaledBisectionRep (D := D) b x) = Quotient.mk _ ρ₀ :=
      Quotient.sound hrelb
    -- a representative of the image of that arrow
    obtain ⟨θ, hθ⟩ : ∃ θ : D.presentation.Rep (F.obj ⟨⟨x, hx⟩⟩).val.1
        (F.obj ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩).val.1,
        (D.presentation.restrict D').ofRep (X := F.obj ⟨⟨x, hx⟩⟩)
          (Y := F.obj ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩) θ =
        F.map ((D.presentation.restrict R).ofRep (X := ⟨⟨x, hx⟩⟩)
          (Y := ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩)
          (scaledBisectionRep (D := D) b x)) :=
      ⟨Quotient.out (F.map ((D.presentation.restrict R).ofRep (X := ⟨⟨x, hx⟩⟩)
          (Y := ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩)
          (scaledBisectionRep (D := D) b x))), Quotient.out_eq _⟩
    have h7c := h7 (X := ⟨⟨x, hx⟩⟩) (Z := ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩)
      (scaledBisectionRep (D := D) b x) θ hθ
    -- its class is the arrow of `â` at the image of `x`, after the object equality
    have h₃ : D.presentation.ofRep (X := ⟨(F.obj ⟨⟨x, hx⟩⟩).val.1⟩)
        (Y := ⟨(F.obj ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩).val.1⟩) θ =
        (F ⋙ D.presentation.restrictInclusionFunctor D').map (Quotient.mk _ ρ₀) :=
      (congrArg (D.presentation.restrictInclusionFunctor D').map hθ).trans
        (congrArg (F ⋙ D.presentation.restrictInclusionFunctor D').map hcθ)
    have hheq₁ := (heq_of_eq hg₁).trans (comp_eqToHom_heq
      (â.hom ((F ⋙ D.presentation.restrictInclusionFunctor D').obj ⟨⟨x, hx⟩⟩)) h₁)
    have hj : (F.obj ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩).val.1 =
        scaledBisectionIndexEquiv (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1 :=
      (congrArg GroupoidPresentation.Obj.val h₁).symm
    have hcls : HEq (D.presentation.ofRep (X := ⟨(F.obj ⟨⟨x, hx⟩⟩).val.1⟩)
        (Y := ⟨(F.obj ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩).val.1⟩) θ)
        (D.presentation.ofRep (X := ⟨(F.obj ⟨⟨x, hx⟩⟩).val.1⟩)
          (Y := ⟨scaledBisectionIndexEquiv (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1⟩)
          (scaledBisectionRep (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1)) :=
      (heq_of_eq h₃).trans (hheq₁.trans (heq_of_eq (Quotient.out_eq _).symm))
    have htr : ((scaledBisectionArrows (D := D) ι hinj hdisj â).arrow
          (F.obj ⟨⟨x, hx⟩⟩).val.1).twoSidedDisagreement
        (sandwich ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹ x
            (F.obj ⟨⟨x, hx⟩⟩).val.1)
          ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹
            ((scaledBisectionArrows (D := D) ι hinj hdisj b).objEquiv x)
            ((scaledBisectionArrows (D := D) ι hinj hdisj â).objEquiv
              (F.obj ⟨⟨x, hx⟩⟩).val.1))
          ((scaledBisectionArrows (D := D) ι hinj hdisj b).arrow x)) <
        D.clusterMetric.radius (F.obj ⟨⟨x, hx⟩⟩).val.1
            (scaledBisectionIndexEquiv (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1) +
          ε ⟨⟨x, hx⟩⟩ ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩ :=
      D.clusterMetric.twoSidedDisagreement_lt_of_heq_ofRep hj θ
        (scaledBisectionRep (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1) hcls
        (fun k ↦ sandwich ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹ x
            (F.obj ⟨⟨x, hx⟩⟩).val.1)
          ((scaledClusterEmbedding D ι hinj hdisj).bridge q⁻¹
            (scaledBisectionIndexEquiv (D := D) b x) k)
          (D.clusterMetric.val (scaledBisectionRep (D := D) b x))) h7c
    exact lt_of_le_of_lt (card_disagreement_le_twoSidedDisagreement _ _)
      (lt_of_lt_of_le htr (hsc ⟨⟨scaledBisectionIndexEquiv (D := D) b x, hy⟩⟩
        (scaledBisectionIndexEquiv (D := D) â (F.obj ⟨⟨x, hx⟩⟩).val.1)))

end BlockPatching
end GroupApproximation
