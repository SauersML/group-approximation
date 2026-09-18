import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Formal glue for the `K₂` split of `K₂(N, F_p[s_1..s_k]) = 0`

Lane `bh-met-14`, helper module.  These lemmas hold for arbitrary rings and index types, with no
hypothesis:

* `eq_one_of_K2_eq_bot`: an element of a trivial `K₂(I, R)` is `1`;
* `k2StabInjective_of_injective`: injectivity of `K2Stab m R : K₂(m, R) →* K₂(m+1, R)` is the
  Steinberg-level form `GroupApproximation.Full.LVH2GL3.K2StabInjective R m`.  So the existing
  telescoping lemma `GroupApproximation.Full.LVH2GL3.eq_one_of_indexMap_eq_one` applies to it.
  The two forms agree because `Fin.castSuccEmb` is by definition `Fin.castLEEmb _`;
* `K2IndexMap_K2Map`: coefficient maps commute with index padding on `K₂` (from
  `GroupApproximation.Full.LVStableK2.indexMap_ringMap`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- An element of a trivial unstable `K₂(I, R)` is `1`. -/
theorem eq_one_of_K2_eq_bot {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]
    (h : K2 I R = ⊥) (v : K2 I R) : v = 1 :=
  Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h v v.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.eq_one_of_K2_eq_bot

/-- Injectivity of the stabilization `K₂(m, R) →* K₂(m+1, R)` gives the Steinberg-level
injective stability `K2StabInjective R m`. -/
theorem k2StabInjective_of_injective {R : Type*} [Ring R] {m : ℕ}
    (h : Function.Injective (K2Stab m R)) :
    GroupApproximation.Full.LVH2GL3.K2StabInjective R m := by
  intro g hg hg1
  have h1 : (⟨g, (mem_K2_iff g).mpr hg⟩ : K2n m R) = 1 := by
    apply h
    rw [map_one]
    exact Subtype.ext hg1
  exact congrArg Subtype.val h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2StabInjective_of_injective

/-- Coefficient maps commute with index padding on the unstable `K₂`. -/
theorem K2IndexMap_K2Map {I J R S : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Ring R] [Ring S] (e : I ↪ J) (f : R →+* S) (u : K2 I R) :
    K2IndexMap e (K2Map f u) = K2Map f (K2IndexMap e u) :=
  Subtype.ext (GroupApproximation.Full.LVStableK2.indexMap_ringMap e f (u : SteinbergGroup I R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2IndexMap_K2Map

end GroupApproximation.BooneHigman.Metabelian.ElemFP
