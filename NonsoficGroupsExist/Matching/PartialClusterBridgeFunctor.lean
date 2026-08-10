import NonsoficGroupsExist.Matching.FiniteGroupoidFunctor
import NonsoficGroupsExist.Matching.FinitePartialClusterGroupoid
import NonsoficGroupsExist.Matching.PartialBijectionSandwich

/-!
# A quantitative seam for compressor functors between cluster groupoids

At a finite stage, an object is sent to a matched component and an arrow is
transported through the two co-large overlap bridges.  The transported raw
partial bijection is then repaired to a cluster candidate.  This file proves
that explicit bounds on bridge defects and repair disagreement force the
repaired representative map to respect identities, composition, and the
cluster relation.

The structure below is deliberately finite and quantitative: its fields are
cardinal inequalities for concrete partial bijections.  It contains no
groupoid functor, quotient-level law, asymptotic statement, or rigidity
conclusion.  `toFunctorData` derives all of that finite quotient bookkeeping.
-/

namespace NonsoficGroupsExist

universe u v

/-- Concrete finite data from which the compressor representative map
descends to a functor between two partial-cluster groupoids. -/
structure PartialClusterBridgeData
    {I : Type u} [Fintype I] {J : Type v} [Fintype J]
    (P : FinitePartialClusterData I)
    (Q : FinitePartialClusterData J) where
  /-- Matched target component. -/
  obj : I → J
  /-- Co-large overlap arrow from a source component to its matched target. -/
  bridge : ∀ X, FinitePartialBijection (P.model X) (Q.model (obj X))
  /-- Repaired transport of a source cluster candidate. -/
  map : ∀ {X Y}, P.Rep X Y → Q.Rep (obj X) (obj Y)
  /-- Uniform strict bound for bridge self-defects. -/
  bridgeBound : ℕ
  /-- Uniform strict bound for repair disagreement. -/
  repairBound : ℕ
  bridge_small : ∀ X,
    (bridge X).sourceDefect + (bridge X).targetDefect < bridgeBound
  map_close : ∀ {X Y} (f : P.Rep X Y),
    (map f).1.twoSidedDisagreement
      (FinitePartialBijection.sandwich (bridge X) (bridge Y) f.1) < repairBound
  /-- Budget ensuring that transport respects the source cluster relation. -/
  relation_budget :
    2 * repairBound + 2 * bridgeBound + P.radius ≤ 8 * Q.radius
  /-- Budget ensuring that the transported identity lies in the identity
  cluster. -/
  one_budget : repairBound + 2 * bridgeBound ≤ 8 * Q.radius
  /-- Budget ensuring compatibility with repaired composition. -/
  comp_budget :
    3 * repairBound + 6 * bridgeBound + 3 * P.radius + Q.radius ≤
      8 * Q.radius
  /-- Budget ensuring that small target disagreement reflects small source
  disagreement, hence that the descended functor is faithful. -/
  reflect_budget :
    2 * repairBound + 14 * bridgeBound + 2 * P.radius + Q.radius ≤
      8 * P.radius

namespace PartialClusterBridgeData

variable {I : Type u} [Fintype I] {J : Type v} [Fintype J]
variable {P : FinitePartialClusterData I}
variable {Q : FinitePartialClusterData J}
variable (D : PartialClusterBridgeData P Q)

/-- The repaired bridge transport respects the finite cluster relation. -/
theorem map_respects {X Y : I} {f g : P.Rep X Y}
    (hfg : P.Near f g) : Q.Near (D.map f) (D.map g) := by
  apply Q.near_of_lt_eight
  let sf := FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) f.1
  let sg := FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) g.1
  have hf := D.map_close f
  have hg := D.map_close g
  have hs := FinitePartialBijection.twoSidedDisagreement_sandwich_le
    (D.bridge X) (D.bridge Y) f.1 g.1
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map f).1 sf sg
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map f).1 sg (D.map g).1
  have hg' : sg.twoSidedDisagreement (D.map g).1 < D.repairBound := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
    exact hg
  have hbx := D.bridge_small X
  have hby := D.bridge_small Y
  unfold FinitePartialClusterData.Near at hfg
  dsimp only [sf, sg] at hf hg' hs htri₁ htri₂
  omega

/-- The repaired transport of an identity represents the target identity. -/
theorem map_one (X : I) :
    Q.Near (D.map (P.presentation.one X)) (Q.presentation.one (D.obj X)) := by
  apply Q.near_of_lt_eight
  let s := FinitePartialBijection.sandwich
    (D.bridge X) (D.bridge X) (FinitePartialBijection.refl (P.model X))
  have hm := D.map_close (P.presentation.one X)
  have hs := FinitePartialBijection.twoSidedDisagreement_sandwich_refl
    (D.bridge X)
  have htri := FinitePartialBijection.twoSidedDisagreement_le
    (D.map (P.presentation.one X)).1 s
      (FinitePartialBijection.refl (Q.model (D.obj X)))
  have hb := D.bridge_small X
  change (D.map (P.presentation.one X)).1.twoSidedDisagreement
    (FinitePartialBijection.refl (Q.model (D.obj X))) < 8 * Q.radius
  change (D.map (P.presentation.one X)).1.twoSidedDisagreement s <
    D.repairBound at hm
  dsimp only [s] at hs htri
  omega

/-- The repaired bridge transport respects the rounded composition used by
the finite cluster presentations. -/
theorem map_comp {X Y Z : I} (f : P.Rep X Y) (g : P.Rep Y Z) :
    Q.Near (D.map (P.presentation.comp f g))
      (Q.presentation.comp (D.map f) (D.map g)) := by
  apply Q.near_of_lt_eight
  let pf : FinitePartialBijection (Q.model (D.obj X)) (Q.model (D.obj Y)) :=
    FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) f.1
  let pg : FinitePartialBijection (Q.model (D.obj Y)) (Q.model (D.obj Z)) :=
    FinitePartialBijection.sandwich (D.bridge Y) (D.bridge Z) g.1
  let pfg : FinitePartialBijection (Q.model (D.obj X)) (Q.model (D.obj Z)) :=
    FinitePartialBijection.sandwich (D.bridge X) (D.bridge Z) (f.1.trans g.1)
  let pimp : FinitePartialBijection (Q.model (D.obj X)) (Q.model (D.obj Z)) :=
    FinitePartialBijection.sandwich (D.bridge X) (D.bridge Z)
      (P.improve f.1 g.1)
  have hmapComp := D.map_close (P.presentation.comp f g)
  have himprove := P.improve_close f.1 f.2 g.1 g.2
  have himproveSandwich :=
    FinitePartialBijection.twoSidedDisagreement_sandwich_le
      (D.bridge X) (D.bridge Z) (P.improve f.1 g.1) (f.1.trans g.1)
  have hsandwichComp :=
    FinitePartialBijection.twoSidedDisagreement_sandwich_trans_le
      (D.bridge X) (D.bridge Y) (D.bridge Z) f.1 g.1
  have hf := D.map_close f
  have hg := D.map_close g
  have hmappedComp := FinitePartialBijection.twoSidedDisagreement_trans_le
    pf (D.map f).1 pg (D.map g).1
  have hqImprove := Q.improve_close
    (D.map f).1 (D.map f).2 (D.map g).1 (D.map g).2
  have hqImprove' :
      ((D.map f).1.trans (D.map g).1).twoSidedDisagreement
        (Q.improve (D.map f).1 (D.map g).1) < Q.radius := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
    exact hqImprove
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map (P.presentation.comp f g)).1 pimp pfg
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map (P.presentation.comp f g)).1 pfg (pf.trans pg)
  have htri₃ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map (P.presentation.comp f g)).1 (pf.trans pg)
      ((D.map f).1.trans (D.map g).1)
  have htri₄ := FinitePartialBijection.twoSidedDisagreement_le
    (D.map (P.presentation.comp f g)).1
      ((D.map f).1.trans (D.map g).1)
      (Q.improve (D.map f).1 (D.map g).1)
  have hbx := D.bridge_small X
  have hby := D.bridge_small Y
  have hbz := D.bridge_small Z
  have hsf := P.self_small f.1 f.2
  have hsg := P.self_small g.1 g.2
  change (D.map (P.presentation.comp f g)).1.twoSidedDisagreement
    (Q.improve (D.map f).1 (D.map g).1) < 8 * Q.radius
  change (D.map (P.presentation.comp f g)).1.twoSidedDisagreement pimp <
    D.repairBound at hmapComp
  dsimp only [pf, pg, pfg, pimp] at himproveSandwich hsandwichComp
    hf hg hmappedComp htri₁ htri₂ htri₃ htri₄
  omega

/-- Small disagreement after repaired bridge transport reflects the source
cluster relation.  The proof transports both target arrows back across the
same bridges and uses the explicit round-trip estimate. -/
theorem map_reflects {X Y : I} {f g : P.Rep X Y}
    (hfg : Q.Near (D.map f) (D.map g)) : P.Near f g := by
  apply P.near_of_lt_eight
  let sf := FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) f.1
  let sg := FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) g.1
  let bf := FinitePartialBijection.sandwich
    (D.bridge X).symm (D.bridge Y).symm (D.map f).1
  let bg := FinitePartialBijection.sandwich
    (D.bridge X).symm (D.bridge Y).symm (D.map g).1
  let rf := FinitePartialBijection.sandwich
    (D.bridge X).symm (D.bridge Y).symm sf
  let rg := FinitePartialBijection.sandwich
    (D.bridge X).symm (D.bridge Y).symm sg
  have hmf := D.map_close f
  have hmg := D.map_close g
  have hbf := FinitePartialBijection.twoSidedDisagreement_sandwich_le
    (D.bridge X).symm (D.bridge Y).symm (D.map f).1 sf
  have hbg := FinitePartialBijection.twoSidedDisagreement_sandwich_le
    (D.bridge X).symm (D.bridge Y).symm (D.map g).1 sg
  have hrf := FinitePartialBijection.twoSidedDisagreement_sandwich_roundtrip_le
    (D.bridge X) (D.bridge Y) f.1
  have hrg := FinitePartialBijection.twoSidedDisagreement_sandwich_roundtrip_le
    (D.bridge X) (D.bridge Y) g.1
  have hmiddle := FinitePartialBijection.twoSidedDisagreement_sandwich_le
    (D.bridge X).symm (D.bridge Y).symm (D.map f).1 (D.map g).1
  have hbfToF := FinitePartialBijection.twoSidedDisagreement_le bf rf f.1
  have hbgToG := FinitePartialBijection.twoSidedDisagreement_le bg rg g.1
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le f.1 bf bg
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le f.1 bg g.1
  have hfb : f.1.twoSidedDisagreement bf = bf.twoSidedDisagreement f.1 :=
    FinitePartialBijection.twoSidedDisagreement_comm _ _
  have hbx := D.bridge_small X
  have hby := D.bridge_small Y
  have hsf := P.self_small f.1 f.2
  have hsg := P.self_small g.1 g.2
  unfold FinitePartialClusterData.Near at hfg
  dsimp only [sf, sg, bf, bg, rf, rg] at hbf hbg hrf hrg hmiddle
    hbfToF hbgToG htri₁ htri₂ hfb
  simp only [FinitePartialBijection.sourceDefect_symm,
    FinitePartialBijection.targetDefect_symm] at hbf hbg hmiddle
  omega

/-- Descend the finite compressor data to an honest functor between the
quotient cluster groupoids. -/
noncomputable def toFunctorData :
    GroupoidPresentation.FunctorData P.presentation Q.presentation where
  obj := D.obj
  map := D.map
  map_respects := fun h ↦ D.map_respects h
  map_one := D.map_one
  map_comp := D.map_comp

/-- The compressor functor obtained from the quantitative finite bridge data
is faithful. -/
noncomputable def faithful : D.toFunctorData.toFunctor.Faithful :=
  D.toFunctorData.faithful (fun h ↦ D.map_reflects h)

end PartialClusterBridgeData
end NonsoficGroupsExist
