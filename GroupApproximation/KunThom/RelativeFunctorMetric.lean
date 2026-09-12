import GroupApproximation.KunThom.ComponentCountingRelativeFunctorPresentation
import GroupApproximation.KunThom.CentralizerNormalizationClusterSystem
import GroupApproximation.Matching.FinitePartialClusterGroupoid
import GroupApproximation.Matching.PartialBijectionSandwich

/-!
# Cluster metrics on groupoid presentations

Kun and Thom (arXiv:2608.06222, Lemma 4.3) define the relative cluster functor
on representatives.  An allowed partial bijection is transported through the
bridges at its source and target and then improved.  Every check that the result
is a functor is a count closed by the distance gap of the target clusters.  This
file isolates what those counts need from a presentation.  The functor can then
be assembled on any cluster groupoid, whether its radius is one number or depends
on the pair of objects.

* `GroupoidPresentation.ClusterMetric`: the representatives are partial
  bijections between finite models, and every pair of objects carries a radius.
  Related representatives are closer than the radius of their pair, and
  representatives closer than eight radii are related.  The unit is the identity,
  composites are close to the composed representatives at the radius of the outer
  pair, and every representative has missing mass below the radius.
* `FinitePartialClusterData.clusterMetric`: constant radius.
* `ScaledFinitePartialClusterData.clusterMetric` and
  `ScaledPartialClusterSystem.clusterMetric`: the pair radius
  `2 * min (scale X) (scale Y)` of the scaled cluster groupoid.
* `twoSidedDisagreement_transport_le`, `twoSidedDisagreement_transport_refl_le`,
  `twoSidedDisagreement_transport_comp_le` and
  `twoSidedDisagreement_transport_reflect_le`: the four triangle chains behind
  well-definedness, identities, composition and faithfulness of transport.
-/

namespace GroupApproximation

universe u v

namespace GroupoidPresentation

/-- A groupoid presentation whose representatives are partial bijections between
finite models, with the distance facts used by the relative cluster functor.  The
radius used for representatives from `X` to `Y` is `radius X Y`. -/
structure ClusterMetric {I : Type u} (P : GroupoidPresentation.{u, v} I) where
  /-- The finite model of an object. -/
  model : I → FiniteModel
  /-- The partial bijection of a representative. -/
  val : ∀ {X Y : I}, P.Rep X Y → FinitePartialBijection (model X) (model Y)
  /-- The cluster radius of a pair of objects. -/
  radius : I → I → ℕ
  lt_of_rel : ∀ {X Y : I} {f g : P.Rep X Y}, P.rel X Y f g →
    (val f).twoSidedDisagreement (val g) < radius X Y
  rel_of_lt : ∀ {X Y : I} {f g : P.Rep X Y},
    (val f).twoSidedDisagreement (val g) < 8 * radius X Y → P.rel X Y f g
  val_one : ∀ X : I, val (P.one X) = FinitePartialBijection.refl (model X)
  comp_close : ∀ {X Y Z : I} (f : P.Rep X Y) (g : P.Rep Y Z),
    (val (P.comp f g)).twoSidedDisagreement ((val f).trans (val g)) < radius X Z
  self_small : ∀ {X Y : I} (f : P.Rep X Y),
    (val f).sourceDefect + (val f).targetDefect < radius X Y

end GroupoidPresentation

namespace FinitePartialClusterData

/-- The cluster groupoid of `FinitePartialClusterData` is a cluster metric with
constant radius. -/
noncomputable def clusterMetric {I : Type u} [Fintype I] (D : FinitePartialClusterData I) :
    D.presentation.ClusterMetric where
  model := D.model
  val {X Y} (f : D.Rep X Y) := f.1
  radius _ _ := D.radius
  lt_of_rel := by
    intro _ _ _ _ h
    exact h
  rel_of_lt := by
    intro _ _ f g h
    exact D.near_of_lt_eight (f := f) (g := g) h
  val_one _ := rfl
  comp_close {X Y Z} (f : D.Rep X Y) (g : D.Rep Y Z) := D.improve_close f.1 f.2 g.1 g.2
  self_small {X Y} (f : D.Rep X Y) := D.self_small f.1 f.2

end FinitePartialClusterData

namespace ScaledFinitePartialClusterData

/-- The cluster groupoid of `ScaledFinitePartialClusterData` is a cluster metric at
its pair radius. -/
noncomputable def clusterMetric {I : Type u} [Fintype I]
    (D : ScaledFinitePartialClusterData I) : D.presentation.ClusterMetric where
  model := D.model
  val {X Y} (f : D.Rep X Y) := f.1
  radius := D.radius
  lt_of_rel := by
    intro _ _ _ _ h
    exact h
  rel_of_lt := by
    intro _ _ f g h
    exact D.near_of_lt_eight (f := f) (g := g) h
  val_one _ := rfl
  comp_close {X Y Z} (f : D.Rep X Y) (g : D.Rep Y Z) := D.improve_close f.1 f.2 g.1 g.2
  self_small {X Y} (f : D.Rep X Y) := D.self_small f.1 f.2

theorem clusterMetric_radius {I : Type u} [Fintype I] (D : ScaledFinitePartialClusterData I)
    (X Y : I) : D.clusterMetric.radius X Y = D.radius X Y :=
  rfl

theorem clusterMetric_val {I : Type u} [Fintype I] (D : ScaledFinitePartialClusterData I)
    {X Y : I} (f : D.Rep X Y) : D.clusterMetric.val (X := X) (Y := Y) f = f.1 :=
  rfl

end ScaledFinitePartialClusterData

namespace ScaledPartialClusterSystem

/-- The cluster groupoid of a scaled partial cluster system is a cluster metric at
the pair radius `2 * min (scale X) (scale Y)`. -/
noncomputable def clusterMetric {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) :
    D.presentation.ClusterMetric :=
  D.clusterData.clusterMetric

theorem clusterMetric_radius {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) (X Y : I) :
    D.clusterMetric.radius X Y = 2 * min (D.scale X) (D.scale Y) :=
  rfl

theorem clusterMetric_val {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {X Y : I}
    (f : D.clusterData.Rep X Y) : D.clusterMetric.val (X := X) (Y := Y) f = f.1 :=
  rfl

end ScaledPartialClusterSystem

namespace FinitePartialBijection

variable {X X' Y Y' Z Z' : FiniteModel}

/-- **Transport respects nearness.**  Two arrows `r` and `s` close to the
transports of `f` and `g` through the same bridges are at most as far apart as
their distances to the transports, the missing masses of the bridges, and the
distance of `f` and `g`. -/
theorem twoSidedDisagreement_transport_le
    (u : FinitePartialBijection X X') (v : FinitePartialBijection Y Y')
    (f g : FinitePartialBijection X Y) (r s : FinitePartialBijection X' Y') :
    r.twoSidedDisagreement s ≤
      r.twoSidedDisagreement (sandwich u v f) + (u.sourceDefect + u.targetDefect) +
        f.twoSidedDisagreement g + (v.sourceDefect + v.targetDefect) +
          s.twoSidedDisagreement (sandwich u v g) := by
  have hsand := twoSidedDisagreement_sandwich_le u v f g
  have htri₁ := twoSidedDisagreement_le r (sandwich u v f) s
  have htri₂ := twoSidedDisagreement_le (sandwich u v f) (sandwich u v g) s
  have hcomm := twoSidedDisagreement_comm (sandwich u v g) s
  omega

/-- **Transport of an identity.**  An arrow close to the transport of the identity
is at most its distance to the transport plus twice the missing target mass of
the bridge away from the identity. -/
theorem twoSidedDisagreement_transport_refl_le
    (u : FinitePartialBijection X X') (r : FinitePartialBijection X' X') :
    r.twoSidedDisagreement (refl X') ≤
      r.twoSidedDisagreement (sandwich u u (refl X)) + 2 * u.targetDefect := by
  have hid := twoSidedDisagreement_sandwich_refl u
  have htri := twoSidedDisagreement_le r (sandwich u u (refl X)) (refl X')
  omega

/-- **Transport of a composite.**  Let `h` be close to `f.trans g`, let `r` be
close to the transport of `h`, let `a` and `b` be close to the transports of `f`
and `g`, and let `c` be close to `a.trans b`.  Then `r` and `c` are close, with
an explicit budget. -/
theorem twoSidedDisagreement_transport_comp_le
    (u : FinitePartialBijection X X') (v : FinitePartialBijection Y Y')
    (w : FinitePartialBijection Z Z')
    (f : FinitePartialBijection X Y) (g : FinitePartialBijection Y Z)
    (h : FinitePartialBijection X Z)
    (r : FinitePartialBijection X' Z') (a : FinitePartialBijection X' Y')
    (b : FinitePartialBijection Y' Z') (c : FinitePartialBijection X' Z') :
    r.twoSidedDisagreement c ≤
      r.twoSidedDisagreement (sandwich u w h) +
        ((u.sourceDefect + u.targetDefect) + h.twoSidedDisagreement (f.trans g) +
          (w.sourceDefect + w.targetDefect)) +
        ((u.sourceDefect + u.targetDefect) + (f.sourceDefect + f.targetDefect) +
          2 * v.sourceDefect + (g.sourceDefect + g.targetDefect) +
            (w.sourceDefect + w.targetDefect)) +
        (a.twoSidedDisagreement (sandwich u v f) +
          b.twoSidedDisagreement (sandwich v w g)) +
        c.twoSidedDisagreement (a.trans b) := by
  have h₁ := twoSidedDisagreement_le r (sandwich u w h) c
  have h₂ := twoSidedDisagreement_le (sandwich u w h) (sandwich u w (f.trans g)) c
  have h₃ := twoSidedDisagreement_sandwich_le u w h (f.trans g)
  have h₄ := twoSidedDisagreement_le (sandwich u w (f.trans g))
    ((sandwich u v f).trans (sandwich v w g)) c
  have h₅ := twoSidedDisagreement_sandwich_trans_le u v w f g
  have h₆ := twoSidedDisagreement_le ((sandwich u v f).trans (sandwich v w g))
    (a.trans b) c
  have h₇ := twoSidedDisagreement_trans_le (sandwich u v f) a (sandwich v w g) b
  have h₈ := twoSidedDisagreement_comm (sandwich u v f) a
  have h₉ := twoSidedDisagreement_comm (sandwich v w g) b
  have h₁₀ := twoSidedDisagreement_comm (a.trans b) c
  omega

/-- **Transport reflects nearness.**  If `r` and `s` are close to the transports
of `f` and `g`, then `f` and `g` are close.  The budget consists of the missing
masses of the bridges, the self-defects of `f` and `g`, and the three distances
among `r`, `s` and the transports. -/
theorem twoSidedDisagreement_transport_reflect_le
    (u : FinitePartialBijection X X') (v : FinitePartialBijection Y Y')
    (f g : FinitePartialBijection X Y) (r s : FinitePartialBijection X' Y') :
    f.twoSidedDisagreement g ≤
      (2 * u.sourceDefect + (f.sourceDefect + f.targetDefect) + 2 * v.sourceDefect) +
        ((u.sourceDefect + u.targetDefect) +
          (r.twoSidedDisagreement (sandwich u v f) + r.twoSidedDisagreement s +
            s.twoSidedDisagreement (sandwich u v g)) +
          (v.sourceDefect + v.targetDefect)) +
        (2 * u.sourceDefect + (g.sourceDefect + g.targetDefect) + 2 * v.sourceDefect) := by
  have hf := twoSidedDisagreement_sandwich_roundtrip_le u v f
  have hg := twoSidedDisagreement_sandwich_roundtrip_le u v g
  have hmid := twoSidedDisagreement_sandwich_le u.symm v.symm (sandwich u v f)
    (sandwich u v g)
  simp only [sourceDefect_symm, targetDefect_symm] at hmid
  have hsf := twoSidedDisagreement_le (sandwich u v f) r (sandwich u v g)
  have hrs := twoSidedDisagreement_le r s (sandwich u v g)
  have hcf := twoSidedDisagreement_comm (sandwich u v f) r
  have htri₁ := twoSidedDisagreement_le f (sandwich u.symm v.symm (sandwich u v f)) g
  have htri₂ := twoSidedDisagreement_le (sandwich u.symm v.symm (sandwich u v f))
    (sandwich u.symm v.symm (sandwich u v g)) g
  have hcomm := twoSidedDisagreement_comm f (sandwich u.symm v.symm (sandwich u v f))
  omega

end FinitePartialBijection

end GroupApproximation
