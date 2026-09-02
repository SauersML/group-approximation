import GroupApproximation.GGT.RelHypOsin24ClassificationBridge

/-!
# Finite bounded-penetration slices

Osin's proof of the linear power estimate uses the bounded-penetration part of
the relative geometry.  In the Memoirs source this is the finite relative
metric supplied by the isolated-component lemma (Lemma `Omega` in the source
file, used in the proof of Theorem `10`, the published Theorem 1.10).  The
elementary-subgroups paper is arXiv:math/0404118 (not math/0404041, which is a
probability paper); its Lemma `Q1` is the fellow-travelling estimate and Lemma
`Q2` is the resulting finite double-coset control.

The landed API contains the exact local-finiteness clause of a hyperbolically
embedded labelled family.  This file records the finite slice of Osin's
double-coset conclusion that follows from that clause: if `K` is finite, then
the part of `K h H_λ` whose right-hand peripheral factor has bounded relative
metric is finite.  The full source step, which produces a *fixed* finite `K`
from a bounded relative-length family of powers, is not asserted here.  The
slice is strictly smaller than that production step and is the finite-set
input consumed by the power-pigeonhole module.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

universe u v

/-! ## The finite slice supplied by local finiteness -/

/-- **Bounded-penetration finite slice.**  For a hyperbolically embedded
labelled family, a finite left set `K`, a fixed element `h`, and a bounded
`d̂_λ`-ball on the right, the corresponding part of the double coset
`K h H_λ` is finite.  This is the set-theoretic finite core of Osin's
bounded-penetration argument (Memoirs Lemma `Omega`, and arXiv:math/0404118
Lemma `Q2`). -/
def RelativeBoundedPenetrationSliceStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded →
      ∀ (lam : I) (n : ℕ) (K : Set G) (h : G), K.Finite →
        (Set.image2 (fun k z : G => k * h * z) K (D.relBall lam n)).Finite

/-- Local finiteness is exactly what is needed for the finite slice. -/
theorem relativeBoundedPenetrationSlice_proved :
    RelativeBoundedPenetrationSliceStatement.{u, v} := by
  intro G instG I D _hbase hemb lam n K h hK
  letI : Group G := instG
  exact Set.Finite.image2 (fun k z : G => k * h * z) hK
    (hemb.locallyFinite lam n)

/-- A conjugated bounded peripheral ball is finite.  This is the form used
when a bounded-penetration diagram is based at a conjugate of the identity. -/
theorem finite_conjugated_relBall_of_isHyperbolicallyEmbedded
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I)
    (hemb : D.IsHyperbolicallyEmbedded) (lam : I) (n : ℕ) (c : G) :
    (Set.image (fun z : G => c * z * c⁻¹) (D.relBall lam n)).Finite := by
  exact (hemb.locallyFinite lam n).image (fun z : G => c * z * c⁻¹)

/-- The one-point left slice is finite, so a fixed double-coset witness has
only finitely many possible bounded-penetration values. -/
theorem finite_fixed_doubleCoset_slice_of_isHyperbolicallyEmbedded
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I)
    (hemb : D.IsHyperbolicallyEmbedded) (lam : I) (n : ℕ)
    (k h : G) :
    (Set.image (fun z : G => k * h * z) (D.relBall lam n)).Finite := by
  have hK : ({k} : Set G).Finite := Set.finite_singleton k
  have hslice :
      (Set.image2 (fun a z : G => a * h * z) ({k} : Set G)
        (D.relBall lam n)).Finite :=
    Set.Finite.image2 (fun a z : G => a * h * z) hK
      (hemb.locallyFinite lam n)
  have himage :
      Set.image2 (fun a z : G => a * h * z) ({k} : Set G)
        (D.relBall lam n) =
        Set.image (fun z : G => k * h * z) (D.relBall lam n) := by
    ext y
    constructor
    · rintro ⟨a, ha, z, hz, rfl⟩
      have hak : a = k := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨k, Set.mem_singleton k, z, hz, rfl⟩
  rw [← himage]
  exact hslice

/-- Model test: over the one-point group every bounded-penetration slice is
finite, independently of the chosen index type and relative generating set. -/
theorem relativeBoundedPenetrationSlice_trivialModel
    {I : Type v} (D : RelGenSet PUnit I) (hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (lam : I) (n : ℕ)
    (K : Set PUnit) (h : PUnit) (hK : K.Finite) :
    (Set.image2 (fun k z : PUnit => k * h * z) K (D.relBall lam n)).Finite := by
  exact relativeBoundedPenetrationSlice_proved PUnit inferInstance I D hbase
    hemb lam n K h hK

end RelHyp
end GGT
end GroupApproximation
