import GroupApproximation.Higman.RopeTorsion
import GroupApproximation.Higman.BenignJoin

/-!
# The benign theory, with torsion-free witnesses

`Higman.RopeTorsion` reduces Chiodo's torsion clause to one demand: that the
benign witness be torsion-free.  This file shows the demand costs nothing in
the part of the theory already proved --- every construction of
`Higman.Benign`, `Higman.BenignClosure` and `Higman.BenignJoin` produces a
torsion-free witness whenever it is given torsion-free ones.

The reason is that all of them are built from direct products and HNN
extensions, and this repository proves both permanence theorems:

* a direct product of torsion-free groups is torsion-free
  (`IsPowerTorsionFree.prod`);
* an HNN extension of a torsion-free group is torsion-free
  (`HNNBritton.isPowerTorsionFree_hnn`).

No amalgam appears in any of them --- which is why the join was built over a
direct product rather than over Mikaelian's `✻`-construction; that choice,
made to shorten the proof, is what keeps the torsion clause free here.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.ProductFinitePresentation

variable {G N : Type} [Group G] [Group N]

/-- A subgroup that is benign with a torsion-free witness. -/
def BenignTF (H : Subgroup G) : Prop := Nonempty (TorsionFreeBenignWitness H)

theorem BenignTF.toBenign {H : Subgroup G} (h : BenignTF H) : Benign H := by
  obtain ⟨u⟩ := h
  exact ⟨u.witness⟩

/-! ## 1.  Finitely generated subgroups -/

/-- A finitely generated subgroup of a finitely presented torsion-free group is
benign with a torsion-free witness: the witness is the group itself. -/
def TorsionFreeBenignWitness.ofFG [Group.IsFinitelyPresented G]
    (hG : IsPowerTorsionFree G) {H : Subgroup G} (hH : H.FG) :
    TorsionFreeBenignWitness H where
  witness := BenignWitness.ofFG hH
  torsionFree := hG

theorem benignTF_of_fg [Group.IsFinitelyPresented G] (hG : IsPowerTorsionFree G)
    {H : Subgroup G} (hH : H.FG) : BenignTF H :=
  ⟨TorsionFreeBenignWitness.ofFG hG hH⟩

/-! ## 2.  Intersections -/

/-- Intersections keep the torsion clause: the witness is a direct product. -/
def TorsionFreeBenignWitness.inf {H₁ H₂ : Subgroup G}
    (u₁ : TorsionFreeBenignWitness H₁) (u₂ : TorsionFreeBenignWitness H₂) :
    TorsionFreeBenignWitness (H₁ ⊓ H₂) where
  witness := (u₁.witness).inf (u₂.witness)
  torsionFree := IsPowerTorsionFree.prod u₁.torsionFree u₂.torsionFree

theorem BenignTF.inf {H₁ H₂ : Subgroup G} (h₁ : BenignTF H₁) (h₂ : BenignTF H₂) :
    BenignTF (H₁ ⊓ H₂) := by
  obtain ⟨u₁⟩ := h₁
  obtain ⟨u₂⟩ := h₂
  exact ⟨u₁.inf u₂⟩

/-! ## 3.  Kernels and preimages -/

/-- Kernels keep the torsion clause. -/
def TorsionFreeBenignWitness.ker {B : Type} [Group B]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented B]
    (hG : IsPowerTorsionFree G) (hB : IsPowerTorsionFree B) (ψ : G →* B) :
    TorsionFreeBenignWitness (MonoidHom.ker ψ) where
  witness := BenignWitness.ker ψ
  torsionFree := IsPowerTorsionFree.prod hG hB

/-- A torsion-free finitely presented overgroup. -/
structure TorsionFreeFPOvergroup (G : Type) [Group G] where
  /-- The overgroup. -/
  K : Type
  /-- Its group structure. -/
  [group : Group K]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented K]
  /-- It is torsion-free. -/
  torsionFree : IsPowerTorsionFree K
  /-- The embedding. -/
  emb : G →* K
  /-- ... which is one. -/
  emb_injective : Function.Injective emb

attribute [instance] TorsionFreeFPOvergroup.group TorsionFreeFPOvergroup.fp

/-- The underlying overgroup. -/
def TorsionFreeFPOvergroup.toFPOvergroup (u : TorsionFreeFPOvergroup G) :
    FPOvergroup G where
  K := u.K
  emb := u.emb
  emb_injective := u.emb_injective

/-- Preimages keep the torsion clause. -/
def TorsionFreeBenignWitness.comap (u : TorsionFreeFPOvergroup G) (φ : G →* N)
    {H : Subgroup N} (v : TorsionFreeBenignWitness H) :
    TorsionFreeBenignWitness (H.comap φ) where
  witness := (v.witness).comap u.toFPOvergroup φ
  torsionFree := IsPowerTorsionFree.prod u.torsionFree v.torsionFree

theorem BenignTF.comap (u : TorsionFreeFPOvergroup G) (φ : G →* N)
    {H : Subgroup N} (h : BenignTF H) : BenignTF (H.comap φ) := by
  obtain ⟨v⟩ := h
  exact ⟨TorsionFreeBenignWitness.comap u φ v⟩

/-! ## 4.  Transport along an isomorphism -/

/-- Transport keeps the torsion clause: the witness does not change. -/
def TorsionFreeBenignWitness.congr {G' : Type} [Group G'] {H : Subgroup G}
    (φ : G' ≃* G) (u : TorsionFreeBenignWitness H) :
    TorsionFreeBenignWitness (H.comap φ.toMonoidHom) where
  witness := (u.witness).congr φ
  torsionFree := u.torsionFree

theorem BenignTF.congr {G' : Type} [Group G'] {H : Subgroup G} (φ : G' ≃* G)
    (h : BenignTF H) : BenignTF (H.comap φ.toMonoidHom) := by
  obtain ⟨u⟩ := h
  exact ⟨u.congr φ⟩

/-! ## 5.  Joins -/

/-- **Joins keep the torsion clause.**  The join witness is two HNN extensions
over a direct product, and both permanence theorems are available. -/
def TorsionFreeBenignWitness.sup [Group.FG G] {A₁ A₂ : Subgroup G}
    (u₁ : TorsionFreeBenignWitness A₁) (u₂ : TorsionFreeBenignWitness A₂) :
    TorsionFreeBenignWitness (A₁ ⊔ A₂) where
  witness := joinWitness u₁.witness u₂.witness
  torsionFree := by
    have hbase : IsPowerTorsionFree (JoinBase u₁.witness u₂.witness) :=
      IsPowerTorsionFree.prod u₁.torsionFree u₂.torsionFree
    have hlevel1 : IsPowerTorsionFree (JoinLevel1 u₁.witness u₂.witness) :=
      HNNBritton.isPowerTorsionFree_hnn
        (MulEquiv.refl (joinM₁ u₁.witness u₂.witness)) hbase
    exact HNNBritton.isPowerTorsionFree_hnn
      (MulEquiv.refl (joinM₂' u₁.witness u₂.witness)) hlevel1

theorem BenignTF.sup [Group.FG G] {A₁ A₂ : Subgroup G} (h₁ : BenignTF A₁)
    (h₂ : BenignTF A₂) : BenignTF (A₁ ⊔ A₂) := by
  obtain ⟨u₁⟩ := h₁
  obtain ⟨u₂⟩ := h₂
  exact ⟨u₁.sup u₂⟩

/-! ## 6.  What this says about the remaining input

`Higman.REBenignTF` asks for a torsion-free benign witness for every
recursively enumerable normal subgroup of a free group of finite rank.  By the
five constructions above, the torsion clause is inherited by every step of
Higman's Section 3.1, and free groups are torsion-free, so a proof of
`Higman.REBenign` that goes through those steps --- and through the concrete
examples of his Section 3.2, whose witnesses are HNN extensions of free
groups --- proves `REBenignTF` with no extra work.  The clause is not an
additional obligation; it is a property of the constructions. -/

end Higman
end GroupApproximation
