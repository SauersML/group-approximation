import GroupApproximation.Algebra.PushoutITorsionFree
import GroupApproximation.Higman.BenignAmbient
import GroupApproximation.Higman.BenignTorsionFree
import GroupApproximation.Higman.OperationClosureRho

/-!
# The image half of Higman's Lemma 3.3, with the torsion clause

`Higman.BenignAmbient` proves that benignness is monotone in the ambient group
--- if `H` is benign in `G` and `θ : G ↪ N` embeds `G` in a finitely presented
group, then `θ(H)` is benign in `N` --- by gluing the old witness `K` to the new
ambient group `N` along `G`.  It is the one construction in the benign theory
whose witness is an amalgam rather than a direct product or an HNN extension,
and that is why `Higman.BenignTorsionFree` could not carry the torsion clause
through it: the clause asks that `K ∗_G N` be torsion-free, and

> an amalgamated free product of torsion-free groups is torsion-free

was nowhere in the repository.  It now is, as
`Algebra.PushoutITorsionFree.isPowerTorsionFree_pushoutI_of_nonempty`, proved by
cyclic reduction on `Monoid.PushoutI.NormalWord` exactly as
`Algebra.CoprodICyclicReduction` does for the free product.

So this file is bookkeeping.  `Amalgam.isPowerTorsionFree_push` states the
permanence at the repository's two-element diagram; `BenignTF.mapEmb` is the
image half with the clause; and `Seq.torsionFreeImageClosure` **inhabits
`Seq.TorsionFreeImageClosure`**, the general input that
`Higman.OperationClosureRho`, `Higman.OperationClosureTau` and
`Higman.OperationClosureTheta` were all waiting on and that nothing inhabited.
-/

namespace GroupApproximation
namespace Higman

open Monoid

variable {G K₁ K₂ N : Type} [Group G] [Group K₁] [Group K₂] [Group N]

/-! ## 1.  The amalgam of two torsion-free groups -/

/-- **An amalgamated free product of torsion-free groups is torsion-free**, at
the two-element diagram `Higman.Amalgam` uses.  The base group needs no
hypothesis: it embeds in a factor. -/
theorem Amalgam.isPowerTorsionFree_push (e₁ : G →* K₁) (e₂ : G →* K₂)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (t₁ : IsPowerTorsionFree K₁) (t₂ : IsPowerTorsionFree K₂) :
    IsPowerTorsionFree (Amalgam.Push e₁ e₂) := by
  refine PushoutITorsionFree.isPowerTorsionFree_pushoutI_of_nonempty
    (Amalgam.famHom_injective e₁ e₂ h₁ h₂) ?_
  intro b
  cases b with
  | false => exact t₁
  | true => exact t₂

/-! ## 2.  The image half of Lemma 3.3 keeps the torsion clause -/

/-- **Benignness with a torsion-free witness is monotone in the ambient
group.**  The witness is `Higman.BenignWitness.mapEmb`'s amalgam of the old
witness with the new ambient group, and it is torsion-free because both factors
are. -/
def TorsionFreeBenignWitness.mapEmb [Group.IsFinitelyPresented N] [Group.FG G]
    (hN : IsPowerTorsionFree N) {Hs : Subgroup G} (u : TorsionFreeBenignWitness Hs)
    (θ : G →* N) (hθ : Function.Injective θ) :
    TorsionFreeBenignWitness (Hs.map θ) where
  witness := u.witness.mapEmb θ hθ
  torsionFree :=
    Amalgam.isPowerTorsionFree_push u.witness.emb θ u.witness.emb_injective hθ
      u.torsionFree hN

/-- **Benignness with a torsion-free witness is monotone in the ambient
group**, in `Prop` form. -/
theorem BenignTF.mapEmb [Group.IsFinitelyPresented N] [Group.FG G]
    (hN : IsPowerTorsionFree N) {Hs : Subgroup G} (h : BenignTF Hs) (θ : G →* N)
    (hθ : Function.Injective θ) : BenignTF (Hs.map θ) := by
  obtain ⟨u⟩ := h
  exact ⟨u.mapEmb hN θ hθ⟩

/-! ## 3.  The named input, discharged -/

/-- **`Seq.TorsionFreeImageClosure` holds.**  It said exactly that the image of
a benign subgroup under an embedding into a finitely presented torsion-free
group is benign with a torsion-free witness, and that is `BenignTF.mapEmb`. -/
theorem Seq.torsionFreeImageClosure : Seq.TorsionFreeImageClosure := by
  intro A B _ _ _ _ hB Hs θ hθ hH
  exact BenignTF.mapEmb hB hH θ hθ

end Higman
end GroupApproximation
