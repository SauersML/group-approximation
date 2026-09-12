import GroupApproximation.Higman.OmegaFillFatCompletion

/-!
# Benignness moves to a full preimage

`Higman.OmegaFillFatCompletion` reduces Higman's `ωₘ` closure to benignness of
the slim link `Omega.slimLink m` inside `Cent3 (rowOut m)`.  That group is not
finitely presented --- its first stage centralizes a subgroup of infinite rank
--- so none of the benign calculus's *construction* lemmas can be applied
inside it.  `Higman.BenignTF.stableHull`, which is what an induction on the
window width uses, asks for `[Group.IsFinitelyPresented P] [Group.FG P]`.

They do not have to be applied there.  Benignness is inherited by a **full
preimage** along an injection, and it costs nothing: a witness for the image
is already a witness for the preimage, with the same overgroup and the same
finitely generated cutter.  That is `BenignTF.comapEmb` below, and it is the
one clause of the benign calculus this repository did not have --- `comap` was
available only in the form that asks for a finitely presented overgroup of the
*source* (`Higman.BenignTF.comap`).

So the residue can be moved to any group whatever, and in particular to a
finitely presented one.
-/

namespace GroupApproximation
namespace Higman

/-- **A benign subgroup pulls back along an injection.**  Unlike
`Higman.BenignTF.comap`, this needs no finitely presented overgroup of the
source: the witness for `S` already carries one, so the composite embedding
serves.  What it does need is that the subgroup be the *whole* preimage of
`S`, not merely contained in it. -/
theorem BenignTF.comapEmb {G N : Type} [Group G] [Group N] (θ : G →* N)
    (hθ : Function.Injective θ) {S : Subgroup N} (h : BenignTF S) :
    BenignTF (S.comap θ) := by
  obtain ⟨v⟩ := h
  have hcomap : v.witness.L.comap (v.witness.emb.comp θ) = S.comap θ := by
    rw [← Subgroup.comap_comap, v.witness.comap_eq]
  exact ⟨{ witness :=
             { K := v.witness.K
               emb := v.witness.emb.comp θ
               emb_injective := v.witness.emb_injective.comp hθ
               L := v.witness.L
               L_fg := v.witness.L_fg
               comap_eq := hcomap }
           torsionFree := v.torsionFree }⟩

/-- The same, stated at a subgroup already known to be the preimage. -/
theorem benignTF_of_comap_eq {G N : Type} [Group G] [Group N] (θ : G →* N)
    (hθ : Function.Injective θ) {S : Subgroup N} {H : Subgroup G}
    (heq : S.comap θ = H) (h : BenignTF S) : BenignTF H := by
  rw [← heq]
  exact BenignTF.comapEmb θ hθ h

namespace Omega

open GroupApproximation.Higman.Seq

/-- **The residue, relocated.**  The slim link is benign as soon as it is cut
out of a benign subgroup of some other group by an injection --- and that
group may be finitely presented, where the stable-hull induction on the window
width is available. -/
theorem benignTF_slimLink_of_preimage {m : ℕ} {N : Type} [Group N]
    (θ : Cent3 (rowOut m) →* N) (hθ : Function.Injective θ) {S : Subgroup N}
    (heq : S.comap θ = slimLink m) (hS : BenignTF S) : BenignTF (slimLink m) :=
  benignTF_of_comap_eq θ hθ heq hS

end Omega
end Higman
end GroupApproximation
