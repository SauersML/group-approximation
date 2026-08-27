import GroupApproximation.Higman.OmegaFillFatCompletion

/-!
# The `ωₘ` residue, moved into a finitely presented group

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
one clause of the benign calculus this repository did not have --- `comap`
was available only in the form that asks for a finitely presented overgroup of
the *source* (`Higman.BenignTF.comap`).

So the residue can be stated about any group whatever, and in particular about
a finitely presented one.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  The missing clause of the calculus -/

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
    (heq : S.comap θ = H) (h : BenignTF S) : BenignTF H :=
  heq ▸ BenignTF.comapEmb θ hθ h

namespace Omega

open GroupApproximation.Higman.Seq

/-! ## 2.  The residue, relocated -/

/-- **Input: the link is cut out of a benign subgroup of some group.**  No
condition is placed on the ambient group, which is the point: the construction
that discharges this will choose a finitely presented one, so that the
stable-hull induction on the window width becomes available.

**Nothing inhabits this structure.** -/
structure LinkPreimage : Prop where
  /-- For every window width, an injection out of the slim first stage and a
  benign subgroup downstream whose full preimage is the link. -/
  preimage : ∀ m : ℕ, ∃ (N : Type) (_ : Group N) (θ : Cent3 (rowOut m) →* N)
    (S : Subgroup N), Function.Injective θ ∧ BenignTF S ∧
      S.comap θ = slimLink m

/-- **The relocated residue is the link residue.** -/
theorem benignTF_slimLink_of_linkPreimage (h : LinkPreimage) (m : ℕ) :
    BenignTF (slimLink m) := by
  obtain ⟨N, _, θ, S, hθ, hS, heq⟩ := h.preimage m
  exact benignTF_of_comap_eq θ hθ heq hS

/-- **Higman's `ωₘ` closure, from the slim descent and the relocated
residue.** -/
theorem omegaInput_of_linkPreimage (hd : SlimDescent) (h : LinkPreimage) :
    OmegaInput :=
  omegaInput_of_slimLinkBenign hd (benignTF_slimLink_of_linkPreimage h)

end Omega
end Higman
end GroupApproximation
