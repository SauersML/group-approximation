import GroupApproximation.Higman.Benign
import GroupApproximation.Higman.AmalgamPushout

/-!
# Benignness is monotone in the ambient group

`Higman.Benign` proves the closure properties that come from direct products:
intersections, kernels, preimages (`Higman.BenignClosure`).  The remaining half
of Higman's Lemma 3.3 is the *image* direction, and it is the first one that
needs an amalgamated free product rather than a direct product:

> if `H` is benign in `G` and `θ : G ↪ N` embeds `G` in a finitely presented
> group, then `θ(H)` is benign in `N`.

Direct products cannot give it.  A witness for `H` is a finitely presented `K`
with `G ↪ K` and `L ≤ K` finitely generated; to see `θ(H)` inside `N` we have
to glue `K` and `N` *along* `G`, and the glued group must not create new
coincidences between `N` and `L`.  That is exactly what the amalgam normal
form provides, in the single form
`Monoid.PushoutI.inf_of_range_eq_base_range`: the intersection of the two
factors of an amalgam is the amalgamated subgroup, and nothing more.

`Higman.Amalgam` already supplies the amalgam, its finite presentation
(`isFinitelyPresented_push`) and the injectivity of its structure maps, so the
only new ingredient here is that one intersection identity, read through
`Amalgam.fam`.

## The argument

Work in `P = K *_G N`.  Take the finitely generated subgroup `ι₁(L) ≤ P` and
the embedding `ι₂ : N ↪ P`.  If `x ∈ N` has `ι₂ x ∈ ι₁(L)` then `ι₂ x` lies in
both factors, so `ι₂ x = base y` for some `y ∈ G`.  Then `ι₂ x = ι₂ (θ y)`
gives `x = θ y`, and `ι₁ (emb y) = base y = ι₁ l` gives `emb y = l ∈ L`, so
`y ∈ emb⁻¹(L) = H` and `x ∈ θ(H)`.  The converse is the defining relation of
the amalgam.

Hypotheses: `N` finitely presented and `G` finitely generated, both of which
the amalgam's finite presentation needs and neither of which is a restriction
in Higman's use, where the ambient groups are finitely generated free.
-/

namespace GroupApproximation
namespace Higman

open Monoid

variable {G K₁ K₂ : Type} [Group G] [Group K₁] [Group K₂]

/-! ## 1.  Three facts about the amalgam, spelled at the factors -/

/-- The left structure map, composed with the left embedding, is the base
map.  Mathlib's `of_apply_eq_base` phrased at `Amalgam.fam` so that it can be
rewritten with. -/
theorem Amalgam.of_false_eq_base (e₁ : G →* K₁) (e₂ : G →* K₂) (y : G) :
    PushoutI.of (φ := Amalgam.famHom e₁ e₂) false (e₁ y)
      = PushoutI.base (Amalgam.famHom e₁ e₂) y :=
  PushoutI.of_apply_eq_base _ false y

/-- The same on the right. -/
theorem Amalgam.of_true_eq_base (e₁ : G →* K₁) (e₂ : G →* K₂) (y : G) :
    PushoutI.of (φ := Amalgam.famHom e₁ e₂) true (e₂ y)
      = PushoutI.base (Amalgam.famHom e₁ e₂) y :=
  PushoutI.of_apply_eq_base _ true y

/-- **The intersection of the two factors of an amalgam is the amalgamated
subgroup.**  This is the whole of the normal form theorem that the image half
of Lemma 3.3 uses. -/
theorem Amalgam.inf_range_eq_base_range (e₁ : G →* K₁) (e₂ : G →* K₂)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂) :
    (PushoutI.of (φ := Amalgam.famHom e₁ e₂) false).range ⊓
        (PushoutI.of (φ := Amalgam.famHom e₁ e₂) true).range
      = (PushoutI.base (Amalgam.famHom e₁ e₂)).range :=
  PushoutI.inf_of_range_eq_base_range
    (Amalgam.famHom_injective e₁ e₂ h₁ h₂) Bool.false_ne_true

/-! ## 2.  The image half of Lemma 3.3 -/

variable {N : Type} [Group N]

/-- **Benignness is monotone in the ambient group.**  The witness is the
amalgam of the old witness with the new ambient group, glued along `G`. -/
def BenignWitness.mapEmb [Group.IsFinitelyPresented N] [Group.FG G]
    {H : Subgroup G} (w : BenignWitness H) (θ : G →* N)
    (hθ : Function.Injective θ) : BenignWitness (H.map θ) where
  K := Amalgam.Push w.emb θ
  fp := Amalgam.isFinitelyPresented_push w.emb θ
  emb := PushoutI.of (φ := Amalgam.famHom w.emb θ) true
  emb_injective :=
    Amalgam.of_injective_push w.emb θ w.emb_injective hθ true
  L := w.L.map (PushoutI.of (φ := Amalgam.famHom w.emb θ) false)
  L_fg := fg_map w.L_fg _
  comap_eq := by
    refine Subgroup.ext fun x => ?_
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hlL, hl⟩
      have hmem : (PushoutI.of (φ := Amalgam.famHom w.emb θ) true x) ∈
          (PushoutI.of (φ := Amalgam.famHom w.emb θ) false).range ⊓
            (PushoutI.of (φ := Amalgam.famHom w.emb θ) true).range :=
        Subgroup.mem_inf.2
          ⟨MonoidHom.mem_range.2 ⟨l, hl⟩, MonoidHom.mem_range.2 ⟨x, rfl⟩⟩
      rw [Amalgam.inf_range_eq_base_range w.emb θ w.emb_injective hθ] at hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hmem
      have hxy : θ y = x := by
        apply Amalgam.of_injective_push w.emb θ w.emb_injective hθ true
        rw [Amalgam.of_true_eq_base w.emb θ y]
        exact hy
      have hly : w.emb y = l := by
        apply Amalgam.of_injective_push w.emb θ w.emb_injective hθ false
        calc
          PushoutI.of (φ := Amalgam.famHom w.emb θ) false (w.emb y)
              = PushoutI.base (Amalgam.famHom w.emb θ) y :=
                Amalgam.of_false_eq_base w.emb θ y
          _ = PushoutI.of (φ := Amalgam.famHom w.emb θ) true x := hy
          _ = PushoutI.of (φ := Amalgam.famHom w.emb θ) false l := hl.symm
      refine ⟨y, ?_, hxy⟩
      have hcomap : y ∈ w.L.comap w.emb := by
        rw [Subgroup.mem_comap, hly]
        exact hlL
      rwa [w.comap_eq] at hcomap
    · rintro ⟨y, hyH, rfl⟩
      refine ⟨w.emb y, ?_, ?_⟩
      · have hcomap : y ∈ w.L.comap w.emb := by
          rw [w.comap_eq]
          exact hyH
        exact Subgroup.mem_comap.1 hcomap
      · exact (Amalgam.of_false_eq_base w.emb θ y).trans
          (Amalgam.of_true_eq_base w.emb θ y).symm

/-- **Benignness is monotone in the ambient group**, in `Prop` form. -/
theorem Benign.mapEmb [Group.IsFinitelyPresented N] [Group.FG G]
    {H : Subgroup G} (h : Benign H) (θ : G →* N)
    (hθ : Function.Injective θ) : Benign (H.map θ) := by
  obtain ⟨w⟩ := h
  exact ⟨w.mapEmb θ hθ⟩

end Higman
end GroupApproximation
