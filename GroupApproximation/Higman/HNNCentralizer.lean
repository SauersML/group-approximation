import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Higman.BenignClosure
import Mathlib.GroupTheory.HNNExtension

/-!
# The stable letter that centralizes a subgroup, and what it detects

Every construction in Higman's embedding theorem is assembled from one
device: an HNN extension `K ∗_L t` whose stable letter *centralizes* the
subgroup `L`, that is, the HNN extension of `K` along the identity
isomorphism of `L`.  Its whole purpose is the equation

    G ∩ Gᵗ = G ∩ L                                        (for `G ≤ K`),

which converts the *invisible* subgroup `G ∩ L` --- which may be infinitely
generated, and is the thing a benign witness cuts out --- into an
*intersection of two conjugates of a finitely generated group*, and that is a
shape the next construction can consume.

The proof is Britton's lemma and nothing else: `t⁻¹ g t` is already a reduced
word unless `g ∈ L`, so it can only lie in the base when `g ∈ L`.  Mathlib
supplies Britton's lemma as
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`, and this file
supplies the two-letter reduced word to feed it.

## Contents

* `CentHNN L` --- the HNN extension of `K` in which `t` centralizes `L`.
* `mem_of_conj_mem_range` --- Britton, in the form used everywhere below: if
  `t⁻¹ (of g) t` lies in the image of `K`, then `g ∈ L`.
* `conj_mem_range_iff` --- the same, as an equivalence.
* `map_inf_conj_map` --- the equation `G ∩ Gᵗ = G ∩ L`, at the level of
  subgroups.
* `isFinitelyPresented_centHNN` --- `K ∗_L t` is finitely presented when `K`
  is and `L` is finitely generated, by the repository's own permanence
  theorem `HNNFinitePresentation.isFinitelyPresented_hnnExtension`.
-/

namespace GroupApproximation
namespace Higman

open HNNExtension

variable {K : Type} [Group K] (L : Subgroup K)

/-- **The HNN extension whose stable letter centralizes `L`.** -/
abbrev CentHNN : Type := HNNExtension K L L (MulEquiv.refl L)

/-- Both associated subgroups are `L`, whichever sign of the stable letter is
being looked at. -/
theorem toSubgroup_self (u : ℤˣ) : toSubgroup L L u = L := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp

/-- The stable letter commutes with the elements of `L`. -/
theorem conj_eq_self_of_mem {l : K} (hl : l ∈ L) :
    (t : CentHNN L)⁻¹ * of l * t = of l := by
  have h := equiv_symm_eq_conj (φ := MulEquiv.refl L) (⟨l, hl⟩ : L)
  simpa using h.symm

/-- **Britton's lemma, in the form the whole development uses.**  A conjugate
of an element of the base by the stable letter lies in the base only when the
element lies in the centralized subgroup.

The reduced word is `t⁻¹ · g · t`, whose list is `[(-1, g), (1, 1)]`; the
chain condition on a reduced word demands exactly that `g ∉ L`, so if `g ∉ L`
the word is reduced and nonempty, and Britton's lemma forbids its product
from lying in the image of the base. -/
theorem mem_of_conj_mem_range {g : K}
    (h : (t : CentHNN L)⁻¹ * of g * t ∈ (of : K →* CentHNN L).range) : g ∈ L := by
  by_contra hg
  have hchain : List.IsChain
      (fun a b : ℤˣ × K => a.2 ∈ toSubgroup L L a.1 → a.1 = b.1)
      [((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : K))] := by
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
    intro hmem
    rw [toSubgroup_self L] at hmem
    exact absurd hmem hg
  let w : ReducedWord K L L :=
    { head := 1
      toList := [((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : K))]
      chain := hchain }
  have hprod : w.prod (MulEquiv.refl L) = (t : CentHNN L)⁻¹ * of g * t := by
    show (of (1 : K) : CentHNN L) *
      (([((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : K))].map
        (fun x : ℤˣ × K => (t : CentHNN L) ^ (x.1 : ℤ) * of x.2)).prod)
      = (t : CentHNN L)⁻¹ * of g * t
    simp [mul_assoc]
  have hnil : w.toList = [] := by
    refine ReducedWord.toList_eq_nil_of_mem_of_range (MulEquiv.refl L) w ?_
    rw [hprod]
    exact h
  simp [w] at hnil

/-- The two-sided form. -/
theorem conj_mem_range_iff (g : K) :
    (t : CentHNN L)⁻¹ * of g * t ∈ (of : K →* CentHNN L).range ↔ g ∈ L := by
  constructor
  · exact mem_of_conj_mem_range L
  · intro hg
    rw [conj_eq_self_of_mem L hg]
    exact ⟨g, rfl⟩

/-! ## The subgroup form -/

/-- Conjugation by the stable letter, as an automorphism. -/
noncomputable def conjT : CentHNN L ≃* CentHNN L :=
  MulAut.conj (t : CentHNN L)⁻¹

@[simp] theorem conjT_apply (x : CentHNN L) :
    conjT L x = (t : CentHNN L)⁻¹ * x * (t : CentHNN L)⁻¹⁻¹ := rfl

/-- **`G ∩ Gᵗ = G ∩ L`.**  The equation the whole theory is built on: a
conjugate of `G` by the stable letter meets `G` exactly in the part of `G`
that the centralized subgroup sees.

Only Britton's lemma is used, through `mem_of_conj_mem_range`. -/
theorem map_inf_conj_map (G' : Subgroup K) :
    (G'.map (of : K →* CentHNN L)) ⊓
        ((G'.map (of : K →* CentHNN L)).map (conjT L).toMonoidHom)
      = (G' ⊓ L).map (of : K →* CentHNN L) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨g, hg, rfl⟩ := hx₁
    obtain ⟨y, hy, hyx⟩ := hx₂
    obtain ⟨h, hh, rfl⟩ := hy
    have hmem : (t : CentHNN L)⁻¹ * of h * t ∈ (of : K →* CentHNN L).range := by
      refine ⟨g, ?_⟩
      rw [← hyx]
      simp [conjT]
    have hhL : h ∈ L := mem_of_conj_mem_range L hmem
    have hEq : of h = (of : K →* CentHNN L) g := by
      rw [← hyx]
      simp only [conjT_apply, inv_inv]
      rw [conj_eq_self_of_mem L hhL]
    have hgh : g = h := (of_injective (φ := MulEquiv.refl L)) hEq.symm
    refine ⟨h, ⟨?_, hhL⟩, rfl⟩
    rw [← hgh]
    exact hg
  · rintro _ ⟨g, ⟨hgG, hgL⟩, rfl⟩
    refine ⟨⟨g, hgG, rfl⟩, ?_⟩
    refine ⟨of g, ⟨g, hgG, rfl⟩, ?_⟩
    simp only [conjT_apply, inv_inv]
    exact conj_eq_self_of_mem L hgL

/-! ## Finite presentation -/

/-- `K ∗_L t` is finitely presented when `K` is finitely presented and `L` is
finitely generated.  This is the repository's own permanence theorem, which
Mathlib does not have. -/
theorem isFinitelyPresented_centHNN [Group.IsFinitelyPresented K]
    (hL : L.FG) : Group.IsFinitelyPresented (CentHNN L) := by
  letI : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (MulEquiv.refl L)

/-- The embedding of the base into the extension is injective. -/
theorem of_injective_centHNN :
    Function.Injective (of : K →* CentHNN L) :=
  of_injective (φ := MulEquiv.refl L)

end Higman
end GroupApproximation
