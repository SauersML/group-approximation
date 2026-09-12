import GroupApproximation.KunThom.ComponentCountingNormalizationGroupoid
import GroupApproximation.KunThom.CountingEndgameCompletion
import Mathlib.Tactic.Choose

/-!
# Lifting a bisection through the relative cluster functor

In the endgame of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3, §4,
tex lines 1238–1292) the relative functor `F_n : 𝒞_n|_{R_n} → 𝒫_n|_{D_n}` is
faithful and injective on objects.  For a total bisection of the target and a
set of selected source objects, the orbit and isotropy counts force every
selected arrow of the bisection to have a unique preimage.  The preimages form
a partial bisection of the ambient cluster groupoid, which is then completed.

This file states that finite step for abstract finite groupoids.  The relative
functor is any faithful functor `F : C' ⥤ D` injective on objects, and
`J : C' ⥤ C` is any functor injective on objects carrying its source into the
ambient groupoid; for a restricted presentation it is the inclusion.

* `nonempty_hom_of_card_orbit_lt_add`: two objects whose images are connected,
  with the image orbit smaller than the two source orbits together, are
  connected.  This is the claim `Ω₁ = Ω₂`.
* `map_bijective_of_counts`: with the same orbit count and an isotropy index
  below `2`, the functor is bijective on the Hom-set.
* `eqToHom_comp_arrow_comp_eqToHom`: transport of a family of arrows along an
  equality of indices.
* `exists_bisection_extend_of_injOn`: the completion of
  `CountingEndgameCompletion`, with the selected arrows indexed by any type.
* `exists_bisection_lift`: the finite endgame.  Some total bisection of `C`
  has, at every selected object, the image under `J` of the preimage of the
  transported arrow of the given bisection.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory

universe u v u' v' u'' v''

/-- **`Ω₁ = Ω₂`.**  If the images of `X` and `X'` under a functor injective on
objects are connected, and the image orbit of `X` has fewer objects than the
orbits of `X` and `X'` together, then `X` and `X'` are connected. -/
theorem nonempty_hom_of_card_orbit_lt_add {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) {X X' : C}
    (himage : Nonempty (F.obj X ⟶ F.obj X'))
    (hsmall : (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card) :
    Nonempty (X ⟶ X') := by
  by_contra hdisc
  have h := ComponentCountingNormalization.card_orbit_inter_add_le Finset.univ F.obj
    (fun _ _ _ _ hYZ ↦ hobj hYZ) (fun _ _ _ _ hYZ ↦ Nonempty.map (fun g ↦ F.map g) hYZ)
    (Finset.mem_univ X) (Finset.mem_univ X') hdisc himage
  simp only [Finset.inter_univ] at h
  omega

/-- **Hom-set bijection from the counts.**  Let `F` be faithful and injective on
objects.  If the images of `X` and `X'` are connected, the image orbit of `X` has
fewer objects than the orbits of `X` and `X'` together, and the isotropy index
at `X` is below `2`, then `F` is bijective from `X ⟶ X'` onto the image
Hom-set. -/
theorem map_bijective_of_counts {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    [F.Faithful] (hobj : Function.Injective F.obj) {X X' : C}
    [Fintype (X ⟶ X)] [Fintype (X ⟶ X')] [Fintype (F.obj X ⟶ F.obj X)]
    [Fintype (F.obj X ⟶ F.obj X')]
    (himage : Nonempty (F.obj X ⟶ F.obj X'))
    (horbit : (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card)
    (hvertex : Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X)) :
    Function.Bijective (F.map : (X ⟶ X') → (F.obj X ⟶ F.obj X')) :=
  ComponentCountingNormalization.map_bijective_of_isotropy_lt_two_mul F
    (Classical.choice (nonempty_hom_of_card_orbit_lt_add F hobj himage horbit)) hvertex

/-- Transport of a family of arrows indexed by a finite set along an equality of
indices. -/
theorem eqToHom_comp_arrow_comp_eqToHom {C : Type u} [Category.{v} C] {K : Type u''}
    (S : Finset K) (src tgt : K → C) (arrow : ∀ k ∈ S, src k ⟶ tgt k) {k k' : K}
    (h : k' = k) (hk : k ∈ S) (hk' : k' ∈ S) {T : C} (h₁ : src k = src k')
    (h₂ : tgt k' = T) (h₃ : tgt k = T) :
    eqToHom h₁ ≫ arrow k' hk' ≫ eqToHom h₂ = arrow k hk ≫ eqToHom h₃ := by
  subst h
  simp

/-- **Completion of an indexed partial bisection.**  Arrows `src k ⟶ tgt k` for
`k ∈ S`, with `src` and `tgt` injective on `S`, extend to a total bisection whose
arrow at every `src k` is the given arrow, up to the identification of its
target. -/
theorem exists_bisection_extend_of_injOn {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {K : Type u''} (S : Finset K) (src tgt : K → C)
    (hsrc : Set.InjOn src (S : Set K)) (htgt : Set.InjOn tgt (S : Set K))
    (arrow : ∀ k ∈ S, src k ⟶ tgt k) :
    ∃ b : FiniteGroupoid.Bisection C, ∀ k (hk : k ∈ S),
      ∃ e : b.objEquiv (src k) = tgt k, b.hom (src k) ≫ eqToHom e = arrow k hk := by
  have hpick : ∀ Z ∈ S.image src, ∃ k ∈ S, src k = Z := fun Z hZ ↦ Finset.mem_image.mp hZ
  choose pick hpickS hpicksrc using hpick
  obtain ⟨τ, hτ⟩ : ∃ τ : C → C, ∀ Z (hZ : Z ∈ S.image src), τ Z = tgt (pick Z hZ) :=
    ⟨fun Z ↦ if hZ : Z ∈ S.image src then tgt (pick Z hZ) else Z, fun Z hZ ↦ dif_pos hZ⟩
  have hinj : Set.InjOn τ ((S.image src : Finset C) : Set C) := by
    intro Z₁ hZ₁ Z₂ hZ₂ h
    have hZ₁' : Z₁ ∈ S.image src := Finset.mem_coe.mp hZ₁
    have hZ₂' : Z₂ ∈ S.image src := Finset.mem_coe.mp hZ₂
    rw [hτ Z₁ hZ₁', hτ Z₂ hZ₂'] at h
    have hk : pick Z₁ hZ₁' = pick Z₂ hZ₂' :=
      htgt (Finset.mem_coe.mpr (hpickS Z₁ hZ₁')) (Finset.mem_coe.mpr (hpickS Z₂ hZ₂')) h
    exact (hpicksrc Z₁ hZ₁').symm.trans ((congrArg src hk).trans (hpicksrc Z₂ hZ₂'))
  obtain ⟨b, hb⟩ := exists_bisection_extend (S.image src) τ hinj fun Z hZ ↦
    eqToHom (hpicksrc Z hZ).symm ≫ arrow (pick Z hZ) (hpickS Z hZ) ≫ eqToHom (hτ Z hZ).symm
  refine ⟨b, fun k hk ↦ ?_⟩
  have hZ : src k ∈ S.image src := Finset.mem_image_of_mem src hk
  obtain ⟨e₀, he₀⟩ := hb (src k) hZ
  have hpk : pick (src k) hZ = k :=
    hsrc (Finset.mem_coe.mpr (hpickS (src k) hZ)) (Finset.mem_coe.mpr hk) (hpicksrc (src k) hZ)
  have h₃ : tgt k = τ (src k) := by
    rw [hτ (src k) hZ, hpk]
  have htrans := eqToHom_comp_arrow_comp_eqToHom S src tgt arrow hpk hk (hpickS (src k) hZ)
    (hpicksrc (src k) hZ).symm (hτ (src k) hZ).symm h₃
  refine ⟨e₀.trans h₃.symm, ?_⟩
  calc b.hom (src k) ≫ eqToHom (e₀.trans h₃.symm)
      = (b.hom (src k) ≫ eqToHom e₀) ≫ eqToHom h₃.symm := by simp
    _ = (arrow k hk ≫ eqToHom h₃) ≫ eqToHom h₃.symm := by simp only [he₀, htrans]
    _ = arrow k hk := by simp

/-- **The finite endgame.**  Let `F : C' ⥤ D` be faithful and injective on
objects and `J : C' ⥤ C` injective on objects.  Let `a` be a total bisection of
`D`, `S` a finite set of objects of `C'` and `sel` a choice of targets with
`F (sel X) = a (F X)` for `X ∈ S`.  Suppose that at every `X ∈ S` the image
orbit of `X` has fewer objects than the orbits of `X` and `sel X` together, and
the isotropy index of `F` at `X` is below `2`.  Then every transported arrow of
`a` has a preimage `g : X ⟶ sel X`, and some total bisection of `C` has the
arrow `J g` at every `J X`. -/
theorem exists_bisection_lift
    {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {C' : Type u'} [Groupoid.{v'} C'] [Fintype C'] [DecidableEq C']
    [∀ X Y : C', Fintype (X ⟶ Y)]
    {D : Type u''} [Groupoid.{v''} D] [Fintype D] [∀ X Y : D, Fintype (X ⟶ Y)]
    (J : C' ⥤ C) (hJ : Function.Injective J.obj)
    (F : C' ⥤ D) [F.Faithful] (hF : Function.Injective F.obj)
    (a : FiniteGroupoid.Bisection D) (S : Finset C') (sel : C' → C')
    (hsel : ∀ X ∈ S, F.obj (sel X) = a.objEquiv (F.obj X))
    (horbit : ∀ X ∈ S, (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit (sel X)).card)
    (hvertex : ∀ X ∈ S,
      Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X)) :
    ∃ b : FiniteGroupoid.Bisection C, ∀ X (hX : X ∈ S), ∃ g : X ⟶ sel X,
      F.map g = a.hom (F.obj X) ≫ eqToHom (hsel X hX).symm ∧
        ∃ e : b.objEquiv (J.obj X) = J.obj (sel X),
          b.hom (J.obj X) ≫ eqToHom e = J.map g := by
  have hlift : ∀ X (hX : X ∈ S), ∃ g : X ⟶ sel X,
      F.map g = a.hom (F.obj X) ≫ eqToHom (hsel X hX).symm := fun X hX ↦
    (map_bijective_of_counts F hF (X := X) (X' := sel X)
      ⟨a.hom (F.obj X) ≫ eqToHom (hsel X hX).symm⟩ (horbit X hX) (hvertex X hX)).2 _
  choose g hg using hlift
  have htgt : Set.InjOn (fun X ↦ J.obj (sel X)) (S : Set C') := by
    intro X₁ hX₁ X₂ hX₂ h
    have h₁ : sel X₁ = sel X₂ := hJ h
    have h₂ : a.objEquiv (F.obj X₁) = a.objEquiv (F.obj X₂) := by
      rw [← hsel X₁ (Finset.mem_coe.mp hX₁), ← hsel X₂ (Finset.mem_coe.mp hX₂), h₁]
    exact hF (a.objEquiv.injective h₂)
  obtain ⟨b, hb⟩ := exists_bisection_extend_of_injOn S J.obj (fun X ↦ J.obj (sel X))
    (fun _ _ _ _ h ↦ hJ h) htgt fun X hX ↦ J.map (g X hX)
  exact ⟨b, fun X hX ↦ ⟨g X hX, hg X hX, hb X hX⟩⟩

end CountingEndgame
end GroupApproximation
