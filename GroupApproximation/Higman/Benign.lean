import GroupApproximation.Algebra.ProductFinitePresentation

/-!
# Benign subgroups

Higman's embedding theorem is organized around one notion.  A subgroup `H` of
a group `G` is **benign** when it is cut out of `G` by a finitely generated
subgroup of a *finitely presented* overgroup: there are a finitely presented
`K`, an embedding `e : G ↪ K` and a finitely generated `L ≤ K` with

    H = e⁻¹(L).

The point of the definition is that it is a *finiteness* condition on `H`
which does not require `H` itself to be finitely generated, and which is
closed under a surprising number of operations.  Higman's theorem is then two
halves:

* every recursively enumerable subgroup of a finitely generated free group is
  benign (the machine half, `Higman.ReSubgroup`);
* if `N ⊴ F` is benign then `F ⧸ N` embeds in a finitely presented group
  (the *rope trick*, `Higman.RopeTrick`).

This file is the definition and the constructions that need no normal-form
theorem: the ones that come from direct products.  Everything here is
elementary and unconditional.

## Contents

* `BenignWitness` --- the data, bundled the way `BooneGroup.Stage` bundles a
  stage of an HNN tower, because the finite presentation and the group
  structure of `K` have to travel with `K`.
* `Benign` --- its `Prop` form.
* `BenignWitness.ofFG` --- a finitely generated subgroup of a finitely
  presented group is benign.  Take `K = G`.
* `BenignWitness.inf` --- benign subgroups are closed under intersection.
  This is the one closure property that is *cheap*: put the two overgroups
  side by side in a direct product and embed `G` diagonally, and the two
  finitely generated subgroups become one, `L₁ × L₂`.  No normal form theorem
  is used anywhere.
* `BenignWitness.ker` --- the kernel of a homomorphism from `G` to a finitely
  presented group is benign, again by a direct product: `L` is the *graph* of
  the homomorphism, which is finitely generated because `G` is.  This is the
  easy half of Higman's characterization, and it is the reason the hard half
  cannot be dodged: it says exactly that a subgroup is benign whenever the
  quotient by it is already known to embed in a finitely presented group.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.ProductFinitePresentation

variable {G : Type} [Group G]

/-! ## 1.  Finite generation toolkit -/

/-- The image of a finitely generated subgroup is finitely generated. -/
theorem fg_map {H : Type} [Group H] {A : Subgroup G} (hA : A.FG) (f : G →* H) :
    (A.map f).FG := by
  obtain ⟨X, hX, hXfin⟩ := (Subgroup.fg_iff A).mp hA
  refine (Subgroup.fg_iff _).mpr ⟨f '' X, ?_, hXfin.image _⟩
  rw [← hX, MonoidHom.map_closure]

/-- A join of two finitely generated subgroups is finitely generated. -/
theorem fg_sup {A B : Subgroup G} (hA : A.FG) (hB : B.FG) : (A ⊔ B).FG := by
  obtain ⟨X, hX, hXfin⟩ := (Subgroup.fg_iff A).mp hA
  obtain ⟨Y, hY, hYfin⟩ := (Subgroup.fg_iff B).mp hB
  refine (Subgroup.fg_iff _).mpr ⟨X ∪ Y, ?_, hXfin.union hYfin⟩
  rw [Subgroup.closure_union, hX, hY]

/-- The whole group is finitely generated as a subgroup of itself when the
group is finitely generated. -/
theorem fg_top [Group.FG G] : (⊤ : Subgroup G).FG := by
  obtain ⟨X, hX, hXfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  exact (Subgroup.fg_iff _).mpr ⟨X, hX, hXfin⟩

/-- The trivial subgroup is finitely generated. -/
theorem fg_bot : (⊥ : Subgroup G).FG := by
  refine (Subgroup.fg_iff _).mpr ⟨∅, ?_, Set.finite_empty⟩
  simp

/-- The range of a homomorphism out of a finitely generated group is finitely
generated. -/
theorem fg_range {H : Type} [Group H] [Group.FG G] (f : G →* H) : f.range.FG := by
  rw [MonoidHom.range_eq_map]
  exact fg_map fg_top f

/-- A product of two finitely generated subgroups is finitely generated.

`Subgroup.prod L₁ L₂` is the join of the two one-sided images, and both
`fg_map` and `fg_sup` are available. -/
theorem fg_prod {H : Type} [Group H] {A : Subgroup G} {B : Subgroup H}
    (hA : A.FG) (hB : B.FG) : (A.prod B).FG := by
  have hsplit : A.prod B = (A.map (MonoidHom.inl G H)) ⊔ (B.map (MonoidHom.inr G H)) := by
    refine le_antisymm ?_ ?_
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hx, hy⟩ := Subgroup.mem_prod.mp hxy
      have hx' : ((x, 1) : G × H) ∈ (A.map (MonoidHom.inl G H)) ⊔
          (B.map (MonoidHom.inr G H)) :=
        Subgroup.mem_sup_left ⟨x, hx, rfl⟩
      have hy' : ((1, y) : G × H) ∈ (A.map (MonoidHom.inl G H)) ⊔
          (B.map (MonoidHom.inr G H)) :=
        Subgroup.mem_sup_right ⟨y, hy, rfl⟩
      have hmul := mul_mem hx' hy'
      have : ((x, 1) : G × H) * ((1, y) : G × H) = (x, y) := by
        refine Prod.ext ?_ ?_
        · simp
        · simp
      rwa [this] at hmul
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hy⟩
  rw [hsplit]
  exact fg_sup (fg_map hA _) (fg_map hB _)

/-! ## 2.  The definition -/

/-- **Higman's benign subgroup, with its witness.**  A finitely presented
overgroup `K` of `G` and a finitely generated `L ≤ K` cutting `H` out of `G`.

The group structure and the finite presentation of `K` are fields rather than
instance arguments for the same reason `BooneGroup.Stage` bundles them: the
witnesses are *constructed*, one from another, and each construction picks a
new carrier type. -/
structure BenignWitness (H : Subgroup G) where
  /-- The finitely presented overgroup. -/
  K : Type
  /-- Its group structure. -/
  [group : Group K]
  /-- It is finitely presented; this is the whole content of the notion. -/
  [fp : Group.IsFinitelyPresented K]
  /-- `G` sits inside it. -/
  emb : G →* K
  /-- ... as a subgroup. -/
  emb_injective : Function.Injective emb
  /-- The finitely generated subgroup that cuts `H` out. -/
  L : Subgroup K
  /-- ... which is finitely generated; the other half of the content. -/
  L_fg : L.FG
  /-- ... and cuts out exactly `H`. -/
  comap_eq : L.comap emb = H

attribute [instance] BenignWitness.group BenignWitness.fp

/-- `H` is benign: some witness exists. -/
def Benign (H : Subgroup G) : Prop := Nonempty (BenignWitness H)

theorem Benign.mk' {H : Subgroup G} (w : BenignWitness H) : Benign H := ⟨w⟩

/-! ## 3.  What direct products give -/

/-- **A finitely generated subgroup of a finitely presented group is
benign.**  Take `K = G` and `L = H`; there is nothing to prove. -/
def BenignWitness.ofFG [Group.IsFinitelyPresented G] {H : Subgroup G} (hH : H.FG) :
    BenignWitness H where
  K := G
  emb := MonoidHom.id G
  emb_injective := fun _ _ h => h
  L := H
  L_fg := hH
  comap_eq := by
    refine Subgroup.ext fun g => ?_
    exact Iff.rfl

theorem benign_of_fg [Group.IsFinitelyPresented G] {H : Subgroup G} (hH : H.FG) :
    Benign H :=
  ⟨BenignWitness.ofFG hH⟩

/-- The trivial subgroup is benign. -/
theorem benign_bot [Group.IsFinitelyPresented G] : Benign (⊥ : Subgroup G) :=
  benign_of_fg fg_bot

/-- The whole group is benign. -/
theorem benign_top [Group.IsFinitelyPresented G] : Benign (⊤ : Subgroup G) := by
  letI : Group.FG G := fg_of_isFinitelyPresented G
  exact benign_of_fg fg_top

/-- **Benign subgroups are closed under intersection.**

The construction is the diagonal: put the two witnesses side by side in
`K₁ × K₂`, embed `G` by `g ↦ (e₁ g, e₂ g)`, and take `L₁ × L₂`, which is
finitely generated because both factors are.  An element of `G` lands in
`L₁ × L₂` exactly when it lands in `L₁` and in `L₂`, which is exactly
`H₁ ⊓ H₂`.

No normal form theorem is used.  This is the only closure property of benign
subgroups with a proof this short, and it is why the development is organized
to use intersections wherever it can. -/
def BenignWitness.inf {H₁ H₂ : Subgroup G} (w₁ : BenignWitness H₁)
    (w₂ : BenignWitness H₂) : BenignWitness (H₁ ⊓ H₂) where
  K := w₁.K × w₂.K
  emb := (w₁.emb).prod (w₂.emb)
  emb_injective := by
    intro x y hxy
    exact w₁.emb_injective (congrArg Prod.fst hxy)
  L := (w₁.L).prod (w₂.L)
  L_fg := fg_prod w₁.L_fg w₂.L_fg
  comap_eq := by
    have h₁ := w₁.comap_eq
    have h₂ := w₂.comap_eq
    refine Subgroup.ext fun g => ?_
    constructor
    · intro hg
      have hg' : ((w₁.emb g, w₂.emb g) : w₁.K × w₂.K) ∈ (w₁.L).prod (w₂.L) :=
        Subgroup.mem_comap.mp hg
      obtain ⟨hgl₁, hgl₂⟩ := Subgroup.mem_prod.mp hg'
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← h₁]
        exact Subgroup.mem_comap.mpr hgl₁
      · rw [← h₂]
        exact Subgroup.mem_comap.mpr hgl₂
    · intro hg
      obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.mp hg
      rw [← h₁] at hg₁
      rw [← h₂] at hg₂
      refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨?_, ?_⟩)
      · exact Subgroup.mem_comap.mp hg₁
      · exact Subgroup.mem_comap.mp hg₂

theorem Benign.inf {H₁ H₂ : Subgroup G} (h₁ : Benign H₁) (h₂ : Benign H₂) :
    Benign (H₁ ⊓ H₂) := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  exact ⟨w₁.inf w₂⟩

/-- **The kernel of a map to a finitely presented group is benign.**

`K = G × B`, `G` embedded as `g ↦ (g, 1)`, and `L` the graph
`{(g, ψ g) : g ∈ G}`, which is finitely generated because it is the range of
a homomorphism out of the finitely generated group `G`.  An element `(g, 1)`
lies on the graph exactly when `ψ g = 1`.

This is the easy half of Higman's characterization: `N` is benign whenever
`G ⧸ N` is already known to sit inside a finitely presented group.  The hard
half --- that a recursively enumerable `N` is benign with no such prior
knowledge --- is what the machine modules do. -/
def BenignWitness.ker {B : Type} [Group B] [Group.IsFinitelyPresented G]
    [Group.IsFinitelyPresented B] (ψ : G →* B) :
    BenignWitness (MonoidHom.ker ψ) where
  K := G × B
  emb := MonoidHom.inl G B
  emb_injective := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  L := ((MonoidHom.id G).prod ψ).range
  L_fg := by
    letI : Group.FG G := fg_of_isFinitelyPresented G
    exact fg_range _
  comap_eq := by
    refine Subgroup.ext fun g => ?_
    constructor
    · intro hg
      have hg' : ((g, (1 : B)) : G × B) ∈ ((MonoidHom.id G).prod ψ).range :=
        Subgroup.mem_comap.mp hg
      obtain ⟨x, hx⟩ := hg'
      have hx1 : x = g := congrArg Prod.fst hx
      have hx2 : ψ x = 1 := congrArg Prod.snd hx
      rw [hx1] at hx2
      exact MonoidHom.mem_ker.mpr hx2
    · intro hg
      have hg' : ψ g = 1 := MonoidHom.mem_ker.mp hg
      refine Subgroup.mem_comap.mpr ⟨g, ?_⟩
      refine Prod.ext ?_ ?_
      · rfl
      · exact hg'

theorem benign_ker {B : Type} [Group B] [Group.IsFinitelyPresented G]
    [Group.IsFinitelyPresented B] (ψ : G →* B) : Benign (MonoidHom.ker ψ) :=
  ⟨BenignWitness.ker ψ⟩

/-! ## 4.  Transport -/

/-- Benignness travels along an isomorphism of the ambient group. -/
def BenignWitness.congr {G' : Type} [Group G'] {H : Subgroup G}
    (φ : G' ≃* G) (w : BenignWitness H) : BenignWitness (H.comap φ.toMonoidHom) where
  K := w.K
  emb := w.emb.comp φ.toMonoidHom
  emb_injective := w.emb_injective.comp φ.injective
  L := w.L
  L_fg := w.L_fg
  comap_eq := by
    rw [← Subgroup.comap_comap, w.comap_eq]

theorem Benign.congr {G' : Type} [Group G'] {H : Subgroup G} (φ : G' ≃* G)
    (h : Benign H) : Benign (H.comap φ.toMonoidHom) := by
  obtain ⟨w⟩ := h
  exact ⟨w.congr φ⟩

end Higman
end GroupApproximation
