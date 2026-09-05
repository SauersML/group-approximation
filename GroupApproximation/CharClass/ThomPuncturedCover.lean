import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Opens

/-!
# The two-set open cover of a punctured product

Step C of the LIX obstruction needs the vanishing `H^k(N ∖ z; F₂) = 0` for
`k ≥ dim N`, where `N` is a finite product of spheres and complex projective
spaces (`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4 item 3 of lane `cc-thom`).
The induction is Mayer–Vietoris for the cover

```text
(X × Y) ∖ {(x₀, y₀)}  =  ((X ∖ x₀) × Y)  ∪  (X × (Y ∖ y₀)),
    intersection      =   (X ∖ x₀) × (Y ∖ y₀).
```

This file is the point-set half of that statement: the two pieces, their
openness, that they cover the punctured product, what their intersection is, and
homeomorphisms identifying all three with honest products of punctured factors.
It also packages the cover as a pair of `TopologicalSpace.Opens` of the punctured
product, which is the shape in which Mayer–Vietoris consumes a cover
(`mvShortExact` of the vendored tree takes `U V : Opens X` with `U ⊔ V = ⊤`).

Nothing here is about cohomology; nothing here needs a peer lane.

## Main definitions

* `leftPunctured x₀ Y`, `rightPunctured X y₀` — the two pieces, as subsets of
  `X × Y`.
* `leftPuncturedHomeo`, `rightPuncturedHomeo`, `interPuncturedHomeo`,
  `unionPuncturedHomeo` — the four identifications.
* `leftOpens`, `rightOpens` — the same two pieces as opens of the punctured
  product, with `leftOpens_sup_rightOpens : leftOpens ⊔ rightOpens = ⊤`.
-/

namespace GroupApproximation.CharClass

open Set

section Sets

variable {X Y : Type*}

/-- The piece `{(x, y) : x ≠ x₀}` of the punctured product `(X × Y) ∖ {(x₀, y₀)}`. -/
def leftPunctured (x₀ : X) (Y : Type*) : Set (X × Y) :=
  ({x₀}ᶜ : Set X) ×ˢ (univ : Set Y)

/-- The piece `{(x, y) : y ≠ y₀}` of the punctured product `(X × Y) ∖ {(x₀, y₀)}`. -/
def rightPunctured (X : Type*) (y₀ : Y) : Set (X × Y) :=
  (univ : Set X) ×ˢ ({y₀}ᶜ : Set Y)

@[simp]
theorem mem_leftPunctured (x₀ : X) (p : X × Y) :
    p ∈ leftPunctured x₀ Y ↔ p.1 ≠ x₀ := by
  simp [leftPunctured]

@[simp]
theorem mem_rightPunctured (y₀ : Y) (p : X × Y) :
    p ∈ rightPunctured X y₀ ↔ p.2 ≠ y₀ := by
  simp [rightPunctured]

/-- **The two pieces cover the punctured product.** -/
theorem leftPunctured_union_rightPunctured (x₀ : X) (y₀ : Y) :
    leftPunctured x₀ Y ∪ rightPunctured X y₀ = ({(x₀, y₀)}ᶜ : Set (X × Y)) := by
  rw [← singleton_prod_singleton, compl_prod_eq_union]

/-- **The intersection of the two pieces is the product of the punctured factors.** -/
theorem leftPunctured_inter_rightPunctured (x₀ : X) (y₀ : Y) :
    leftPunctured x₀ Y ∩ rightPunctured X y₀
      = ({x₀}ᶜ : Set X) ×ˢ ({y₀}ᶜ : Set Y) := by
  rw [leftPunctured, rightPunctured, prod_inter_prod, inter_univ, univ_inter]

theorem leftPunctured_subset (x₀ : X) (y₀ : Y) :
    leftPunctured x₀ Y ⊆ ({(x₀, y₀)}ᶜ : Set (X × Y)) := by
  rw [← leftPunctured_union_rightPunctured x₀ y₀]
  exact subset_union_left

theorem rightPunctured_subset (x₀ : X) (y₀ : Y) :
    rightPunctured X y₀ ⊆ ({(x₀, y₀)}ᶜ : Set (X × Y)) := by
  rw [← leftPunctured_union_rightPunctured x₀ y₀]
  exact subset_union_right

end Sets

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isOpen_leftPunctured [T1Space X] (x₀ : X) (Y : Type*) [TopologicalSpace Y] :
    IsOpen (leftPunctured x₀ Y) :=
  (isOpen_compl_singleton).prod isOpen_univ

theorem isOpen_rightPunctured [T1Space Y] (X : Type*) [TopologicalSpace X] (y₀ : Y) :
    IsOpen (rightPunctured X y₀) :=
  isOpen_univ.prod (isOpen_compl_singleton)

/-- `{(x, y) : x ≠ x₀} ≃ₜ (X ∖ x₀) × Y`. -/
def leftPuncturedHomeo (x₀ : X) (Y : Type*) [TopologicalSpace Y] :
    ↥(leftPunctured x₀ Y) ≃ₜ ↥({x₀}ᶜ : Set X) × Y :=
  (Homeomorph.Set.prod _ _).trans ((Homeomorph.refl _).prodCongr (Homeomorph.Set.univ Y))

/-- `{(x, y) : y ≠ y₀} ≃ₜ X × (Y ∖ y₀)`. -/
def rightPuncturedHomeo (X : Type*) [TopologicalSpace X] (y₀ : Y) :
    ↥(rightPunctured X y₀) ≃ₜ X × ↥({y₀}ᶜ : Set Y) :=
  (Homeomorph.Set.prod _ _).trans ((Homeomorph.Set.univ X).prodCongr (Homeomorph.refl _))

/-- The intersection of the two pieces is `(X ∖ x₀) × (Y ∖ y₀)`. -/
def interPuncturedHomeo (x₀ : X) (y₀ : Y) :
    ↥(leftPunctured x₀ Y ∩ rightPunctured X y₀)
      ≃ₜ ↥({x₀}ᶜ : Set X) × ↥({y₀}ᶜ : Set Y) :=
  (Homeomorph.setCongr (leftPunctured_inter_rightPunctured x₀ y₀)).trans
    (Homeomorph.Set.prod _ _)

/-- The union of the two pieces is the punctured product. -/
def unionPuncturedHomeo (x₀ : X) (y₀ : Y) :
    ↥(leftPunctured x₀ Y ∪ rightPunctured X y₀)
      ≃ₜ ↥({(x₀, y₀)}ᶜ : Set (X × Y)) :=
  Homeomorph.setCongr (leftPunctured_union_rightPunctured x₀ y₀)

/-- **A subset of a subspace, viewed in the subspace or in the ambient space.**  For
`L ⊆ S`, the preimage of `L` in the subspace `S` is homeomorphic to `L`.  This is the
plumbing that turns the two pieces of the cover into opens *of the punctured product*
while keeping their identification with products of punctured factors. -/
def subtypePreimageHomeo {α : Type*} [TopologicalSpace α] {S L : Set α} (h : L ⊆ S) :
    ↥((Subtype.val : ↥S → α) ⁻¹' L) ≃ₜ ↥L where
  toFun p := ⟨((p : ↥S) : α), p.2⟩
  invFun q := ⟨⟨(q : α), h q.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end Topology

section Opens

open TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The punctured product `(X × Y) ∖ {(x₀, y₀)}`, as a topological space. -/
abbrev puncturedProd (x₀ : X) (y₀ : Y) : Type _ := ↥({(x₀, y₀)}ᶜ : Set (X × Y))

/-- The piece `(X ∖ x₀) × Y` as an open subset of the punctured product. -/
def leftOpens [T1Space X] (x₀ : X) (y₀ : Y) : Opens (puncturedProd x₀ y₀) where
  carrier := (Subtype.val : puncturedProd x₀ y₀ → X × Y) ⁻¹' leftPunctured x₀ Y
  is_open' := (isOpen_leftPunctured x₀ Y).preimage continuous_subtype_val

/-- The piece `X × (Y ∖ y₀)` as an open subset of the punctured product. -/
def rightOpens [T1Space Y] (x₀ : X) (y₀ : Y) : Opens (puncturedProd x₀ y₀) where
  carrier := (Subtype.val : puncturedProd x₀ y₀ → X × Y) ⁻¹' rightPunctured X y₀
  is_open' := (isOpen_rightPunctured X y₀).preimage continuous_subtype_val

/-- **The cover condition, in the form Mayer–Vietoris wants it.** -/
theorem leftOpens_sup_rightOpens [T1Space X] [T1Space Y] (x₀ : X) (y₀ : Y) :
    leftOpens x₀ y₀ ⊔ rightOpens x₀ y₀ = ⊤ := by
  ext p
  simp only [Opens.coe_sup, Opens.coe_top, mem_univ, iff_true, mem_union]
  rcases p with ⟨⟨x, y⟩, hp⟩
  simp only [mem_compl_iff, mem_singleton_iff, Prod.mk.injEq, not_and_or] at hp
  rcases hp with hx | hy
  · exact Or.inl (by simpa [leftOpens] using hx)
  · exact Or.inr (by simpa [rightOpens] using hy)

/-- The intersection of the two opens of the cover, as a set of the punctured product. -/
theorem leftOpens_inf_rightOpens_carrier [T1Space X] [T1Space Y] (x₀ : X) (y₀ : Y) :
    ((leftOpens x₀ y₀ ⊓ rightOpens x₀ y₀ : Opens (puncturedProd x₀ y₀)) : Set _)
      = (Subtype.val : puncturedProd x₀ y₀ → X × Y) ⁻¹'
          (({x₀}ᶜ : Set X) ×ˢ ({y₀}ᶜ : Set Y)) := by
  rw [← leftPunctured_inter_rightPunctured x₀ y₀]
  rfl

/-- The left open of the cover really is `(X ∖ x₀) × Y`. -/
def leftOpensHomeo [T1Space X] (x₀ : X) (y₀ : Y) :
    ↥(leftOpens x₀ y₀) ≃ₜ ↥({x₀}ᶜ : Set X) × Y :=
  (subtypePreimageHomeo (leftPunctured_subset x₀ y₀)).trans (leftPuncturedHomeo x₀ Y)

/-- The right open of the cover really is `X × (Y ∖ y₀)`. -/
def rightOpensHomeo [T1Space Y] (x₀ : X) (y₀ : Y) :
    ↥(rightOpens x₀ y₀) ≃ₜ X × ↥({y₀}ᶜ : Set Y) :=
  (subtypePreimageHomeo (rightPunctured_subset x₀ y₀)).trans (rightPuncturedHomeo X y₀)

/-- The intersection of the two opens of the cover really is `(X ∖ x₀) × (Y ∖ y₀)`. -/
def interOpensHomeo [T1Space X] [T1Space Y] (x₀ : X) (y₀ : Y) :
    ↥(leftOpens x₀ y₀ ⊓ rightOpens x₀ y₀) ≃ₜ ↥({x₀}ᶜ : Set X) × ↥({y₀}ᶜ : Set Y) :=
  (Homeomorph.setCongr (leftOpens_inf_rightOpens_carrier x₀ y₀)).trans
    ((subtypePreimageHomeo (S := ({(x₀, y₀)}ᶜ : Set (X × Y)))
        (L := ({x₀}ᶜ : Set X) ×ˢ ({y₀}ᶜ : Set Y))
        (by
          rw [← leftPunctured_inter_rightPunctured x₀ y₀]
          exact inter_subset_left.trans (leftPunctured_subset x₀ y₀))).trans
      (Homeomorph.Set.prod _ _))

end Opens

end GroupApproximation.CharClass
