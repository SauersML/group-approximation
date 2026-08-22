import GroupApproximation.GroupTheory.HNNBrittonSpelling
import GroupApproximation.Higman.HNNDescent
import GroupApproximation.Algebra.HNNFinitePresentation

/-!
# Subextensions of an HNN extension

Let `Γ = G ∗_φ t` be an HNN extension with associated pair `(A, B, φ)`, and let
`G' ≤ G` be a subgroup with

    A' := G' ⊓ A,   B' := G' ⊓ B,   φ (A') = B' .

Then the subgroup `⟨G', t⟩ ≤ Γ` *is* the HNN extension of `G'` along the
restriction `φ' : A' ≃* B'`: the canonical homomorphism

    HNNExtension G' A' B' φ'  →*  Γ ,     G' ↪ G,  t ↦ t

is injective, and its range is `⟨G', t⟩`.  This is the structural half of
Lemma 2.4 of V. H. Mikaelian, *On embeddings of countable generalized wreath
products into divisible groups* (arXiv:1908.10153); the arithmetic half — that
`⟨G', t⟩ ⊓ G = G'` — is `Higman.HNNDescent.closure_inf_range`, which is cited
here rather than reproved (`range_inf_of_range`).

Nothing of this shape exists in Mathlib, whose `GroupTheory/HNNExtension.lean`
knows the base embedding `HNNExtension.of_injective` but nothing about
sub-extensions.

## Why the hypothesis is *saturation*, not inclusion

The proof is Britton's lemma, and it needs exactly one thing: a syllable of a
word over `G'` that lands in an associated subgroup of `Γ` must already lie in
the corresponding associated subgroup of the small extension.  Written out,

    ι g ∈ A  →  g ∈ A'      and      ι g ∈ B  →  g ∈ B' ,

which for `A' = G' ⊓ A` is a tautology and in general is the statement that
`A'` is the *full* preimage of `A`.  Under it, a Britton-reduced word of
`HNNExtension G' A' B' φ'` maps to a Britton-reduced word of `Γ` with the same
syllable list, so it can be trivial only if it has no syllables at all, and
then injectivity of `ι` finishes.  Nothing about `G' ⊓ A` being finitely
generated, or about `φ` being anything but an isomorphism, is used.

## Contents

* `IsSubextension` — the hypothesis, for an abstract inclusion `ι : H →* G`
  rather than a literal subgroup: injectivity, `φ`-compatibility, and the two
  saturation clauses.  `IsSubextension.memB` shows the `B`-side inclusion
  clause is redundant.
* `IsSubextensionHom` — the characterising property of the canonical map
  (`of h ↦ of (ι h)`, `t ↦ t`), so that every statement below is proved from
  the two equations and not from the shape of `HNNExtension.lift`.
* `canonical`, `isSubextensionHom_canonical` — the map, and that it has that
  property.
* `noPinch_mapList` — the combinatorial heart: pinch-freeness is preserved by
  the map on syllable lists.  This is where saturation is used.
* `injective_of_isSubextensionHom` — **the lemma**: the canonical map is
  injective.
* `range_eq_closure` — its range is `⟨ι '' H, t⟩`.
* `mulEquivRange` — the resulting isomorphism onto `⟨G', t⟩`.
* `restrictEquiv` — for a literal subgroup `Z ≤ G` that is
  `Higman.HNNDescent.Stable`, the restriction `A ⊓ Z ≃* B ⊓ Z` of `φ`,
  expressed with `Subgroup.subgroupOf`.
* `toAmbient_injective`, `range_inf_of_range`, `isFinitelyPresented_range` —
  the three statements in the literal-subgroup form the constructions consume,
  the last one via `HNNFinitePresentation.isFinitelyPresented_hnnExtension`.
-/

namespace GroupApproximation
namespace HNNSubextension

open HNNBritton

universe u v

/-! ## 1.  Words built from a set of base elements -/

section Words

variable {G : Type u} [Group G] {A B : Subgroup G}

/-- The generating set `of '' S ∪ {t}` of the subgroup a set `S` of base
elements generates together with the stable letter. -/
def genOf (φ : A ≃* B) (S : Set G) : Set (HNNExtension G A B φ) :=
  ((HNNExtension.of : G →* HNNExtension G A B φ) '' S) ∪
    {(HNNExtension.t : HNNExtension G A B φ)}

/-- A spelling whose syllables all come from `S` lies in the subgroup that `S`
generates with the stable letter. -/
theorem spell_mem_closure (φ : A ≃* B) (S : Set G) :
    ∀ l : List (ℤˣ × G), (∀ p ∈ l, p.2 ∈ S) →
      spell φ l ∈ Subgroup.closure (genOf φ S) := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [spell_nil]
      exact one_mem _
  | cons x l ih =>
      intro hl
      rw [spell_cons]
      have ht : (HNNExtension.t : HNNExtension G A B φ) ∈
          Subgroup.closure (genOf φ S) := Subgroup.subset_closure (Or.inr rfl)
      have hx : (HNNExtension.of x.2 : HNNExtension G A B φ) ∈
          Subgroup.closure (genOf φ S) :=
        Subgroup.subset_closure (Or.inl ⟨x.2, hl x List.mem_cons_self, rfl⟩)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ ht _) hx)
        (ih fun p hp => hl p (List.mem_cons_of_mem _ hp))

/-- The same, with a head. -/
theorem wordProd_mem_closure (φ : A ≃* B) (S : Set G) {g : G} (hg : g ∈ S)
    (l : List (ℤˣ × G)) (hl : ∀ p ∈ l, p.2 ∈ S) :
    wordProd φ g l ∈ Subgroup.closure (genOf φ S) := by
  simp only [wordProd]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨g, hg, rfl⟩))
    (spell_mem_closure φ S l hl)

end Words

/-! ## 2.  Pushing a syllable list forward -/

section Abstract

variable {G : Type u} [Group G] {A B : Subgroup G}
variable {H : Type v} [Group H] {A' B' : Subgroup H}

/-- Push a syllable list forward along a homomorphism of base groups: the signs
are untouched, the group entries are moved. -/
def mapList (ι : H →* G) (l : List (ℤˣ × H)) : List (ℤˣ × G) :=
  l.map (fun p : ℤˣ × H => (p.1, ι p.2))

theorem mapList_nil (ι : H →* G) : mapList ι ([] : List (ℤˣ × H)) = [] := rfl

theorem mapList_cons (ι : H →* G) (x : ℤˣ × H) (l : List (ℤˣ × H)) :
    mapList ι (x :: l) = (x.1, ι x.2) :: mapList ι l := rfl

theorem mapList_ne_nil (ι : H →* G) {l : List (ℤˣ × H)} (hl : l ≠ []) :
    mapList ι l ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ =>
      rw [mapList_cons]
      exact List.cons_ne_nil _ _

theorem mem_mapList (ι : H →* G) {p : ℤˣ × G} {l : List (ℤˣ × H)}
    (hp : p ∈ mapList ι l) : ∃ q ∈ l, (q.1, ι q.2) = p :=
  List.mem_map.mp hp

/-! ## 3.  The hypothesis, and the canonical map -/

/-- **`ι` presents `(H, A', B', φ')` as a subextension of `(G, A, B, φ)`.**

The two `sat` clauses are the content: an element of `H` whose image lies in an
associated subgroup of the big extension already lies in the corresponding
associated subgroup of the small one.  For a literal subgroup `Z ≤ G` with
`A' = A ⊓ Z` and `B' = B ⊓ Z` they are tautologies; see
`isSubextension_subgroupOf`. -/
structure IsSubextension (φ : A ≃* B) (φ' : A' ≃* B') (ι : H →* G) : Prop where
  /-- The base map is injective. -/
  inj : Function.Injective ι
  /-- `ι` carries `A'` into `A`. -/
  memA : ∀ a : A', ι (a : H) ∈ A
  /-- **Saturation at `A`.** -/
  satA : ∀ h : H, ι h ∈ A → h ∈ A'
  /-- **Saturation at `B`.** -/
  satB : ∀ h : H, ι h ∈ B → h ∈ B'
  /-- `ι` intertwines `φ'` with `φ`. -/
  compat : ∀ (a : A') (hA : ι (a : H) ∈ A),
    ι ((φ' a : B') : H) = ((φ ⟨ι (a : H), hA⟩ : B) : G)

/-- **The canonical map, characterised.**  Every statement about the canonical
map below is proved from these two equations alone, so nothing depends on how
`HNNExtension.lift` spells its hypothesis. -/
structure IsSubextensionHom (φ : A ≃* B) (φ' : A' ≃* B') (ι : H →* G)
    (Ψ : HNNExtension H A' B' φ' →* HNNExtension G A B φ) : Prop where
  /-- On the base copy, `Ψ` is `ι`. -/
  map_of : ∀ h : H, Ψ (HNNExtension.of h) = HNNExtension.of (ι h)
  /-- `Ψ` sends the stable letter to the stable letter. -/
  map_t : Ψ (HNNExtension.t : HNNExtension H A' B' φ') =
    (HNNExtension.t : HNNExtension G A B φ)

variable {φ : A ≃* B} {φ' : A' ≃* B'} {ι : H →* G}
variable {Ψ : HNNExtension H A' B' φ' →* HNNExtension G A B φ}

/-- The `B`-side inclusion clause is redundant: it follows from the `A`-side
clause, compatibility, and surjectivity of `φ'`. -/
theorem IsSubextension.memB (hs : IsSubextension φ φ' ι) (b : B') :
    ι (b : H) ∈ B := by
  have hA : ι (φ'.symm b : H) ∈ A := hs.memA (φ'.symm b)
  have hc := hs.compat (φ'.symm b) hA
  rw [MulEquiv.apply_symm_apply] at hc
  rw [hc]
  exact (φ ⟨ι (φ'.symm b : H), hA⟩).2

/-- **Saturation, at either sign.**  This is the single place the hypothesis is
used, and it is exactly what keeps a reduced word reduced. -/
theorem mem_toSubgroup_of_map (hs : IsSubextension φ φ' ι) (u : ℤˣ) {h : H}
    (hmem : ι h ∈ HNNExtension.toSubgroup A B u) :
    h ∈ HNNExtension.toSubgroup A' B' u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [HNNExtension.toSubgroup_one] at hmem
    rw [HNNExtension.toSubgroup_one]
    exact hs.satA h hmem
  · rw [HNNExtension.toSubgroup_neg_one] at hmem
    rw [HNNExtension.toSubgroup_neg_one]
    exact hs.satB h hmem

/-- The canonical homomorphism `HNNExtension H A' B' φ' →* HNNExtension G A B φ`
determined by `ι` on the base and by fixing the stable letter. -/
def canonical (hs : IsSubextension φ φ' ι) :
    HNNExtension H A' B' φ' →* HNNExtension G A B φ :=
  HNNExtension.lift ((HNNExtension.of : G →* HNNExtension G A B φ).comp ι)
    (HNNExtension.t : HNNExtension G A B φ)
    (by
      intro a
      have hA : ι (a : H) ∈ A := hs.memA a
      have hc : ι ((φ' a : B') : H) = ((φ ⟨ι (a : H), hA⟩ : B) : G) :=
        hs.compat a hA
      have hb : (HNNExtension.t : HNNExtension G A B φ) *
            HNNExtension.of (ι (a : H)) * HNNExtension.t⁻¹
          = HNNExtension.of ((φ ⟨ι (a : H), hA⟩ : B) : G) :=
        t_conj_of_mem φ hA
      have hgoal : (HNNExtension.of (ι ((φ' a : B') : H)) :
              HNNExtension G A B φ)
          = (HNNExtension.t : HNNExtension G A B φ) *
            HNNExtension.of (ι (a : H)) * HNNExtension.t⁻¹ := by
        rw [hc, hb]
      exact mul_inv_eq_iff_eq_mul.mp hgoal.symm)

/-- The canonical map does what it should. -/
theorem isSubextensionHom_canonical (hs : IsSubextension φ φ' ι) :
    IsSubextensionHom φ φ' ι (canonical hs) where
  map_of h := by simp [canonical, HNNExtension.lift_of]
  map_t := by simp [canonical, HNNExtension.lift_t]

/-! ## 4.  Reducedness is preserved -/

/-- **The combinatorial heart.**  Pushing a pinch-free syllable list forward
keeps it pinch-free: a pinch upstairs would be a syllable landing in an
associated subgroup of the big extension, and saturation puts it back into the
corresponding associated subgroup of the small one, where the original list was
already known to have no pinch. -/
theorem noPinch_mapList (hs : IsSubextension φ φ' ι) :
    ∀ l : List (ℤˣ × H), NoPinch A' B' l → NoPinch A B (mapList ι l)
  | [], _ => by
      rw [mapList_nil]
      exact noPinch_nil
  | [_], _ => by
      rw [mapList_cons, mapList_nil]
      exact noPinch_singleton _
  | x :: y :: l, h => by
      have ih : NoPinch A B (mapList ι (y :: l)) :=
        noPinch_mapList hs (y :: l) h.tail
      rw [mapList_cons] at ih
      rw [mapList_cons, mapList_cons]
      refine noPinch_cons_cons ?_ ih
      intro hmem
      exact h.seam y (by simp) (mem_toSubgroup_of_map hs x.1 hmem)

/-! ## 5.  Transporting spellings -/

/-- The canonical map turns a spelling into the pushed-forward spelling. -/
theorem map_spell (hΨ : IsSubextensionHom φ φ' ι Ψ) (l : List (ℤˣ × H)) :
    Ψ (spell φ' l) = spell φ (mapList ι l) := by
  induction l with
  | nil => simp only [mapList_nil, spell_nil, map_one]
  | cons x l ih =>
      simp only [mapList_cons, spell_cons, map_mul, map_zpow, hΨ.map_t,
        hΨ.map_of, ih]

/-- The same, with a head. -/
theorem map_wordProd (hΨ : IsSubextensionHom φ φ' ι Ψ) (g : H)
    (l : List (ℤˣ × H)) :
    Ψ (wordProd φ' g l) = wordProd φ (ι g) (mapList ι l) := by
  simp only [wordProd, map_mul, hΨ.map_of, map_spell hΨ]

/-! ## 6.  The lemma -/

/-- **Mikaelian's Lemma 2.4, structural half.**  The canonical map of a
subextension is injective.

A nontrivial element of the small extension either has a pinch-free spelling
with at least one stable letter — and then so does its image, by
`noPinch_mapList`, so Britton's lemma keeps the image nontrivial — or lies in
the base copy, where injectivity of `ι` and `HNNExtension.of_injective` settle
it. -/
theorem injective_of_isSubextensionHom (hs : IsSubextension φ φ' ι)
    (hΨ : IsSubextensionHom φ φ' ι Ψ) : Function.Injective Ψ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, l, hl, rfl⟩ := exists_hasSpelling φ' x
  rcases eq_or_ne l [] with rfl | hne
  · have hxo : Ψ (HNNExtension.of g : HNNExtension H A' B' φ') = 1 := by
      rw [← wordProd_nil φ' g]
      exact hx
    have h1 : (HNNExtension.of (ι g) : HNNExtension G A B φ) = 1 := by
      rw [← hΨ.map_of g]
      exact hxo
    have hone : (HNNExtension.of (1 : G) : HNNExtension G A B φ) = 1 := map_one _
    have h2 : ι g = 1 :=
      HNNExtension.of_injective (φ := φ) (h1.trans hone.symm)
    have h3 : g = 1 := hs.inj (by rw [h2, map_one])
    rw [wordProd_nil, h3, map_one]
  · exfalso
    have hmap : Ψ (wordProd φ' g l) = wordProd φ (ι g) (mapList ι l) :=
      map_wordProd hΨ g l
    have hzero : wordProd φ (ι g) (mapList ι l) = 1 := by
      rw [← hmap]
      exact hx
    exact wordProd_ne_one φ (mapList_ne_nil ι hne) (noPinch_mapList hs l hl) hzero

/-- **The range.**  The canonical map hits exactly the subgroup generated by the
image of the small base group and the stable letter. -/
theorem range_eq_closure (hΨ : IsSubextensionHom φ φ' ι Ψ) (S : Set G)
    (hmem : ∀ h : H, ι h ∈ S) (hsurj : ∀ g ∈ S, ∃ h : H, ι h = g) :
    Ψ.range = Subgroup.closure (genOf φ S) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨g, l, -, rfl⟩ := exists_hasSpelling φ' x
    rw [map_wordProd hΨ]
    refine wordProd_mem_closure φ S (hmem g) (mapList ι l) ?_
    intro p hp
    obtain ⟨q, -, rfl⟩ := mem_mapList ι hp
    exact hmem q.2
  · rw [Subgroup.closure_le]
    simp only [genOf]
    rintro y (⟨a, ha, rfl⟩ | hy)
    · obtain ⟨h, rfl⟩ := hsurj a ha
      exact SetLike.mem_coe.mpr ⟨HNNExtension.of h, hΨ.map_of h⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact SetLike.mem_coe.mpr ⟨HNNExtension.t, hΨ.map_t⟩

/-- **The small extension is isomorphic to the subgroup it generates.** -/
noncomputable def mulEquivRange (hs : IsSubextension φ φ' ι)
    (hΨ : IsSubextensionHom φ φ' ι Ψ) :
    HNNExtension H A' B' φ' ≃* Ψ.range :=
  MonoidHom.ofInjective (injective_of_isSubextensionHom hs hΨ)

end Abstract

/-! ## 7.  The literal-subgroup form -/

section Restriction

variable {G : Type} [Group G] {A B : Subgroup G} (φ : A ≃* B) {Z : Subgroup G}

/-- The element of `K` underlying a member of `K.subgroupOf L`. -/
def liftSub {K L : Subgroup G} (a : ↥(K.subgroupOf L)) : ↥K :=
  ⟨(a.1 : G), Subgroup.mem_subgroupOf.mp a.2⟩

/-- The forward half of the restriction of `φ` to a stable subgroup. -/
def restrictFwd (hst : Higman.HNNDescent.Stable φ Z)
    (a : ↥(A.subgroupOf Z)) : ↥(B.subgroupOf Z) :=
  ⟨⟨((φ (liftSub a) : ↥B) : G), hst.fwd (liftSub a) a.1.2⟩,
    Subgroup.mem_subgroupOf.mpr (φ (liftSub a)).2⟩

/-- The backward half of the restriction of `φ` to a stable subgroup. -/
def restrictBwd (hst : Higman.HNNDescent.Stable φ Z)
    (b : ↥(B.subgroupOf Z)) : ↥(A.subgroupOf Z) :=
  ⟨⟨((φ.symm (liftSub b) : ↥A) : G), hst.bwd (liftSub b) b.1.2⟩,
    Subgroup.mem_subgroupOf.mpr (φ.symm (liftSub b)).2⟩

/-- **The restriction of `φ` to a stable subgroup.**  `Higman.HNNDescent.Stable`
says `φ` carries `A ⊓ Z` into `Z` and `φ⁻¹` carries `B ⊓ Z` into `Z`; since `φ`
is a bijection `A ≃* B`, that is exactly `φ (A ⊓ Z) = B ⊓ Z`, and the two
restrictions are mutually inverse. -/
def restrictEquiv (hst : Higman.HNNDescent.Stable φ Z) :
    (A.subgroupOf Z) ≃* (B.subgroupOf Z) where
  toFun := restrictFwd φ hst
  invFun := restrictBwd φ hst
  left_inv a := by
    refine Subtype.ext (Subtype.ext ?_)
    have e0 : liftSub (restrictFwd φ hst a) = φ (liftSub a) := rfl
    have e : φ.symm (liftSub (restrictFwd φ hst a)) = liftSub a := by
      rw [e0, MulEquiv.symm_apply_apply]
    exact congrArg (fun x : ↥A => (x : G)) e
  right_inv b := by
    refine Subtype.ext (Subtype.ext ?_)
    have e0 : liftSub (restrictBwd φ hst b) = φ.symm (liftSub b) := rfl
    have e : φ (liftSub (restrictBwd φ hst b)) = liftSub b := by
      rw [e0, MulEquiv.apply_symm_apply]
    exact congrArg (fun x : ↥B => (x : G)) e
  map_mul' a a' := by
    refine Subtype.ext (Subtype.ext ?_)
    have e0 : liftSub (a * a') = liftSub a * liftSub a' := rfl
    have e : φ (liftSub (a * a')) = φ (liftSub a) * φ (liftSub a') := by
      rw [e0, map_mul]
    exact congrArg (fun x : ↥B => (x : G)) e

/-- The restriction, evaluated. -/
theorem restrictEquiv_apply (hst : Higman.HNNDescent.Stable φ Z)
    (a : ↥(A.subgroupOf Z)) :
    restrictEquiv φ hst a = restrictFwd φ hst a := rfl

/-- **A stable subgroup is a subextension.**  Both saturation clauses are the
tautology `x ∈ A.subgroupOf Z ↔ (x : G) ∈ A`; stability enters only through
`restrictEquiv`, whose compatibility with `φ` is definitional. -/
theorem isSubextension_subgroupOf (hst : Higman.HNNDescent.Stable φ Z) :
    IsSubextension φ (restrictEquiv φ hst) Z.subtype where
  inj := fun _ _ h => Subtype.ext h
  memA a := Subgroup.mem_subgroupOf.mp a.2
  satA _ hh := Subgroup.mem_subgroupOf.mpr hh
  satB _ hh := Subgroup.mem_subgroupOf.mpr hh
  compat _ _ := rfl

/-- **The canonical map `⟨Z, t⟩ ← Z ∗_{φ'} t`.** -/
def toAmbient (hst : Higman.HNNDescent.Stable φ Z) :
    HNNExtension ↥Z (A.subgroupOf Z) (B.subgroupOf Z) (restrictEquiv φ hst) →*
      HNNExtension G A B φ :=
  canonical (isSubextension_subgroupOf φ hst)

/-- `toAmbient` is the canonical map: it is `Z ↪ G` on the base copy and fixes
the stable letter. -/
theorem isSubextensionHom_toAmbient (hst : Higman.HNNDescent.Stable φ Z) :
    IsSubextensionHom φ (restrictEquiv φ hst) Z.subtype (toAmbient φ hst) :=
  isSubextensionHom_canonical (isSubextension_subgroupOf φ hst)

/-- **Mikaelian 2.4 for a literal subgroup.**  `⟨Z, t⟩` is an HNN extension of
`Z` along the restriction of `φ`. -/
theorem toAmbient_injective (hst : Higman.HNNDescent.Stable φ Z) :
    Function.Injective (toAmbient φ hst) :=
  injective_of_isSubextensionHom (isSubextension_subgroupOf φ hst)
    (isSubextensionHom_toAmbient φ hst)

/-- The generating set used here and the one `Higman.HNNDescent` uses are the
same set. -/
theorem genOf_coe_eq_genSet :
    genOf φ (Z : Set G) = Higman.HNNDescent.genSet φ Z := by
  have himg : ((HNNExtension.of : G →* HNNExtension G A B φ) '' (Z : Set G))
      = ((Z.map (HNNExtension.of : G →* HNNExtension G A B φ) :
            Subgroup (HNNExtension G A B φ)) : Set (HNNExtension G A B φ)) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  simp only [genOf, Higman.HNNDescent.genSet, himg]

/-- **The range is `⟨Z, t⟩`.** -/
theorem range_toAmbient (hst : Higman.HNNDescent.Stable φ Z) :
    (toAmbient φ hst).range = Subgroup.closure (Higman.HNNDescent.genSet φ Z) := by
  have hrange := range_eq_closure (isSubextensionHom_toAmbient φ hst) (Z : Set G)
    (fun z => z.2) (fun g hg => ⟨⟨g, hg⟩, rfl⟩)
  rw [hrange, genOf_coe_eq_genSet]

/-- **`⟨Z, t⟩ ⊓ G = Z`.**  This is `Higman.HNNDescent.closure_inf_range`, quoted
against the range computed above; it is not reproved here. -/
theorem range_inf_of_range (hst : Higman.HNNDescent.Stable φ Z) :
    (toAmbient φ hst).range ⊓
        (HNNExtension.of : G →* HNNExtension G A B φ).range
      = Z.map (HNNExtension.of : G →* HNNExtension G A B φ) := by
  rw [range_toAmbient φ hst]
  exact Higman.HNNDescent.closure_inf_range φ hst

/-- **`Z` finitely presented and `A ⊓ Z` finitely generated make `⟨Z, t⟩`
finitely presented.**  The extension of `Z` is finitely presented by the
repository's HNN permanence theorem, and `⟨Z, t⟩` is isomorphic to it. -/
theorem isFinitelyPresented_range (hst : Higman.HNNDescent.Stable φ Z)
    [Group.IsFinitelyPresented ↥Z] (hA : (A.subgroupOf Z).FG) :
    Group.IsFinitelyPresented ↥((toAmbient φ hst).range) := by
  letI : Group.FG ↥(A.subgroupOf Z) :=
    (Group.fg_iff_subgroup_fg (A.subgroupOf Z)).mpr hA
  haveI : Group.IsFinitelyPresented
      (HNNExtension ↥Z (A.subgroupOf Z) (B.subgroupOf Z)
        (restrictEquiv φ hst)) :=
    HNNFinitePresentation.isFinitelyPresented_hnnExtension (restrictEquiv φ hst)
  exact Group.IsFinitelyPresented.equiv
    (MonoidHom.ofInjective (toAmbient_injective φ hst))

end Restriction

end HNNSubextension
end GroupApproximation
