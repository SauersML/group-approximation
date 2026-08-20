import GroupApproximation.Higman.Program

/-!
# The join of two benign subgroups, and the one lemma it needs

Higman's Lemma 3.2 has two halves.  Intersections are cheap --- a direct
product does it, and `Higman.BenignWitness.inf` proves it outright.  Joins
are not: the classical proof glues the two witnesses with a nested
combination of amalgams and HNN extensions (Mikaelian's `✻`-construction) and
then reads the join off the multi-stable-letter HNN extension sitting inside
it.

This file records a shorter route, and reduces the join to a single word
lemma.

## The construction

Do not amalgamate.  Put the two overgroups side by side in the **direct
product** `K := K₁ × K₂` and embed `G` diagonally, exactly as for
intersections.  Then

    M₁ := L₁ × ⊤   and   M₂ := ⊤ × L₂

are *finitely generated* subgroups of `K` --- `⊤` is finitely generated
because a finitely presented group is --- and they cut out the right things:

    G ∩ M₁ = A₁,      G ∩ M₂ = A₂.

Now add two stable letters, one at a time, each centralizing one of them:

    Γ₁ := K ∗_{M₁} t₁,     Γ₂ := Γ₁ ∗_{M₂} t₂,

both finitely presented, by
`HNNFinitePresentation.isFinitelyPresented_hnnExtension` twice.  The
finitely generated subgroup that cuts out the join is

    L := ⟨Gᵗ¹, Gᵗ²⟩,

finitely generated because `G` is.  Everything in this file except the
final inclusion is proved below, unconditionally.

## What is left, and why it is one lemma

The remaining inclusion `G ∩ L ≤ ⟨A₁, A₂⟩` follows from `PinchProperty`
applied twice, and from nothing else:

* inside `Γ₁`, with `Z = ⟨A₁, A₂⟩` and `Q = G`.  The hypotheses read
  `G ∩ M₁ = A₁ ≤ Z` and `Z ∩ M₁ ≤ G`, both immediate, and the conclusion is
  `⟨A₁, A₂, Gᵗ¹⟩ ∩ K = ⟨A₁, A₂⟩`;
* inside `Γ₂`, with `Z = ⟨A₁, A₂, Gᵗ¹⟩` and `Q = G`.  The hypotheses read
  `G ∩ M₂ = A₂ ≤ Z`, and `Z ∩ M₂ ≤ Z ∩ K = ⟨A₁, A₂⟩ ≤ G` --- the second one
  is exactly the conclusion of the first application, which is why the two
  have to be taken in this order.

Then `L ≤ ⟨Z, Gᵗ²⟩`, so `G ∩ L ≤ Z ∩ K = ⟨A₁, A₂⟩`.

`PinchProperty` itself is the word lemma stated in `Higman.Program`, and it
is the only thing between this file and Higman's Lemma 3.2.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.ProductFinitePresentation

variable {G : Type} [Group G] {A₁ A₂ : Subgroup G}

/-! ## 1.  The glued base -/

/-- The two overgroups, side by side. -/
abbrev JoinBase (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) : Type :=
  w₁.K × w₂.K

/-- `G`, embedded diagonally. -/
def joinEmb (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    G →* JoinBase w₁ w₂ :=
  (w₁.emb).prod (w₂.emb)

theorem joinEmb_injective (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Function.Injective (joinEmb w₁ w₂) := by
  intro x y hxy
  exact w₁.emb_injective (congrArg Prod.fst hxy)

/-- The first finitely generated subgroup: `L₁ × ⊤`. -/
def joinM₁ (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Subgroup (JoinBase w₁ w₂) :=
  w₁.L.prod ⊤

/-- The second: `⊤ × L₂`. -/
def joinM₂ (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Subgroup (JoinBase w₁ w₂) :=
  (⊤ : Subgroup w₁.K).prod w₂.L

theorem joinM₁_fg (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinM₁ w₁ w₂).FG := by
  letI : Group.FG w₂.K := fg_of_isFinitelyPresented w₂.K
  exact fg_prod w₁.L_fg fg_top

theorem joinM₂_fg (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinM₂ w₁ w₂).FG := by
  letI : Group.FG w₁.K := fg_of_isFinitelyPresented w₁.K
  exact fg_prod fg_top w₂.L_fg

/-- **The first subgroup cuts out `A₁`.** -/
theorem comap_joinM₁ (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinM₁ w₁ w₂).comap (joinEmb w₁ w₂) = A₁ := by
  have h := w₁.comap_eq
  refine Subgroup.ext fun g => ?_
  constructor
  · intro hg
    have hg' : ((w₁.emb g, w₂.emb g) : w₁.K × w₂.K) ∈ w₁.L.prod ⊤ :=
      Subgroup.mem_comap.mp hg
    have h1 : w₁.emb g ∈ w₁.L := (Subgroup.mem_prod.mp hg').1
    rw [← h]
    exact Subgroup.mem_comap.mpr h1
  · intro hg
    rw [← h] at hg
    refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨?_, Subgroup.mem_top _⟩)
    exact Subgroup.mem_comap.mp hg

/-- **The second subgroup cuts out `A₂`.** -/
theorem comap_joinM₂ (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinM₂ w₁ w₂).comap (joinEmb w₁ w₂) = A₂ := by
  have h := w₂.comap_eq
  refine Subgroup.ext fun g => ?_
  constructor
  · intro hg
    have hg' : ((w₁.emb g, w₂.emb g) : w₁.K × w₂.K) ∈ (⊤ : Subgroup w₁.K).prod w₂.L :=
      Subgroup.mem_comap.mp hg
    have h2 : w₂.emb g ∈ w₂.L := (Subgroup.mem_prod.mp hg').2
    rw [← h]
    exact Subgroup.mem_comap.mpr h2
  · intro hg
    rw [← h] at hg
    refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩)
    exact Subgroup.mem_comap.mp hg

/-! ## 2.  The two stable letters -/

/-- The first HNN extension: a stable letter centralizing `L₁ × ⊤`. -/
abbrev JoinLevel1 (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) : Type :=
  CentHNN (joinM₁ w₁ w₂)

/-- The second subgroup, transported into the first extension. -/
def joinM₂' (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Subgroup (JoinLevel1 w₁ w₂) :=
  (joinM₂ w₁ w₂).map (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)

theorem joinM₂'_fg (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinM₂' w₁ w₂).FG :=
  fg_map (joinM₂_fg w₁ w₂) _

/-- The second HNN extension. -/
abbrev JoinLevel2 (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) : Type :=
  CentHNN (joinM₂' w₁ w₂)

/-- Both extensions are finitely presented. -/
theorem isFinitelyPresented_joinLevel1 (w₁ : BenignWitness A₁)
    (w₂ : BenignWitness A₂) : Group.IsFinitelyPresented (JoinLevel1 w₁ w₂) :=
  isFinitelyPresented_centHNN _ (joinM₁_fg w₁ w₂)

theorem isFinitelyPresented_joinLevel2 (w₁ : BenignWitness A₁)
    (w₂ : BenignWitness A₂) : Group.IsFinitelyPresented (JoinLevel2 w₁ w₂) := by
  letI : Group.IsFinitelyPresented (JoinLevel1 w₁ w₂) :=
    isFinitelyPresented_joinLevel1 w₁ w₂
  exact isFinitelyPresented_centHNN _ (joinM₂'_fg w₁ w₂)

/-- `G`, embedded in the two-letter extension. -/
def joinEmb₂ (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    G →* JoinLevel2 w₁ w₂ :=
  (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂).comp
    ((HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂).comp (joinEmb w₁ w₂))

theorem joinEmb₂_injective (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Function.Injective (joinEmb₂ w₁ w₂) :=
  ((of_injective_centHNN _).comp (of_injective_centHNN _)).comp
    (joinEmb_injective w₁ w₂)

/-! ## 3.  The finitely generated subgroup that cuts out the join -/

/-- The image of `G` in the two-letter extension. -/
def joinX (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Subgroup (JoinLevel2 w₁ w₂) :=
  (⊤ : Subgroup G).map (joinEmb₂ w₁ w₂)

/-- The subgroup `⟨Gᵗ¹, Gᵗ²⟩`, where `t₁` is the stable letter of the first
extension pushed into the second, and `t₂` is the second stable letter. -/
def joinL (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    Subgroup (JoinLevel2 w₁ w₂) :=
  ((joinX w₁ w₂).map
      (MulAut.conj
        ((HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂)
          (HNNExtension.t))⁻¹).toMonoidHom)
    ⊔ ((joinX w₁ w₂).map
      (MulAut.conj (HNNExtension.t : JoinLevel2 w₁ w₂)⁻¹).toMonoidHom)

theorem joinX_fg [Group.FG G] (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinX w₁ w₂).FG :=
  fg_map fg_top _

theorem joinL_fg [Group.FG G] (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    (joinL w₁ w₂).FG :=
  fg_sup (fg_map (joinX_fg w₁ w₂) _) (fg_map (joinX_fg w₁ w₂) _)

/-! ## 4.  The easy inclusion -/

/-- An element of `A₁` is fixed by the first stable letter, so it lies in the
conjugate of `G` by it; and likewise for `A₂` and the second.  Hence the join
is contained in what the construction cuts out.

This is the half of Higman's Lemma 3.2(2) that needs no word argument. -/
theorem join_le_comap_joinL (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂) :
    A₁ ⊔ A₂ ≤ (joinL w₁ w₂).comap (joinEmb₂ w₁ w₂) := by
  refine sup_le ?_ ?_
  · intro a ha
    have hmem : joinEmb w₁ w₂ a ∈ joinM₁ w₁ w₂ := by
      have : a ∈ (joinM₁ w₁ w₂).comap (joinEmb w₁ w₂) := by
        rw [comap_joinM₁]
        exact ha
      exact Subgroup.mem_comap.mp this
    have hfix : (HNNExtension.t : JoinLevel1 w₁ w₂)⁻¹ *
        HNNExtension.of (joinEmb w₁ w₂ a) * HNNExtension.t
          = HNNExtension.of (joinEmb w₁ w₂ a) :=
      conj_eq_self_of_mem _ hmem
    refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ?_)
    refine ⟨joinEmb₂ w₁ w₂ a, ⟨a, Subgroup.mem_top a, rfl⟩, ?_⟩
    show _ * _ * _ = _
    rw [inv_inv]
    have hpush : (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂)
        ((HNNExtension.t : JoinLevel1 w₁ w₂)⁻¹ *
          HNNExtension.of (joinEmb w₁ w₂ a) * HNNExtension.t)
        = (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂)
          (HNNExtension.of (joinEmb w₁ w₂ a)) := by
      rw [hfix]
    rw [map_mul, map_mul, map_inv] at hpush
    exact hpush
  · intro a ha
    have hmem : (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)
        (joinEmb w₁ w₂ a) ∈ joinM₂' w₁ w₂ := by
      have h₀ : a ∈ (joinM₂ w₁ w₂).comap (joinEmb w₁ w₂) := by
        rw [comap_joinM₂]
        exact ha
      exact ⟨joinEmb w₁ w₂ a, Subgroup.mem_comap.mp h₀, rfl⟩
    have hfix := conj_eq_self_of_mem (joinM₂' w₁ w₂) hmem
    refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_right ?_)
    refine ⟨joinEmb₂ w₁ w₂ a, ⟨a, Subgroup.mem_top a, rfl⟩, ?_⟩
    show _ * _ * _ = _
    rw [inv_inv]
    exact hfix

/-! ## 5.  The two applications of the pinch lemma -/

variable (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂)

/-- The join, transported into the glued base. -/
def joinZ₁ : Subgroup (JoinBase w₁ w₂) := (A₁ ⊔ A₂).map (joinEmb w₁ w₂)

/-- The image of `G` in the glued base. -/
def joinQ₁ : Subgroup (JoinBase w₁ w₂) := (⊤ : Subgroup G).map (joinEmb w₁ w₂)

/-- `⟨A₁ ⊔ A₂, Gᵗ¹⟩`, inside the first extension. -/
def joinS₁ : Subgroup (JoinLevel1 w₁ w₂) :=
  Subgroup.closure (Pinch.genSet (joinM₁ w₁ w₂) (joinZ₁ w₁ w₂) (joinQ₁ w₁ w₂))

/-- The image of `G` in the first extension. -/
def joinQ₂ : Subgroup (JoinLevel1 w₁ w₂) :=
  (⊤ : Subgroup G).map
    ((HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂).comp (joinEmb w₁ w₂))

/-- `⟨joinS₁, Gᵗ²⟩`, inside the second extension. -/
def joinS₂ : Subgroup (JoinLevel2 w₁ w₂) :=
  Subgroup.closure (Pinch.genSet (joinM₂' w₁ w₂) (joinS₁ w₁ w₂) (joinQ₂ w₁ w₂))

theorem map_joinZ₁_le_joinS₁ :
    (joinZ₁ w₁ w₂).map (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)
      ≤ joinS₁ w₁ w₂ := by
  intro x hx
  exact Subgroup.subset_closure (Or.inl hx)

/-- **The first application.**  `⟨A₁ ⊔ A₂, Gᵗ¹⟩ ∩ K = A₁ ⊔ A₂`, in the glued
base. -/
theorem level_one :
    joinS₁ w₁ w₂ ⊓
        (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂).range
      ≤ (joinZ₁ w₁ w₂).map HNNExtension.of := by
  refine Pinch.pinch (joinM₁ w₁ w₂) (joinZ₁ w₁ w₂) (joinQ₁ w₁ w₂) ?_ ?_
  · rintro x ⟨hxQ, hxM⟩
    obtain ⟨g, -, rfl⟩ := hxQ
    have hg : g ∈ (joinM₁ w₁ w₂).comap (joinEmb w₁ w₂) := Subgroup.mem_comap.mpr hxM
    rw [comap_joinM₁] at hg
    exact ⟨g, Subgroup.mem_sup_left hg, rfl⟩
  · rintro x ⟨hxZ, -⟩
    obtain ⟨g, -, rfl⟩ := hxZ
    exact ⟨g, Subgroup.mem_top g, rfl⟩

/-- **The second application.**  `⟨joinS₁, Gᵗ²⟩ ∩ Γ₁ = joinS₁`.  Its second
hypothesis is the conclusion of the first application, which is why the two
have to be taken in this order. -/
theorem level_two :
    joinS₂ w₁ w₂ ⊓
        (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂).range
      ≤ (joinS₁ w₁ w₂).map HNNExtension.of := by
  refine Pinch.pinch (joinM₂' w₁ w₂) (joinS₁ w₁ w₂) (joinQ₂ w₁ w₂) ?_ ?_
  · rintro x ⟨hxQ, hxM⟩
    obtain ⟨g, -, rfl⟩ := hxQ
    obtain ⟨y, hy, hyeq⟩ := hxM
    have hyg : y = joinEmb w₁ w₂ g := of_injective_centHNN _ hyeq
    rw [hyg] at hy
    have hg : g ∈ (joinM₂ w₁ w₂).comap (joinEmb w₁ w₂) := Subgroup.mem_comap.mpr hy
    rw [comap_joinM₂] at hg
    refine map_joinZ₁_le_joinS₁ w₁ w₂ ?_
    exact ⟨joinEmb w₁ w₂ g, ⟨g, Subgroup.mem_sup_right hg, rfl⟩, rfl⟩
  · rintro x ⟨hxS, hxM⟩
    obtain ⟨y, -, rfl⟩ := hxM
    obtain ⟨u, hu, hueq⟩ :=
      level_one w₁ w₂ ⟨hxS, ⟨y, rfl⟩⟩
    obtain ⟨g, -, hg⟩ := hu
    refine ⟨g, Subgroup.mem_top g, ?_⟩
    show (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)
      (joinEmb w₁ w₂ g) = _
    rw [hg]
    exact hueq

/-! ## 6.  The join is cut out -/

theorem joinL_le_joinS₂ : joinL w₁ w₂ ≤ joinS₂ w₁ w₂ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, -, rfl⟩ := hx
    refine Subgroup.subset_closure (Or.inl ?_)
    refine ⟨(HNNExtension.t : JoinLevel1 w₁ w₂)⁻¹ *
      HNNExtension.of (joinEmb w₁ w₂ g) * HNNExtension.t, ?_, ?_⟩
    · refine Subgroup.subset_closure (Or.inr ?_)
      refine ⟨HNNExtension.of (joinEmb w₁ w₂ g),
        ⟨g, Subgroup.mem_top g, rfl⟩, ?_⟩
      show _ * _ * _ = _
      rw [inv_inv]
    · show (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂)
        ((HNNExtension.t : JoinLevel1 w₁ w₂)⁻¹ *
          HNNExtension.of (joinEmb w₁ w₂ g) * HNNExtension.t) = _
      rw [map_mul, map_mul, map_inv]
      show _ = _ * _ * _
      rw [inv_inv]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, -, rfl⟩ := hx
    refine Subgroup.subset_closure (Or.inr ?_)
    refine ⟨joinEmb₂ w₁ w₂ g, ⟨g, Subgroup.mem_top g, rfl⟩, rfl⟩

/-- **Higman's Lemma 3.2(2): benign subgroups are closed under joins.**  The
subgroup `joinL` cuts the join out of `G`. -/
theorem comap_joinL : (joinL w₁ w₂).comap (joinEmb₂ w₁ w₂) = A₁ ⊔ A₂ := by
  refine le_antisymm ?_ (join_le_comap_joinL w₁ w₂)
  intro g hg
  have hgL : joinEmb₂ w₁ w₂ g ∈ joinL w₁ w₂ := Subgroup.mem_comap.mp hg
  have hgS₂ : joinEmb₂ w₁ w₂ g ∈ joinS₂ w₁ w₂ := joinL_le_joinS₂ w₁ w₂ hgL
  have hrange : joinEmb₂ w₁ w₂ g ∈
      (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂).range :=
    ⟨(HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂) (joinEmb w₁ w₂ g), rfl⟩
  obtain ⟨y, hyS₁, hyeq⟩ := level_two w₁ w₂ ⟨hgS₂, hrange⟩
  have hy : y = (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)
      (joinEmb w₁ w₂ g) := of_injective_centHNN _ hyeq
  rw [hy] at hyS₁
  obtain ⟨u, huZ, hueq⟩ :=
    level_one w₁ w₂ ⟨hyS₁, ⟨joinEmb w₁ w₂ g, rfl⟩⟩
  have hu : u = joinEmb w₁ w₂ g := of_injective_centHNN _ hueq
  rw [hu] at huZ
  obtain ⟨j, hj, hjeq⟩ := huZ
  have : j = g := joinEmb_injective w₁ w₂ hjeq
  rw [← this]
  exact hj

/-- **The witness.** -/
def joinWitness [Group.FG G] : BenignWitness (A₁ ⊔ A₂) where
  K := JoinLevel2 w₁ w₂
  fp := isFinitelyPresented_joinLevel2 w₁ w₂
  emb := joinEmb₂ w₁ w₂
  emb_injective := joinEmb₂_injective w₁ w₂
  L := joinL w₁ w₂
  L_fg := joinL_fg w₁ w₂
  comap_eq := comap_joinL w₁ w₂

/-- **Higman's Lemma 3.2(2), proved.** -/
theorem Benign.sup [Group.FG G] (h₁ : Benign A₁) (h₂ : Benign A₂) :
    Benign (A₁ ⊔ A₂) := by
  obtain ⟨u₁⟩ := h₁
  obtain ⟨u₂⟩ := h₂
  exact ⟨joinWitness u₁ u₂⟩

end Higman
end GroupApproximation
