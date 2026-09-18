import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleCore
import GroupApproximation.GroupTheory.HydeLodha.HigmanEpstein
import GroupApproximation.Meta.AxiomGuard

/-!
# Higman–Epstein with fragmentation

`HydeLodha.isSimpleGroup_commutator` asks that `⁅G, G⁆` compresses *every* pair `g₁, g₂ ∈ G`
into a small set.  In a Röver–Nekrashevych group elements have full support, so here the pairs
are first cut into fragments (`Fragments G Small`: products of pairwise jointly `Small`-supported
elements of `G`), and only small sets are compressed (`Compressible G U₁ Small`).

* `commutatorElement_mem_of_room`: for `N` normalized by `⁅G, G⁆`, `f ∈ N` displacing `U`,
  room `ThreeRoom G U U₁`, and `a, b ∈ G` supported in `U₁`: `⁅a, b⁆ ∈ N` (Epstein's trick).
* `commutator_le_of_room_fragments`: then `⁅G, G⁆ ≤ N`, via `commutator_le_of_fragments`.
* `isSimpleGroup_of_room_fragments`: the simplicity criterion.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open HydeLodha

variable {α : Type*}

/-- Room inside `U` around `U₁`: elements `k₂, k₃ ∈ G` move `U₁` into two further parts of `U`,
the three parts pairwise disjoint. -/
def ThreeRoom (G : Subgroup (Equiv.Perm α)) (U U₁ : Set α) : Prop :=
  ∃ U₂ U₃ : Set α, ∃ k₂ ∈ G, ∃ k₃ ∈ G, k₂ '' U₁ ⊆ U₂ ∧ k₃ '' U₁ ⊆ U₃ ∧
    Disjoint U₁ U₂ ∧ Disjoint U₁ U₃ ∧ Disjoint U₂ U₃ ∧ U₁ ∪ U₂ ∪ U₃ ⊆ U

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.ThreeRoom

/-- `Small` sets are `G`-invariant and `⁅G, G⁆` moves each of them into `U₁`. -/
def Compressible (G : Subgroup (Equiv.Perm α)) (U₁ : Set α) (Small : Set α → Prop) : Prop :=
  (∀ S, Small S → ∀ x ∈ G, Small (x '' S)) ∧ (∀ S, Small S → ∃ k ∈ ⁅G, G⁆, k '' S ⊆ U₁)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.Compressible

/-- Any two elements of `G` are products of fragments in `G`, every fragment of the first and
every fragment of the second being supported in a common `Small` set. -/
def Fragments (G : Subgroup (Equiv.Perm α)) (Small : Set α → Prop) : Prop :=
  ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∃ l₁ l₂ : List (Equiv.Perm α), (∀ a ∈ l₁, a ∈ G) ∧ (∀ b ∈ l₂, b ∈ G) ∧
    l₁.prod = g₁ ∧ l₂.prod = g₂ ∧
      ∀ a ∈ l₁, ∀ b ∈ l₂, ∃ S, Small S ∧ SupportedIn a S ∧ SupportedIn b S

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.Fragments

/-- **Epstein's step.**  Commutators of elements supported in the room lie in `N`. -/
theorem commutatorElement_mem_of_room (G N : Subgroup (Equiv.Perm α))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅G, G⁆, g * n * g⁻¹ ∈ N) {f : Equiv.Perm α} (hf : f ∈ N)
    {U U₁ : Set α} (hdisp : Disjoint (f '' U) U) (hroom : ThreeRoom G U U₁)
    {a b : Equiv.Perm α} (ha : a ∈ G) (hb : b ∈ G) (ha₁ : SupportedIn a U₁)
    (hb₁ : SupportedIn b U₁) : ⁅a, b⁆ ∈ N := by
  obtain ⟨U₂, U₃, k₂, hk₂, k₃, hk₃, h₂, h₃, d12, d13, d23, hsub⟩ := hroom
  have haM : ⁅a, k₂⁆ ∈ ⁅G, G⁆ := Subgroup.commutator_mem_commutator ha hk₂
  have hbM : ⁅b, k₃⁆ ∈ ⁅G, G⁆ := Subgroup.commutator_mem_commutator hb hk₃
  have hc : SupportedIn (k₂ * a⁻¹ * k₂⁻¹) U₂ := (ha₁.inv.conj k₂).mono h₂
  have hd : SupportedIn (k₃ * b⁻¹ * k₃⁻¹) U₃ := (hb₁.inv.conj k₃).mono h₃
  have hsa : ⁅a, k₂⁆ = a * (k₂ * a⁻¹ * k₂⁻¹) := by
    rw [commutatorElement_def]
    group
  have hsb : ⁅b, k₃⁆ = b * (k₃ * b⁻¹ * k₃⁻¹) := by
    rw [commutatorElement_def]
    group
  have h12 : U₁ ∪ U₂ ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub (Or.inl (Or.inl hx))
    · exact hsub (Or.inl (Or.inr hx))
  have h13 : U₁ ∪ U₃ ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub (Or.inl (Or.inl hx))
    · exact hsub (Or.inr hx)
  have haU : SupportedIn ⁅a, k₂⁆ U := by
    rw [hsa]
    exact (ha₁.mul hc).mono h12
  have hbU : SupportedIn ⁅b, k₃⁆ U := by
    rw [hsb]
    exact (hb₁.mul hd).mono h13
  have hN1 : ⁅⁅a, k₂⁆, f⁆ ∈ N := commutatorElement_mem_right hN haM hf
  have hN2 : ⁅⁅⁅a, k₂⁆, f⁆, ⁅b, k₃⁆⁆ ∈ N := commutatorElement_mem_left hN hN1 hbM
  rw [commutatorElement_commutatorElement_of_displaced hdisp haU hbU] at hN2
  have hcb : Commute (k₂ * a⁻¹ * k₂⁻¹) (b * (k₃ * b⁻¹ * k₃⁻¹)) :=
    commute_of_supportedIn hc (hb₁.mul hd) (Set.disjoint_union_right.mpr ⟨d12.symm, d23⟩)
  have had : Commute a (k₃ * b⁻¹ * k₃⁻¹) := commute_of_supportedIn ha₁ hd d13
  rw [hsa, hsb, commutatorElement_mul_left_of_commute hcb,
    commutatorElement_mul_right_of_commute had] at hN2
  exact hN2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutatorElement_mem_of_room

/-- **Higman–Epstein with fragmentation.** -/
theorem commutator_le_of_room_fragments (G N : Subgroup (Equiv.Perm α))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅G, G⁆, g * n * g⁻¹ ∈ N) {f : Equiv.Perm α} (hf : f ∈ N)
    {U U₁ : Set α} (hdisp : Disjoint (f '' U) U) (hroom : ThreeRoom G U U₁)
    {Small : Set α → Prop} (hcomp : Compressible G U₁ Small) (hfrag : Fragments G Small) :
    ⁅G, G⁆ ≤ N := by
  refine commutator_le_of_fragments G N
    (fun a b => ∃ S, Small S ∧ SupportedIn a S ∧ SupportedIn b S) ?_ hfrag
  intro a ha b hb hab x hx
  obtain ⟨S, hS, haS, hbS⟩ := hab
  obtain ⟨k, hk, hkS⟩ := hcomp.2 (x '' S) (hcomp.1 S hS x hx)
  have hkG : k ∈ G := commutator_le_self G hk
  have hxa : x * a * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hx ha) (G.inv_mem hx)
  have hxb : x * b * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hx hb) (G.inv_mem hx)
  have hka : k * (x * a * x⁻¹) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hkG hxa) (G.inv_mem hkG)
  have hkb : k * (x * b * x⁻¹) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hkG hxb) (G.inv_mem hkG)
  have hN2 := commutatorElement_mem_of_room G N hN hf hdisp hroom hka hkb
    (((haS.conj x).conj k).mono hkS) (((hbS.conj x).conj k).mono hkS)
  have e : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, commutatorElement_eq_conj k (x * a * x⁻¹) (x * b * x⁻¹)]
  exact hN _ hN2 _ ((⁅G, G⁆).inv_mem hk)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutator_le_of_room_fragments

/-- **Simplicity of `⁅G, G⁆`** when each nontrivial element of `⁅G, G⁆` displaces a set with
room around a compressing target, and `G` fragments into small pieces. -/
theorem isSimpleGroup_of_room_fragments (G : Subgroup (Equiv.Perm α))
    (hne : ⁅G, G⁆ ≠ ⊥)
    (hdisp : ∀ f ∈ ⁅G, G⁆, f ≠ 1 → ∃ U U₁ : Set α, ∃ Small : Set α → Prop,
      Disjoint (f '' U) U ∧ ThreeRoom G U U₁ ∧ Compressible G U₁ Small ∧ Fragments G Small) :
    IsSimpleGroup ↥⁅G, G⁆ := by
  have hnt : Nontrivial ↥⁅G, G⁆ := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨⟨f, hfM⟩, hfH⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext (Subtype.ext h))
  have hNnorm : ∀ n ∈ H.map ⁅G, G⁆.subtype, ∀ g ∈ ⁅G, G⁆,
      g * n * g⁻¹ ∈ H.map ⁅G, G⁆.subtype := by
    rintro n ⟨x, hxH, rfl⟩ g hg
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hH.conj_mem x hxH ⟨g, hg⟩, rfl⟩
  have hfN : f ∈ H.map ⁅G, G⁆.subtype := ⟨⟨f, hfM⟩, hfH, rfl⟩
  obtain ⟨U, U₁, Small, hU, hroom, hcomp, hfrag⟩ := hdisp f hfM hf1'
  have hle := commutator_le_of_room_fragments G (H.map ⁅G, G⁆.subtype) hNnorm hfN hU hroom
    hcomp hfrag
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨y, hyH, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hyH

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isSimpleGroup_of_room_fragments

end GroupApproximation.BooneHigman.Metabelian.Envelope
