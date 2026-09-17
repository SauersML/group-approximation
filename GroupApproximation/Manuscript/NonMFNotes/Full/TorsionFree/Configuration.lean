import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Sofic.TorsionFreeFullMFRadical
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The torsion-free self-radical group: configuration and defect saturation

`non_mf_group_notes.tex`, Theorem `thm:torsionfree` (l.2757-2812), and
Remark `rem:ff-realization` (l.2814-2832).

The printed proof works inside the Fournier-Facio--Fournier-Facio group `G_0`,
which contains a Kazhdan subgroup `Γ`, a stable letter `t₁` and an embedded
simple group `S' ≤ Γ` with

`t₁ Γ t₁⁻¹ ⊆ Γ` and `t₁⁻¹ S' t₁ ⊆ C_{G_0}(Γ)`.

This file formalizes every step of that proof that does not depend on how
`G_0` and the routed quotient `q : G_0 ↠ G` are produced.

* `map_commutator_mem_printedDefect` is the displayed computation
  `[s, ℓ] = [t₁ z t₁⁻¹, ℓ] ∈ 𝔇(G, L)`. It is proved after an arbitrary
  homomorphism `ρ`, which is the printed "the relations above descend to
  `L = q(Γ)`".
* `map_le_printedDefect_of_simple` gives `q(S') ≤ 𝔇(G, L)`. The printed proof
  uses perfectness of `S'`. Here the proof uses normality of the pulled-back
  defect in the simple group `S'`, together with one noncommuting pair.
* `map_normalClosure_le_printedDefect`: the image of `⟨⟨S'⟩⟩` lies in the
  defect, by normality.
* `NotesConfiguration` records the configuration, and
  `NotesConfiguration.toFournierFacioDefectData` inhabits
  `FournierFacioDefectData` from it.
* `NotesConfiguration.selfRadical_of_routedQuotient` is the closing paragraph
  of the proof. Given a surjection onto a torsion-free group in which the image
  of `⟨⟨S'⟩⟩` is everything and a nonidentity element of `S'` survives, the
  quotient is nontrivial, torsion-free, Kazhdan, and equal to its own actual
  corona MF residual. The last clause comes from
  `normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect`
  (`cor:intrinsic-nk`).
-/

namespace GroupApproximation.Full.NN07b

open scoped commutatorElement
open GroupApproximation.Manuscript.OneSidedMFRadical

/-! ## The commutator calculation and its image under a homomorphism -/

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2776-2782 and l.2800-2805):
if `t Γ t⁻¹ ⊆ Γ` and `z = t⁻¹ s t` centralizes `Γ`, then for every `ℓ ∈ Γ` and
every homomorphism `ρ`, `[ρ s, ρ ℓ] ∈ 𝔇(ρ Γ)`. -/
theorem map_commutator_mem_printedDefect {G₀ L : Type} [Group G₀] [Group L]
    (Γ : Subgroup G₀) (t : G₀) (ht : ∀ δ ∈ Γ, t * δ * t⁻¹ ∈ Γ)
    {s : G₀} (hs : ∀ δ ∈ Γ, Commute (t⁻¹ * s * t) δ) {ℓ : G₀} (hℓ : ℓ ∈ Γ)
    (ρ : G₀ →* L) :
    ⁅ρ s, ρ ℓ⁆ ∈ printedDefect (Γ.map ρ) := by
  have hu : ∀ δ ∈ Γ.map ρ, ρ t * δ * (ρ t)⁻¹ ∈ Γ.map ρ := by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hδ
    have h := Subgroup.mem_map_of_mem ρ (ht γ hγ)
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hc : ∀ δ ∈ Γ.map ρ, Commute (ρ (t⁻¹ * s * t)) δ := by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hδ
    exact (hs γ hγ).map ρ
  have hmem :=
    printedDefect_generator_mem (Γ.map ρ) hu hc (Subgroup.mem_map_of_mem ρ hℓ)
  have heq : ρ t * ρ (t⁻¹ * s * t) * (ρ t)⁻¹ = ρ s := by
    simp only [map_mul, map_inv]
    group
  rw [heq] at hmem
  exact hmem

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2782-2784 and l.2805):
the image of the simple subgroup `S'` lies in the printed defect of the image
of `Γ`. One nontrivial commutator in `S'` is enough, by simplicity. -/
theorem map_le_printedDefect_of_simple {G₀ L : Type} [Group G₀] [Group L]
    (Γ : Subgroup G₀) (t : G₀) (ht : ∀ δ ∈ Γ, t * δ * t⁻¹ ∈ Γ)
    (S : Subgroup G₀) [IsSimpleGroup S] (hSΓ : S ≤ Γ)
    (hS : ∀ s ∈ S, ∀ δ ∈ Γ, Commute (t⁻¹ * s * t) δ)
    {a b : G₀} (ha : a ∈ S) (hb : b ∈ S) (hab : ⁅a, b⁆ ≠ 1)
    (ρ : G₀ →* L) :
    S.map ρ ≤ printedDefect (Γ.map ρ) := by
  let N : Subgroup S :=
    ((printedDefect (Γ.map ρ)).comap ρ).comap S.subtype
  letI : N.Normal := inferInstance
  have hcomm_mem : ⁅a, b⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  let x : S := ⟨⁅a, b⁆, hcomm_mem⟩
  have hxN : x ∈ N := by
    change ρ ⁅a, b⁆ ∈ printedDefect (Γ.map ρ)
    rw [map_commutatorElement]
    exact map_commutator_mem_printedDefect Γ t ht (hS a ha) (hSΓ hb) ρ
  have hxne : x ≠ 1 := by
    intro hx
    exact hab (congrArg Subtype.val hx)
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance with
      hNbot | hNtop
    · exfalso
      have hxone : x = 1 := Subgroup.mem_bot.mp (hNbot ▸ hxN)
      exact hxne hxone
    · exact hNtop
  rw [Subgroup.map_le_iff_le_comap]
  intro y hy
  have hyN : (⟨y, hy⟩ : S) ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top _
  exact hyN

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2805-2806): the image of
`N = ⟨⟨S'⟩⟩` lies in the printed defect `𝔇(G, L)`, because the defect is
normal. -/
theorem map_normalClosure_le_printedDefect {G₀ L : Type} [Group G₀] [Group L]
    (Γ : Subgroup G₀) (t : G₀) (ht : ∀ δ ∈ Γ, t * δ * t⁻¹ ∈ Γ)
    (S : Subgroup G₀) [IsSimpleGroup S] (hSΓ : S ≤ Γ)
    (hS : ∀ s ∈ S, ∀ δ ∈ Γ, Commute (t⁻¹ * s * t) δ)
    {a b : G₀} (ha : a ∈ S) (hb : b ∈ S) (hab : ⁅a, b⁆ ≠ 1)
    (ρ : G₀ →* L) :
    (Subgroup.normalClosure (S : Set G₀)).map ρ ≤ printedDefect (Γ.map ρ) := by
  have hS_le : S ≤ (printedDefect (Γ.map ρ)).comap ρ :=
    Subgroup.map_le_iff_le_comap.mp
      (map_le_printedDefect_of_simple Γ t ht S hSΓ hS ha hb hab ρ)
  rw [Subgroup.map_le_iff_le_comap]
  apply Subgroup.normalClosure_le_normal
  intro y hy
  exact hS_le hy

/-! ## The configuration inside `G_0` -/

/-- The configuration that `thm:torsionfree` (`non_mf_group_notes.tex`,
l.2767-2775) reads off the construction of `[FFF, Section 2]`. It consists of
a countable torsion-free Kazhdan group `G₀`, a Kazhdan subgroup `Γ`, a stable
letter `t` with `t Γ t⁻¹ ⊆ Γ`, and a simple subgroup `S ≤ Γ` whose
`t`-conjugate centralizes `Γ`. The pair `a, b ∈ S` with `[a, b] ≠ 1` records
that `S` is nonabelian. -/
structure NotesConfiguration where
  /-- The group `G_0`. -/
  G₀ : Type
  /-- Its group structure. -/
  [group : Group G₀]
  /-- `G_0` is countable (it is finitely generated). -/
  [countable : Countable G₀]
  /-- `G_0` is torsion-free. -/
  torsionFree : IsPowerTorsionFree G₀
  /-- `G_0` has property (T). -/
  kazhdan : HasKazhdanPropertyT.{0, 0} G₀
  /-- The Kazhdan subgroup `Γ`. -/
  Γ : Subgroup G₀
  /-- `Γ` has property (T). -/
  kazhdanΓ : HasKazhdanPropertyT.{0, 0} ↥Γ
  /-- The stable letter `t₁`. -/
  t : G₀
  /-- `t₁ Γ t₁⁻¹ ⊆ Γ`. -/
  compresses : ∀ δ ∈ Γ, t * δ * t⁻¹ ∈ Γ
  /-- The embedded simple group `S'`. -/
  S : Subgroup G₀
  /-- `S'` is simple. -/
  [simple : IsSimpleGroup S]
  /-- `S' ≤ Γ`. -/
  S_le : S ≤ Γ
  /-- `t₁⁻¹ S' t₁ ⊆ C_{G_0}(Γ)`. -/
  centralizes : ∀ s ∈ S, ∀ δ ∈ Γ, Commute (t⁻¹ * s * t) δ
  /-- First element of a noncommuting pair in `S'`. -/
  a : G₀
  /-- Second element of a noncommuting pair in `S'`. -/
  b : G₀
  /-- `a ∈ S'`. -/
  a_mem : a ∈ S
  /-- `b ∈ S'`. -/
  b_mem : b ∈ S
  /-- `[a, b] ≠ 1`. -/
  commutator_ne_one : ⁅a, b⁆ ≠ 1

attribute [instance] NotesConfiguration.group NotesConfiguration.countable
  NotesConfiguration.simple

namespace NotesConfiguration

variable (C : NotesConfiguration)

/-- The protected element `a` of `S'` is not the identity. -/
theorem a_ne_one : C.a ≠ 1 := by
  intro h
  apply C.commutator_ne_one
  rw [h, commutatorElement_one_left]

/-- `thm:torsionfree` gives `S' ≤ 𝔇(G_0, Γ)` (l.2783-2784). -/
theorem S_le_printedDefect : C.S ≤ printedDefect C.Γ := by
  have h := map_le_printedDefect_of_simple C.Γ C.t C.compresses C.S C.S_le
    C.centralizes C.a_mem C.b_mem C.commutator_ne_one (MonoidHom.id C.G₀)
  rw [Subgroup.map_id, Subgroup.map_id] at h
  exact h

/-- Milestone 2 of lane L7: the configuration of `thm:torsionfree` inhabits
the development's `FournierFacioDefectData`. The base is `Γ` itself, the
compressor is `t`, the selected element is `a`, and the witness is `b`. -/
def toFournierFacioDefectData : FournierFacioDefectData ↥C.Γ C.G₀ where
  iota := C.Γ.subtype
  u := C.t
  s := C.a
  kazhdan := C.kazhdanΓ
  compresses p := ⟨⟨C.t * (p : C.G₀) * C.t⁻¹, C.compresses p p.2⟩, rfl⟩
  commutesAfterCompression p := by
    have h := (C.centralizes C.a C.a_mem p p.2).eq
    show C.a * (C.t * (p : C.G₀) * C.t⁻¹) = (C.t * (p : C.G₀) * C.t⁻¹) * C.a
    calc C.a * (C.t * (p : C.G₀) * C.t⁻¹)
        = C.t * ((C.t⁻¹ * C.a * C.t) * (p : C.G₀)) * C.t⁻¹ := by group
      _ = C.t * ((p : C.G₀) * (C.t⁻¹ * C.a * C.t)) * C.t⁻¹ := by rw [h]
      _ = (C.t * (p : C.G₀) * C.t⁻¹) * C.a := by group
  simpleSubgroup := C.S
  simple := C.simple
  s_mem := C.a_mem
  witness := ⟨C.b, C.S_le C.b_mem⟩
  witness_mem := C.b_mem
  witness_commutator_ne_one := C.commutator_ne_one

/-! ## The closing paragraph of `thm:torsionfree` -/

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2795-2812). Let
`q : G_0 ↠ Q` be a surjection onto a torsion-free group such that
`q(⟨⟨S'⟩⟩) = Q` (Hull Theorem 7.1(c)) and the protected element `a ∈ S'`
survives. Then `Q` is nontrivial, torsion-free and Kazhdan, and it equals its
own actual corona MF residual. -/
theorem selfRadical_of_routedQuotient {Q : Type} [Group Q]
    (q : C.G₀ →* Q) (hq : Function.Surjective q) (hQ : IsPowerTorsionFree Q)
    (hgen : (Subgroup.normalClosure (C.S : Set C.G₀)).map q = ⊤)
    (ha : q C.a ≠ 1) :
    Nontrivial Q ∧ IsPowerTorsionFree Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      actualCoronaMFResidual Q = ⊤ := by
  letI : Countable Q := hq.countable
  have hGT : HasKazhdanPropertyT.{0, 0} Q :=
    HasKazhdanPropertyT.of_surjective q hq C.kazhdan
  have hLT : HasKazhdanPropertyT.{0, 0} ↥(C.Γ.map q) :=
    HasKazhdanPropertyT.of_surjective (q.subgroupMap C.Γ)
      (q.subgroupMap_surjective C.Γ) C.kazhdanΓ
  have hTop : HasKazhdanPropertyT.{0, 0} ↥(⊤ : Subgroup Q) :=
    HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv hGT
  have hKD : (⊤ : Subgroup Q) ≤ printedDefect (C.Γ.map q) := by
    rw [← hgen]
    exact map_normalClosure_le_printedDefect C.Γ C.t C.compresses C.S C.S_le
      C.centralizes C.a_mem C.b_mem C.commutator_ne_one q
  refine ⟨⟨⟨q C.a, 1, ha⟩⟩, hQ, hGT, ?_⟩
  exact top_unique
    (normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
      (C.Γ.map q) hLT ⊤ hTop hKD)

/-- The existential form of `thm:torsionfree`, reached from a configuration and
a routed quotient. -/
theorem exists_selfRadical_of_routedQuotient {Q : Type} [Group Q]
    (q : C.G₀ →* Q) (hq : Function.Surjective q) (hQ : IsPowerTorsionFree Q)
    (hgen : (Subgroup.normalClosure (C.S : Set C.G₀)).map q = ⊤)
    (ha : q C.a ≠ 1) :
    ∃ (G : Type) (_ : Group G), Nontrivial G ∧ IsPowerTorsionFree G ∧
      HasKazhdanPropertyT.{0, 0} G ∧ actualCoronaMFResidual G = ⊤ :=
  ⟨Q, inferInstance, C.selfRadical_of_routedQuotient q hq hQ hgen ha⟩

/-- The degenerate routing, where `S'` already normally generates `G_0`.
In that case `G_0` itself equals its own actual corona MF residual. -/
theorem selfRadical_of_normalClosure_eq_top
    (hgen : Subgroup.normalClosure (C.S : Set C.G₀) = ⊤) :
    Nontrivial C.G₀ ∧ IsPowerTorsionFree C.G₀ ∧
      HasKazhdanPropertyT.{0, 0} C.G₀ ∧ actualCoronaMFResidual C.G₀ = ⊤ := by
  have hsurj : Function.Surjective (MonoidHom.id C.G₀) := fun y => ⟨y, rfl⟩
  have hgen' :
      (Subgroup.normalClosure (C.S : Set C.G₀)).map (MonoidHom.id C.G₀) = ⊤ := by
    rw [Subgroup.map_id]
    exact hgen
  exact C.selfRadical_of_routedQuotient (MonoidHom.id C.G₀) hsurj C.torsionFree
    hgen' C.a_ne_one

end NotesConfiguration

end GroupApproximation.Full.NN07b
