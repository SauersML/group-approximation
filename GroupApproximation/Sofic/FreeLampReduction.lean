import Mathlib.GroupTheory.PushoutI
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Tactic.Group

/-!
# Free-lamp amalgams

This file gives the algebraic construction and normal form for free-lamp
amalgams.  What is proved:

* the free-lamp amalgam `FreeLamp G Γ K`, built on Mathlib's `PushoutI`, with
  its two canonical embeddings `inAmbient` and `inLamp`;
* the centralizing relation: `inLamp k` commutes with `inAmbient g` for every
  `g ∈ Γ` (`inLamp_commute_inAmbient`);
* the normal-form nontriviality: the witness commutator `lampWitness t γ k`
  is nontrivial whenever `γ ∈ Γ`, `t⁻¹ γ t ∉ Γ`, and `k ≠ 1`
  (`lampWitness_ne_one`), through the reduced-word theorem for pushouts;
* countability of the amalgam from countability of its factors.
-/

namespace GroupApproximation

open Monoid

/-! ## The free-lamp amalgam -/

variable (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]

/-- The two factors of the free-lamp amalgam: the ambient group and the
lamp-augmented copy `Γ × K` of the amalgamation subgroup. -/
abbrev LampFactor : Bool → Type := fun b => bif b then G else ↥Γ × K

instance lampFactorGroup : ∀ b, Group (LampFactor G Γ K b)
  | true => inferInstanceAs (Group G)
  | false => inferInstanceAs (Group (↥Γ × K))

/-- The amalgamation maps: `Γ` into `G` by inclusion, and into `Γ × K` as the
first coordinate. -/
def lampMap : ∀ b, ↥Γ →* LampFactor G Γ K b
  | true => Γ.subtype
  | false => MonoidHom.inl ↥Γ K

@[simp]
theorem lampMap_true_apply (γ : ↥Γ) :
    lampMap G Γ K true γ = (γ : G) := rfl

@[simp]
theorem lampMap_false_apply (γ : ↥Γ) :
    lampMap G Γ K false γ = (γ, (1 : K)) := rfl

theorem lampMap_injective : ∀ b, Function.Injective (lampMap G Γ K b)
  | true => Γ.subtype_injective
  | false => fun _ _ hxy => congrArg Prod.fst hxy

/-- The free-lamp amalgam `G *_Γ (Γ × K)`.  Reducible, so that every use
elaborates against the pushout's own group structure. -/
abbrev FreeLamp : Type := PushoutI (lampMap G Γ K)

/-- The ambient group inside the amalgam. -/
def inAmbient : G →* FreeLamp G Γ K :=
  PushoutI.of (φ := lampMap G Γ K) true

/-- The lamp group inside the amalgam. -/
def inLamp : K →* FreeLamp G Γ K :=
  (PushoutI.of (φ := lampMap G Γ K) false).comp (MonoidHom.inr ↥Γ K)

@[simp] theorem inAmbient_apply (g : G) :
    inAmbient G Γ K g = PushoutI.of (φ := lampMap G Γ K) true g := rfl

@[simp] theorem inLamp_apply (k : K) :
    inLamp G Γ K k
      = PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k) := rfl

theorem inAmbient_injective : Function.Injective (inAmbient G Γ K) :=
  PushoutI.of_injective (lampMap_injective G Γ K) true

/-- **The lamp centralizes the amalgamation subgroup.**  The relation that
replaces all of the commuting-lamp structure of a wreath product. -/
theorem inLamp_commute_inAmbient (k : K) {g : G} (hg : g ∈ Γ) :
    Commute (inLamp G Γ K k) (inAmbient G Γ K g) := by
  have hbase : inAmbient G Γ K g
      = PushoutI.of (φ := lampMap G Γ K) false ((⟨g, hg⟩ : ↥Γ), (1 : K)) := by
    have h1 : inAmbient G Γ K g
        = PushoutI.of (φ := lampMap G Γ K) true
            (lampMap G Γ K true ⟨g, hg⟩) := rfl
    rw [h1, PushoutI.of_apply_eq_base,
      ← PushoutI.of_apply_eq_base (φ := lampMap G Γ K) false]
    rfl
  rw [inLamp_apply, hbase]
  have hcomm : Commute (((1 : ↥Γ), k) : ↥Γ × K) ((⟨g, hg⟩ : ↥Γ), (1 : K)) := by
    show ((1 : ↥Γ), k) * (⟨g, hg⟩, (1 : K))
      = ((⟨g, hg⟩ : ↥Γ), (1 : K)) * (1, k)
    simp
  exact hcomm.map (PushoutI.of (φ := lampMap G Γ K) false)

/-! ## The witness commutator and its nontriviality -/

/-- The witness: the commutator of the transported lamp `t k t⁻¹` against
`γ`. -/
def lampWitness (t γ : G) (k : K) : FreeLamp G Γ K :=
  (inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹)
    * inAmbient G Γ K γ
    * (inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹)⁻¹
    * (inAmbient G Γ K γ)⁻¹

/-- **The core nontriviality.**  If `s ∉ Γ` and `k ≠ 1`, the commutator of
`inLamp k` and `inAmbient s` is nontrivial: the four-letter word alternates
between the two factors with every letter outside the amalgamation image, so
the reduced-word theorem applies. -/
theorem lampCore_ne_one {s : G} (hs : s ∉ Γ) {k : K} (hk : k ≠ 1) :
    inLamp G Γ K k * inAmbient G Γ K s * (inLamp G Γ K k)⁻¹
      * (inAmbient G Γ K s)⁻¹ ≠ 1 := by
  classical
  intro hcon
  have hs1 : s ≠ 1 := fun h => by
    rw [h] at hs
    exact hs (one_mem Γ)
  set w : CoprodI.Word (LampFactor G Γ K) := {
    toList := [⟨false, ((1 : ↥Γ), k)⟩, ⟨true, s⟩,
      ⟨false, ((1 : ↥Γ), k⁻¹)⟩, ⟨true, s⁻¹⟩]
    ne_one := by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · intro h
        exact hk (congrArg Prod.snd h)
      · exact hs1
      · intro h
        exact hk (inv_eq_one.mp (congrArg Prod.snd h))
      · exact inv_ne_one.mpr hs1
    chain_ne := .cons_cons (by simp) (.cons_cons (by simp)
      (.cons_cons (by simp) (.singleton _))) } with hw
  have hred : PushoutI.Reduced (lampMap G Γ K) w := by
    intro l hl
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · rintro ⟨x, hx⟩
      exact hk ((congrArg Prod.snd hx : (1 : K) = k)).symm
    · rintro ⟨x, hx⟩
      apply hs
      have hx' : (x : G) = s := hx
      rw [← hx']
      exact x.2
    · rintro ⟨x, hx⟩
      exact hk (inv_eq_one.mp ((congrArg Prod.snd hx : (1 : K) = k⁻¹)).symm)
    · rintro ⟨x, hx⟩
      apply hs
      have hx' : (x : G) = s⁻¹ := hx
      have hmem : s⁻¹ ∈ Γ := by
        rw [← hx']
        exact x.2
      have h2 := inv_mem hmem
      rwa [inv_inv] at h2
  have e3 : PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k⁻¹)
      = (inLamp G Γ K k)⁻¹ := by
    rw [inLamp_apply]
    calc PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k⁻¹)
        = PushoutI.of (φ := lampMap G Γ K) false (((1 : ↥Γ), k)⁻¹) :=
          congrArg _ (by
            show (((1 : ↥Γ), k⁻¹) : ↥Γ × K) = (((1 : ↥Γ), k) : ↥Γ × K)⁻¹
            rw [Prod.inv_mk, inv_one])
      _ = (PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k))⁻¹ :=
          map_inv _ _
  have e4 : PushoutI.of (φ := lampMap G Γ K) true s⁻¹
      = (inAmbient G Γ K s)⁻¹ := map_inv _ _
  have hprod : PushoutI.ofCoprodI w.prod
      = inLamp G Γ K k * inAmbient G Γ K s * (inLamp G Γ K k)⁻¹
        * (inAmbient G Γ K s)⁻¹ := by
    simp only [hw, CoprodI.Word.prod, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, map_mul, PushoutI.ofCoprodI_of]
    rw [e3, e4, ← inLamp_apply, ← inAmbient_apply]
    simp only [mul_assoc]
  have hmem : PushoutI.ofCoprodI w.prod
      ∈ (PushoutI.base (lampMap G Γ K)).range := by
    rw [hprod, hcon]
    exact ⟨1, map_one _⟩
  have hempty := hred.eq_empty_of_mem_range (lampMap_injective G Γ K) hmem
  have hlist := congrArg CoprodI.Word.toList hempty
  simp [hw, CoprodI.Word.empty] at hlist

/-- **The witness is nontrivial** whenever `γ` escapes the compressed copy —
`t⁻¹ γ t ∉ Γ` — and the lamp is nontrivial.  Membership of `γ` in `Γ` is not
needed here; it is what makes the centralizer argument bite. -/
theorem lampWitness_ne_one {t γ : G} (hs : t⁻¹ * γ * t ∉ Γ)
    {k : K} (hk : k ≠ 1) : lampWitness G Γ K t γ k ≠ 1 := by
  intro hcon
  refine lampCore_ne_one G Γ K hs hk ?_
  have hconj : lampWitness G Γ K t γ k
      = inAmbient G Γ K t
        * (inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
            * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹)
        * (inAmbient G Γ K t)⁻¹ := by
    simp only [lampWitness, map_mul, map_inv]
    group
  rw [hconj] at hcon
  calc inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
        * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹
      = (inAmbient G Γ K t)⁻¹
          * (inAmbient G Γ K t
            * (inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
                * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹)
            * (inAmbient G Γ K t)⁻¹)
          * inAmbient G Γ K t := by group
    _ = 1 := by rw [hcon]; group

/-! ## Countability -/

instance lampFactorCountable [Countable G] [Countable K] :
    ∀ b, Countable (LampFactor G Γ K b)
  | true => inferInstanceAs (Countable G)
  | false => inferInstanceAs (Countable (↥Γ × K))

instance freeLampCountable [Countable G] [Countable K] :
    Countable (FreeLamp G Γ K) := by
  haveI h0 : Countable (FreeMonoid (Σ b, LampFactor G Γ K b)) :=
    inferInstanceAs (Countable (List (Σ b, LampFactor G Γ K b)))
  haveI h1 : Countable (CoprodI (LampFactor G Γ K)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable (FreeMonoid (CoprodI (LampFactor G Γ K) ⊕ ↥Γ)) :=
    inferInstanceAs (Countable (List (CoprodI (LampFactor G Γ K) ⊕ ↥Γ)))
  haveI h3 : Countable (Coprod (CoprodI (LampFactor G Γ K)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

end GroupApproximation
