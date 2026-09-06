import GroupApproximation.CharClass.ParityEvenFlagRelation
import GroupApproximation.CharClass.LIXChernValue

/-!
# `hsplit` for the LIX mapping torus

`hasSplitting_flag` gives the splitting principle for the Chern classes of a bundle
in the form `LerayHirschData.chern`, which lives in the ring.  `cc-lix-odd`'s
`lixChernOf` is the same class taken **degreewise** and pushed back into the ring,
because Step C speaks in a single graded piece.  The two differ by the round trip
`TotalH.of ∘ TotalH.component`, and this file shows the round trip is the identity
on a Chern class, so `WuStepDPinned.hsplit` is discharged.

## Why the round trip is the identity

Not by any degree bookkeeping on `chern`, which is a coefficient of a minimal
polynomial and carries no grading.  The splitting datum itself supplies it.  Its
`chern_split` field says that after pullback the `k`-th class is the `k`-th
elementary symmetric function of `r` classes of degree two, and *that* is visibly
concentrated in degree `2k`: it is a sum of products of `k` factors.  The pullback
is injective and commutes with taking components, so the class downstairs is
concentrated in degree `2k` as well.

So the argument runs through the splitting rather than around it, and needs
nothing from `cc-projective`'s degreewise layer.

## Main declarations

* `exists_prod_of_two`, `exists_esymmOn_of` — an elementary symmetric function of
  degree-two classes is concentrated in the doubled degree.
* `of_component_chern` — **the round trip is the identity** on a class with a
  splitting.
* `hasSplitting_congr`, `hasSplitting_of_component` — transport.
* `hasSplitting_lix` — **`hsplit` for the LIX mapping torus.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Wu

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. Classes concentrated in one degree -/

/-- Moving a class along an equality of degrees does not change the element of the
ring it names. -/
theorem of_congr_degree {X : TopCat.{0}} {m n : ℕ} (h : m = n) (a : TotalPiece X m) :
    TotalH.of X n (cohCast h a) = TotalH.of X m a := by
  subst h
  rw [cohCast_self]

/-- **A product of `B.card` classes of degree two is concentrated in degree
`2 * B.card`.**  The degree is taken as a parameter with an equation so that the
induction step needs no transport of the statement. -/
theorem exists_prod_of_two {F : TopCat.{0}} (g : ℕ → Hmod2 F 2) (B : Finset ℕ) :
    ∀ n : ℕ, 2 * B.card = n →
      ∃ c : Hmod2 F n, (∏ l ∈ B, TotalH.of F 2 (g l)) = TotalH.of F n c := by
  induction B using Finset.induction_on with
  | empty =>
      intro n hn
      rw [Finset.card_empty, Nat.mul_zero] at hn
      subst hn
      exact ⟨one F, by rw [Finset.prod_empty, TotalH.of_one]⟩
  | @insert b B hb ih =>
      intro n hn
      rw [Finset.card_insert_of_notMem hb] at hn
      obtain ⟨c, hc⟩ := ih (2 * B.card) rfl
      refine ⟨cohCast (by omega : 2 + 2 * B.card = n) (cup (g b) c), ?_⟩
      rw [Finset.prod_insert hb, hc, ← TotalH.of_mul]
      exact (of_congr_degree (by omega : 2 + 2 * B.card = n) (cup (g b) c)).symm

/-- A finite sum of classes concentrated in one degree is concentrated there. -/
theorem exists_sum_of {F : TopCat.{0}} {σ : Type} [DecidableEq σ] (n : ℕ)
    (f : σ → TotalH F) (t : Finset σ) :
    (∀ b ∈ t, ∃ c : Hmod2 F n, f b = TotalH.of F n c) →
      ∃ c : Hmod2 F n, (∑ b ∈ t, f b) = TotalH.of F n c := by
  induction t using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, by rw [Finset.sum_empty, map_zero]⟩
  | @insert b t hb ih =>
      intro hf
      obtain ⟨c₁, h₁⟩ := hf b (Finset.mem_insert_self b t)
      obtain ⟨c₂, h₂⟩ := ih fun x hx => hf x (Finset.mem_insert_of_mem hx)
      exact ⟨c₁ + c₂, by rw [Finset.sum_insert hb, h₁, h₂, map_add]⟩

/-- **The `k`-th elementary symmetric function of classes of degree two is
concentrated in degree `2k`.**  Every subset it sums over has exactly `k`
elements. -/
theorem exists_esymmOn_of {F : TopCat.{0}} (s : Finset ℕ) (g : ℕ → Hmod2 F 2) (a : ℕ) :
    ∃ c : Hmod2 F (2 * a),
      esymmOn s (fun l => TotalH.of F 2 (g l)) a = TotalH.of F (2 * a) c := by
  rw [esymmOn_def]
  refine exists_sum_of (2 * a) _ _ fun B hB => ?_
  exact exists_prod_of_two g B (2 * a) (by rw [(Finset.mem_powersetCard.mp hB).2])

/-- **An injective pullback detects concentration.**  If a class becomes
concentrated in degree `n` upstairs, it was concentrated in degree `n`
downstairs. -/
theorem of_component_eq_self_of_map {N F : TopCat.{0}} (proj : F ⟶ N)
    (hinj : Function.Injective (TotalH.map proj)) (n : ℕ) (z : TotalH N)
    (c : Hmod2 F n) (hz : TotalH.map proj z = TotalH.of F n c) :
    TotalH.of N n (TotalH.component N n z) = z := by
  refine hinj ?_
  rw [TotalH.map_of, ← totalH_component_map, hz, TotalH.component_of]

/-! ## 2. A Chern class with a splitting is concentrated -/

/-- **The round trip is the identity.**  A class that has a splitting is
concentrated in the degree its index names. -/
theorem of_component_chern {N : TopCat.{0}} {γ : ℕ → TotalH N} (H : HasSplitting N γ)
    (k : ℕ) : TotalH.of N (2 * k) (TotalH.component N (2 * k) (γ k)) = γ k := by
  obtain ⟨F, r, ⟨S⟩⟩ := H
  obtain ⟨c, hc⟩ := exists_esymmOn_of (Finset.range r) S.root k
  exact of_component_eq_self_of_map S.proj S.pull_injective (2 * k) (γ k) c
    ((S.chern_split k).trans hc)

/-- `HasSplitting` transports along a pointwise equality of the classes. -/
theorem hasSplitting_congr {N : TopCat.{0}} {γ δ : ℕ → TotalH N} (h : ∀ k, δ k = γ k)
    (H : HasSplitting N γ) : HasSplitting N δ := by
  obtain ⟨F, r, ⟨S⟩⟩ := H
  exact ⟨F, r, ⟨{ proj := S.proj
                  root := S.root
                  pull_injective := S.pull_injective
                  sq_one_root := S.sq_one_root
                  chern_split := fun k => by rw [h k]; exact S.chern_split k }⟩⟩

/-- The splitting survives the degreewise round trip, which is the shape
`lixChernOf` presents the classes in. -/
theorem hasSplitting_of_component {N : TopCat.{0}} (γ : ℕ → TotalH N)
    (H : HasSplitting N γ) :
    HasSplitting N (fun k => TotalH.of N (2 * k) (TotalH.component N (2 * k) (γ k))) :=
  hasSplitting_congr (fun k => of_component_chern H k) H

/-! ## 3. `hsplit` for the LIX mapping torus -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **`hsplit` for the LIX mapping torus.**  The bundle has constant rank
`lixRank dd` over a compact non-empty base, so `hasSplitting_flag` applies; the two
`lixChern` lemmas identify its Chern classes with `lixChernOf`'s, and
`of_component_chern` absorbs the degreewise round trip between them. -/
theorem hasSplitting_lix (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    HasSplitting (lixN dd)
      (lixChernOf (lixChern dd) (mappingTorus Vmat G circHoriz circHeight)) := by
  refine hasSplitting_congr (fun k => ?_)
    (hasSplitting_of_component _
      (hasSplitting_flag
        (⟨mappingTorus Vmat G circHoriz circHeight,
            continuous_mappingTorus_lix hGc,
            isStarProjection_mappingTorus_lix hGu⟩ :
          Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))
        (lixRank dd) (by simp [lixRank]) (fun x => rank_lixBundle G hGc hGu x)))
  rw [lixChernOf_mappingTorus (lixChern dd) hGc hGu k,
    lixChern_mappingTorus G hGc hGu (continuous_mappingTorus_lix hGc)
      (isStarProjection_mappingTorus_lix hGu) k]

end

end Wu
end CharClass
end GroupApproximation
