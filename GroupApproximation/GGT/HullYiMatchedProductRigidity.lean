import GroupApproximation.GGT.ElementaryClosure

/-!
# The algebra after Hull's consecutive-component match

In Hull's proof of Lemma 5.6, DGO Lemma 4.21(b) supplies one full cyclic run
of matched peripheral components.  If `cᵢ` is the label of the connector at
the start of the `i`-th component, the endpoint connector is
`aᵢ⁻¹ cᵢ aᵢ`.  The hypotheses `E(fᵢ) = C_G(aᵢ)` and `cᵢ ∈ E(fᵢ)` therefore
make consecutive connector labels equal.  One trip around the detecting
family puts their common value in every `E(fᵢ)`, hence in the loxodromic
radical.

This file proves exactly that post-matching algebra.  It does not assume DGO
Lemma 4.21(b), a component-matching proposition, or a product-word theorem:
the local connector equations are its data, and all conclusions below are
ordinary group theory.  In the suitable case the detected radical is trivial,
so Hull's prefix calculation leaves only a power of the product word.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.Elementary

universe u

variable {G : Type u} [Group G]

/-- **Connector propagation around one matched cyclic run.**

`c i.castSucc` is the connector at the start of the component labelled by
`a i`, and `c i.succ` is its endpoint connector.  Membership in `E i` and the
centralizer condition make those two connectors equal.  Consequently the
first connector belongs to every `E i`; a trivial total intersection makes
every connector trivial. -/
theorem matchedConnectors_eq_one {k : ℕ} (hk : 0 < k)
    (E : Fin k → Subgroup G) (a : Fin k → G) (c : Fin (k + 1) → G)
    (hcentral : ∀ i : Fin k, ∀ x : G, x ∈ E i → Commute x (a i))
    (hmem : ∀ i : Fin k, c i.castSucc ∈ E i)
    (hnext : ∀ i : Fin k,
      c i.succ = (a i)⁻¹ * c i.castSucc * a i)
    (hinter : ∀ x : G, (∀ i : Fin k, x ∈ E i) → x = 1) :
    ∀ j : Fin (k + 1), c j = 1 := by
  have hstep : ∀ i : Fin k, c i.succ = c i.castSucc := by
    intro i
    have hcomm : Commute (c i.castSucc) (a i) :=
      hcentral i (c i.castSucc) (hmem i)
    calc
      c i.succ = (a i)⁻¹ * c i.castSucc * a i := hnext i
      _ = (a i)⁻¹ * (c i.castSucc * a i) := by group
      _ = (a i)⁻¹ * (a i * c i.castSucc) := by rw [hcomm.eq]
      _ = c i.castSucc := by group
  have hconst : ∀ j : Fin (k + 1), c j = c ⟨0, by omega⟩ := by
    intro j
    refine Fin.induction rfl ?_ j
    intro i hi
    exact (hstep i).trans hi
  have hc0 : c ⟨0, by omega⟩ = 1 := by
    apply hinter
    intro i
    rw [← hconst i.castSucc]
    exact hmem i
  intro j
  exact (hconst j).trans hc0

/-- The form used in `yi`: `E(fᵢ)` is literally the centralizer of `aᵢ`.
The theorem above only needs the forward implication, so this adapter keeps
the equality at the source-facing boundary. -/
theorem matchedElementaryConnectors_eq_one {k : ℕ} (hk : 0 < k)
    (f a : Fin k → G) (c : Fin (k + 1) → G)
    (hcentral : ∀ i : Fin k,
      (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (a i)})
    (hmem : ∀ i : Fin k, c i.castSucc ∈ elementaryClosure (f i))
    (hnext : ∀ i : Fin k,
      c i.succ = (a i)⁻¹ * c i.castSucc * a i)
    (hinter : ∀ x : G,
      (∀ i : Fin k, x ∈ elementaryClosure (f i)) → x = 1) :
    ∀ j : Fin (k + 1), c j = 1 := by
  apply matchedConnectors_eq_one hk (fun i => elementaryClosure (f i)) a c
  · intro i x hx
    exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp (hcentral i) x).mp hx)
  · exact hmem
  · exact hnext
  · exact hinter

/-- Connector propagation for two cyclic products which agree through their
first `k` letters.  The connector at the start of the final component is
trivial because the successive common-prefix connectors also lie in the
final peripheral subgroup.  No centralizer condition is needed for the last
letter, where the two products are allowed to differ. -/
theorem matchedCommonPrefixConnectors_eq_one {k : ℕ}
    (E : Fin (k + 1) → Subgroup G) (a b : Fin (k + 1) → G)
    (c : Fin (k + 2) → G)
    (hcommon : ∀ i : Fin k, b i.castSucc = a i.castSucc)
    (hcentral : ∀ i : Fin k, ∀ x : G,
      x ∈ E i.castSucc → Commute x (a i.castSucc))
    (hmem : ∀ i : Fin (k + 1), c i.castSucc ∈ E i)
    (hnext : ∀ i : Fin (k + 1),
      c i.succ = (a i)⁻¹ * c i.castSucc * b i)
    (hinter : ∀ x : G, (∀ i : Fin (k + 1), x ∈ E i) → x = 1) :
    ∀ j : Fin (k + 1), c j.castSucc = 1 := by
  let d : Fin (k + 1) → G := fun j ↦ c j.castSucc
  have hstep : ∀ i : Fin k, d i.succ = d i.castSucc := by
    intro i
    have hcomm : Commute (c i.castSucc.castSucc) (a i.castSucc) :=
      hcentral i (c i.castSucc.castSucc) (hmem i.castSucc)
    have hcommLeft := congrArg
      (fun z : G ↦ (a i.castSucc)⁻¹ * z) hcomm.eq
    change c i.castSucc.succ = c i.castSucc.castSucc
    calc
      c i.castSucc.succ =
          (a i.castSucc)⁻¹ * c i.castSucc.castSucc * b i.castSucc :=
        hnext i.castSucc
      _ = (a i.castSucc)⁻¹ * c i.castSucc.castSucc * a i.castSucc := by
        rw [hcommon i]
      _ = (a i.castSucc)⁻¹ *
          (c i.castSucc.castSucc * a i.castSucc) := by group
      _ = (a i.castSucc)⁻¹ *
          (a i.castSucc * c i.castSucc.castSucc) := hcommLeft
      _ = c i.castSucc.castSucc := by group
  have hconst : ∀ j : Fin (k + 1), d j = d 0 := by
    intro j
    refine Fin.induction rfl ?_ j
    intro i hi
    exact (hstep i).trans hi
  have hd0 : d 0 = 1 := by
    apply hinter
    intro i
    rw [← hconst i]
    exact hmem i
  intro j
  exact (hconst j).trans hd0

/-- The elementary-closure adapter for common-prefix propagation. -/
theorem matchedElementaryCommonPrefixConnectors_eq_one {k : ℕ}
    (f a b : Fin (k + 1) → G) (c : Fin (k + 2) → G)
    (hcommon : ∀ i : Fin k, b i.castSucc = a i.castSucc)
    (hcentral : ∀ i : Fin k,
      (elementaryClosure (f i.castSucc) : Set G) =
        {x : G | Commute x (a i.castSucc)})
    (hmem : ∀ i : Fin (k + 1),
      c i.castSucc ∈ elementaryClosure (f i))
    (hnext : ∀ i : Fin (k + 1),
      c i.succ = (a i)⁻¹ * c i.castSucc * b i)
    (hinter : ∀ x : G,
      (∀ i : Fin (k + 1), x ∈ elementaryClosure (f i)) → x = 1) :
    ∀ j : Fin (k + 1), c j.castSucc = 1 := by
  apply matchedCommonPrefixConnectors_eq_one
    (fun i ↦ elementaryClosure (f i)) a b c hcommon
  · intro i x hx
    exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp (hcentral i) x).mp hx)
  · exact hmem
  · exact hnext
  · exact hinter

/-- Hull's prefix calculation after the common connector has become trivial.
The two matched component runs begin after powers `hˡ`, `hᵐ` and the same
prefix `p`; cancelling that prefix leaves `hˡ⁻ᵐ`. -/
theorem eq_zpow_sub_of_prefix_connector_eq_one
    (h t p connector : G) (l m : ℤ) (hc : connector = 1)
    (ht : t = h ^ l * p * connector * p⁻¹ * h ^ (-m)) :
    t = h ^ (l - m) := by
  rw [ht, hc]
  simp only [mul_one]
  rw [zpow_sub]
  group

/-- The same prefix calculation, packaged as membership in the cyclic
subgroup generated by the product word. -/
theorem mem_zpowers_of_prefix_connector_eq_one
    (h t p connector : G) (l m : ℤ) (hc : connector = 1)
    (ht : t = h ^ l * p * connector * p⁻¹ * h ^ (-m)) :
    t ∈ Subgroup.zpowers h := by
  exact Subgroup.mem_zpowers_iff.mpr
    ⟨l - m,
      (eq_zpow_sub_of_prefix_connector_eq_one h t p connector l m hc ht).symm⟩

/-- **The complete post-matching cyclicity implication.**

The matching producer may choose different connector and prefix data for each
`t ∈ E(h)`.  Once it returns the source equations below, connector
propagation and the prefix calculation show `E(h) ≤ ⟨h⟩`; the reverse
inclusion is unconditional.  This is the exact algebraic endpoint consumed by
Hull's `yi` proof. -/
theorem elementaryClosure_eq_zpowers_of_matchedProduct
    {k : ℕ} (hk : 0 < k) (f a : Fin k → G) (h : G)
    (hcentral : ∀ i : Fin k,
      (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (a i)})
    (hinter : ∀ x : G,
      (∀ i : Fin k, x ∈ elementaryClosure (f i)) → x = 1)
    (hmatch : ∀ t : G, t ∈ elementaryClosure h →
      ∃ (l m : ℤ) (p : G) (c : Fin (k + 1) → G),
        (∀ i : Fin k, c i.castSucc ∈ elementaryClosure (f i)) ∧
        (∀ i : Fin k, c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
        t = h ^ l * p * c 0 * p⁻¹ * h ^ (-m)) :
    elementaryClosure h = Subgroup.zpowers h := by
  apply le_antisymm
  · intro t htE
    obtain ⟨l, m, p, c, hmem, hnext, ht⟩ := hmatch t htE
    have hc := matchedElementaryConnectors_eq_one hk f a c hcentral hmem hnext hinter
    exact mem_zpowers_of_prefix_connector_eq_one h t p (c 0) l m (hc 0) ht
  · exact zpowers_le_elementaryClosure h

end HullSC
end GroupApproximation
