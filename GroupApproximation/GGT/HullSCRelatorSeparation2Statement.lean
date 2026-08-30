import GroupApproximation.GGT.HullSCRelatorSeparation2Core
import GroupApproximation.GGT.HullSCRelatorSeparationRepair

/-!
# Hull's §6 over two subgroups, from the corrected separation

`HullSC.HullRelatorStatement₂` is `HullSC.HullRelatorStatement` restated over
`HullSC.HypEmbeddedCore₂`, and `hullRelatorStatement₂_of_separationNe₂` proves
it from the separation with Olshanskii's exclusion clause `w' ≠ w` restored.

Two corrections are folded in at once.

* `w' ≠ w`, without which the statement is false on the diagonal
  (`GGT/HullSCRelatorSeparationRefuted.lean`).
* The alternating relator, without which the relator is not quasi-geodesic
  (`GGT/HullSCRelatorSeparationNotQG.lean`).

Everything except the separation is discharged here and none of it is a choice:
Hull's `u` is what the run names, and it lies in `N` because both subgroups do
(`HullSC.listVal_blockWord_mem`); admissibility and depth are read off the
letters one at a time; the length is whatever the exponent list gives; and `mu`
is met by taking the relator long, the estimate having produced its constant `B`
before the length.

`RelWord.IsSmallCancellation` and `RelWord.pieces_small_of_longMatch_ne` are
already stated for an arbitrary index type, so they are used here unchanged.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Statement

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- The two elements, selected by their index. -/
theorem ite_lox_eq (E : HypEmbeddedCore₂ A N) (b : Bool) :
    (if b then E.lox true else E.lox false) = E.lox b := by
  cases b <;> rfl

end Statement

/-- **Hull, §6, over two subgroups.**

> For every `eps, mu, rho` there is `u ∈ N` and a `C(eps, mu, rho)` family over
> `{H₀, H₁}` containing a word spelling `t⁻¹u`.

This is `HullSC.HullRelatorStatement` with the family Hull's proof actually
uses. -/
def HullRelatorStatement₂ : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N → ∀ (t : G)
      (eps rho : ℕ) (mu : ℝ), 0 < mu →
        ∃ u ∈ N, ∃ W : Set (List (GGT.RelLetter G Bool)),
          (∃ v ∈ W, GGT.RelLetter.listVal v = t⁻¹ * u) ∧
            RelWord.IsSmallCancellation E.rel W eps mu rho

/-- **Hull's §6 over two subgroups, once `t⁻¹` is a base letter.**

This is the faithful target for Hull's one-letter base part.  The core may
depend on `t`; `HullSC.HypEmbeddedCore₂.adjoinPair` constructs exactly that
core before this statement is invoked by the one-step seam. -/
def HullRelatorStatement₂OfBaseLetter : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N → ∀ (t : G),
      t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ) (mu : ℝ), 0 < mu →
        ∃ u ∈ N, ∃ W : Set (List (GGT.RelLetter G Bool)),
          (∃ v ∈ W, GGT.RelLetter.listVal v = t⁻¹ * u) ∧
            RelWord.IsSmallCancellation E.rel W eps mu rho

/-- **Hull's §6 over two subgroups, from Olshanskii's separation with the
exclusion clause.**

The hypothesis is the separation for the alternating relator, with `w' ≠ w`
restored; the conclusion is the form Hull's Theorem 5.1 consumes. -/
theorem hullRelatorStatement₂_of_separationNe₂
    (h : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G) (eps rho : ℕ), ∃ B : ℕ, ∀ L : ℕ,
          ∃ (p : List G) (ms : List ℕ),
            (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
              (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
                (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
              ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                  RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                    w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                      B < u₀.length →
                        ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                          wordNorm E.rel.base z ≤ eps →
                            GGT.RelLetter.listVal u₀'
                                = y * GGT.RelLetter.listVal u₀ * z →
                              GGT.RelLetter.listVal w'
                                = y * GGT.RelLetter.listVal w * y⁻¹) :
    HullRelatorStatement₂.{u} := by
  intro G _ A N E hN t eps rho mu hmu
  obtain ⟨B, hB⟩ := h A N E hN t eps rho
  obtain ⟨n, hn⟩ := exists_nat_gt ((B : ℝ) / mu)
  obtain ⟨p, ms, hpbase, hpprod, hlen, hdeep, hsep⟩ := hB (max rho n)
  have h1 : (B : ℝ) < (n : ℝ) * mu := by
    rw [div_lt_iff₀ hmu] at hn
    exact hn
  have h2 : (n : ℝ) ≤ ((max rho n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right rho n
  have hBL : (B : ℝ) < mu * ((max rho n : ℕ) : ℝ) := by
    have h3 : (n : ℝ) * mu ≤ ((max rho n : ℕ) : ℝ) * mu :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hmu)
    calc (B : ℝ) < (n : ℝ) * mu := h1
      _ ≤ ((max rho n : ℕ) : ℝ) * mu := h3
      _ = mu * ((max rho n : ℕ) : ℝ) := mul_comm _ _
  have hlenv : max rho n
      ≤ (relatorWord₂ p (E.lox false) (E.lox true) ms).length := by
    rw [length_relatorWord₂]
    omega
  have hBv : (B : ℝ)
      < mu * ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) := by
    have h4 : ((max rho n : ℕ) : ℝ)
        ≤ ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) := by
      exact_mod_cast hlenv
    have h5 : mu * ((max rho n : ℕ) : ℝ)
        ≤ mu * ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hmu)
    linarith [hBL, h5]
  have hbase : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base := E.base_inv
  have hfam : ∀ b : Bool, E.rel.fam b = E.H b := by
    intro b
    rw [E.fam_eq]
  have humem : GGT.RelLetter.listVal
      (blockWord (E.lox false) (E.lox true) false ms) ∈ N := by
    refine listVal_blockWord_mem E.le ?_ false ms
    intro b
    rw [ite_lox_eq E b]
    exact E.lox_mem b
  refine ⟨GGT.RelLetter.listVal (blockWord (E.lox false) (E.lox true) false ms),
    humem, RelWord.symmetrized (relatorWord₂ p (E.lox false) (E.lox true) ms),
    ⟨relatorWord₂ p (E.lox false) (E.lox true) ms,
      RelWord.self_mem_symmetrized _, ?_⟩, ?_⟩
  · rw [listVal_relatorWord₂, hpprod]
  · refine RelWord.isSmallCancellation_symmetrized_of_longMatch_ne hbase ?_ ?_ ?_
      hsep hBv
    · intro x hx
      rcases mem_relatorWord₂ hx with ⟨g, hg, rfl⟩ | ⟨b, m, _, rfl⟩
      · exact hpbase g hg
      · show (if b then E.lox true else E.lox false) ^ m ∈ E.rel.fam b
        rw [ite_lox_eq E b, hfam b]
        exact pow_mem (E.lox_mem b) m
    · have h6 : rho ≤ max rho n := Nat.le_max_left rho n
      omega
    · intro x hx lam hcomp
      rcases mem_relatorWord₂ hx with ⟨g, _, rfl⟩ | ⟨b, m, hm, rfl⟩
      · exact False.elim hcomp
      · have hbl : b = lam := hcomp
        rw [← hbl]
        show (if b then E.lox true else E.lox false) ^ m
            ∉ E.rel.relBall b rho ∧
          ((if b then E.lox true else E.lox false) ^ m)⁻¹
            ∉ E.rel.relBall b rho
        rw [ite_lox_eq E b]
        exact hdeep m hm b

/-- **The base-letter form of Hull's §6 from corrected separation.**

The proof is the same final small-cancellation assembly as the unrestricted
statement above.  Its separation producer is allowed to use the hypothesis
that `t⁻¹` is a letter of the current relative base. -/
theorem hullRelatorStatement₂OfBaseLetter_of_separationNe₂
    (h : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G), t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ),
          ∃ B : ℕ, ∀ L : ℕ,
            ∃ (p : List G) (ms : List ℕ),
              (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
                (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
                  (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
                ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                  RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                    RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                      w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                        B < u₀.length →
                          ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                            wordNorm E.rel.base z ≤ eps →
                              GGT.RelLetter.listVal u₀'
                                  = y * GGT.RelLetter.listVal u₀ * z →
                                GGT.RelLetter.listVal w'
                                  = y * GGT.RelLetter.listVal w * y⁻¹) :
    HullRelatorStatement₂OfBaseLetter.{u} := by
  intro G _ A N E hN t ht eps rho mu hmu
  obtain ⟨B, hB⟩ := h A N E hN t ht eps rho
  obtain ⟨n, hn⟩ := exists_nat_gt ((B : ℝ) / mu)
  obtain ⟨p, ms, hpbase, hpprod, hlen, hdeep, hsep⟩ := hB (max rho n)
  have h1 : (B : ℝ) < (n : ℝ) * mu := by
    rw [div_lt_iff₀ hmu] at hn
    exact hn
  have h2 : (n : ℝ) ≤ ((max rho n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right rho n
  have hBL : (B : ℝ) < mu * ((max rho n : ℕ) : ℝ) := by
    have h3 : (n : ℝ) * mu ≤ ((max rho n : ℕ) : ℝ) * mu :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hmu)
    calc (B : ℝ) < (n : ℝ) * mu := h1
      _ ≤ ((max rho n : ℕ) : ℝ) * mu := h3
      _ = mu * ((max rho n : ℕ) : ℝ) := mul_comm _ _
  have hlenv : max rho n
      ≤ (relatorWord₂ p (E.lox false) (E.lox true) ms).length := by
    rw [length_relatorWord₂]
    omega
  have hBv : (B : ℝ)
      < mu * ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) := by
    have h4 : ((max rho n : ℕ) : ℝ)
        ≤ ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) := by
      exact_mod_cast hlenv
    have h5 : mu * ((max rho n : ℕ) : ℝ)
        ≤ mu * ((relatorWord₂ p (E.lox false) (E.lox true) ms).length : ℝ) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hmu)
    linarith [hBL, h5]
  have hbase : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base := E.base_inv
  have hfam : ∀ b : Bool, E.rel.fam b = E.H b := by
    intro b
    rw [E.fam_eq]
  have humem : GGT.RelLetter.listVal
      (blockWord (E.lox false) (E.lox true) false ms) ∈ N := by
    refine listVal_blockWord_mem E.le ?_ false ms
    intro b
    rw [ite_lox_eq E b]
    exact E.lox_mem b
  refine ⟨GGT.RelLetter.listVal (blockWord (E.lox false) (E.lox true) false ms),
    humem, RelWord.symmetrized (relatorWord₂ p (E.lox false) (E.lox true) ms),
    ⟨relatorWord₂ p (E.lox false) (E.lox true) ms,
      RelWord.self_mem_symmetrized _, ?_⟩, ?_⟩
  · rw [listVal_relatorWord₂, hpprod]
  · refine RelWord.isSmallCancellation_symmetrized_of_longMatch_ne hbase ?_ ?_ ?_
      hsep hBv
    · intro x hx
      rcases mem_relatorWord₂ hx with ⟨g, hg, rfl⟩ | ⟨b, m, _, rfl⟩
      · exact hpbase g hg
      · show (if b then E.lox true else E.lox false) ^ m ∈ E.rel.fam b
        rw [ite_lox_eq E b, hfam b]
        exact pow_mem (E.lox_mem b) m
    · have h6 : rho ≤ max rho n := Nat.le_max_left rho n
      omega
    · intro x hx lam hcomp
      rcases mem_relatorWord₂ hx with ⟨g, _, rfl⟩ | ⟨b, m, hm, rfl⟩
      · exact False.elim hcomp
      · have hbl : b = lam := hcomp
        rw [← hbl]
        show (if b then E.lox true else E.lox false) ^ m
            ∉ E.rel.relBall b rho ∧
          ((if b then E.lox true else E.lox false) ^ m)⁻¹
            ∉ E.rel.relBall b rho
        rw [ite_lox_eq E b]
        exact hdeep m hm b

end HullSC
end GroupApproximation
