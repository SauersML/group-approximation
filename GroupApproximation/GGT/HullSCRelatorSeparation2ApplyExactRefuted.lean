import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyExact
import GroupApproximation.GGT.HullSCRelatorSeparation2Component
import GroupApproximation.GGT.HullSCRelatorSeparation2Inputs
import GroupApproximation.GGT.HullSCRelatorSeparation2Span

/-!
# The exact-design side-exclusion interface is still over-quantified

Restricting the old side-exclusion premise to the jointly chosen exponent list
removes its degenerate-list counterexample, but it does not repair the index
binders.  The superseded `RelatorSideExclusionAtUnrestricted₂` asks for the
exclusion for every index `d`;
it only requires the other index `i'` to start a component.  Taking `d = i' + 1`
makes the prohibited span the inverse of the component letter at `i'`, which is
in the same peripheral subgroup.

The theorem below records the counterexample for every one-base-letter
alternating relator with at least two block letters.  In particular no finite
avoidance property of the exponent list can imply that predicate.  The active
`RelatorSideExclusionAt₂` repairs it by requiring `d` (and the oppositely
oriented anchor `k`) to bound the component actually supplied at the geometric
call site.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Append

variable {G : Type u} [Group G] {Λ : Type v}

omit [Group G] in
/-- A component whose right endpoint is strictly inside a prefix remains a
component after an arbitrary suffix is appended. -/
theorem isComp_append_of_lt {lam : Λ} {q r : List (GGT.RelLetter G Λ)}
    {i k : ℕ} (h : GGT.OsinComponents.IsComp lam q i k)
    (hk : k < q.length) :
    GGT.OsinComponents.IsComp lam (q ++ r) i k := by
  rcases h with ⟨hik, hkq, hrange, hpre, hpost⟩
  refine ⟨hik, by simp; omega, ?_, ?_, ?_⟩
  · intro j hij hjk hjqr
    have hjq : j < q.length := by omega
    rw [List.getElem_append_left hjq]
    exact hrange j hij hjk hjq
  · intro j hij hjqr
    have hjq : j < q.length := by omega
    rw [List.getElem_append_left hjq]
    exact hpre j hij hjq
  · intro hkqr
    rw [List.getElem_append_left hk]
    exact hpost hk

end Append

section Refutation

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- The repaired-to-one-list side exclusion remains false: its universally
quantified first index may be the endpoint of the component starting at the
second index. -/
theorem not_relatorSideExclusionAtUnrestricted₂_one_of_two_le
    (E : HypEmbeddedCore₂ A N) (baseLetter : G) (ms : List ℕ)
    (hms : 2 ≤ ms.length) :
    ¬ RelatorSideExclusionAtUnrestricted₂ E [baseLetter] ms := by
  obtain ⟨m₀, m₁, tail, rfl⟩ : ∃ m₀ m₁ tail, ms = m₀ :: m₁ :: tail := by
    cases ms with
    | nil => simp at hms
    | cons m₀ rest =>
        cases rest with
        | nil => simp at hms
        | cons m₁ tail => exact ⟨m₀, m₁, tail, rfl⟩
  let q := relatorWord₂ [baseLetter] (E.lox false) (E.lox true)
    (m₀ :: m₁ :: tail)
  have hfirst :
      (blockWord (E.lox false) (E.lox true) false (m₀ :: m₁ :: tail))[0]?
        = some (GGT.RelLetter.comp false (E.lox false ^ m₀)) := by
    simp [blockWord_cons]
  have hcompq : GGT.OsinComponents.IsComp false q 1 2 := by
    simpa only [q, List.length_singleton, Nat.add_zero, Nat.add_comm,
      Nat.zero_add] using
      (isComp_relatorWord₂ [baseLetter] (E.lox false) (E.lox true)
        (m₀ :: m₁ :: tail) (by simp) hfirst)
  have hqlen : q.length = 1 + (m₀ :: m₁ :: tail).length := by
    exact length_relatorWord₂ [baseLetter] (E.lox false) (E.lox true)
      (m₀ :: m₁ :: tail)
  have hcompWhole : GGT.OsinComponents.IsComp false
      (q ++ GGT.OsinComponents.revWord q) 1 2 :=
    isComp_append_of_lt hcompq (by rw [hqlen]; simp; omega)
  have hstart : GGT.OsinComponents.IsCompStart false
      ([] ++ q ++ [] ++ GGT.OsinComponents.revWord q) 1 := by
    simpa using (show GGT.OsinComponents.IsCompStart false
      (q ++ GGT.OsinComponents.revWord q) 1 from ⟨2, hcompWhole⟩)
  have hqget : q[1]? =
      some (GGT.RelLetter.comp false (E.lox false ^ m₀)) := by
    simpa only [q, List.length_singleton, Nat.add_zero] using
      (relatorWord₂_getElem?_block [baseLetter] (E.lox false) (E.lox true)
        (m₀ :: m₁ :: tail) 0).trans hfirst
  have hspan :
      (GGT.OsinComponents.vertex (1 : G) q 1)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q 2 = E.lox false ^ m₀ := by
    have h := span_eq_val_of_getElem? (v := (1 : G)) hqget
    change (GGT.OsinComponents.vertex (1 : G) q 1)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) q 2 = E.lox false ^ m₀ at h
    exact h
  have hforward :
      (GGT.OsinComponents.vertex (1 : G) q 1)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q 2 ∈ E.rel.fam false := by
    rw [hspan, E.fam_eq]
    exact pow_mem (E.lox_mem false) m₀
  have hbackward :
      (GGT.OsinComponents.vertex (1 : G) q 2)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q 1 ∈ E.rel.fam false := by
    have hinv := inv_mem hforward
    rw [show (GGT.OsinComponents.vertex (1 : G) q 2)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q 1 =
      ((GGT.OsinComponents.vertex (1 : G) q 1)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q 2)⁻¹ by group]
    exact hinv
  intro hexcl
  have h := hexcl [] [] q q
    ⟨q, [], RelWord.Sym.base, by simp⟩
    ⟨q, [], RelWord.Sym.base, by simp⟩
    (by simp) (by simp)
  exact (h.1 false 2 1 (by rw [hqlen]; simp) (by omega) hstart) hbackward

end Refutation

end HullSC
end GroupApproximation
