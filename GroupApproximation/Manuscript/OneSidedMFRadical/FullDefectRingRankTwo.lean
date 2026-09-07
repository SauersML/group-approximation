import GroupApproximation.Leavitt.RankDescentEmbedding
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring` at every rank `n ≥ 2`

`notes/rank-two-descent-note-2026-09-07.md`, §4.

> `ρ : EL₂(R) → M` with `M` MF.  `ρ∘Ψ : EL₄(R) → M` is trivial by the
> rank-four theorem, so `ker ρ ∋ Ψ(e₁₂(1))`, whose normal closure is `EL₂(R)`.
> For `n ≥ 2` every root of `EL_n(R)` lies in an embedded `EL₂(R)`.

The printed theorem asks `n ≥ 4`.  This module drops the hypothesis to
`n ≥ 2`, which is the whole point of the note, and the drop costs no new
analysis: the rank-four theorem of `FullDefectRingUnconditional` is used as a
black box at `n = 4` and everything else is the ring calculation of
`Leavitt.RankDescentEmbedding`.

## How the two remaining ranks are reached

Rank two is the note's own argument.  Rank three needs one further step, since
the rank-four theorem does not apply there either: the block embedding
`EL₂(R) → EL_n(R)` on the first two coordinates carries `e₁₂(v₀)` to a root of
`EL_n(R)`, and `v₀` is unit-sandwiched by `w₀v₀ = 1`, so
`elementaryGroup_normal_eq_top_of_elementaryRoot_mem` finishes at every rank
`n ≥ 3` at once.  That route also re-derives the printed ranks `n ≥ 4`, so the
statement below is uniform in `n` rather than a case split visible to the
reader.

## What is *not* claimed

No priority is claimed for the rank-descent lemma; the note says so explicitly
and this module repeats it.  The property-`(T)` and strict-compression
statements keep their own rank requirements and are untouched here.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRankTwo

open RankDescent
open OneSidedCompressor

/-! ## The block embedding of `EL₂` on the first two coordinates -/

/-- `EL₂(R) → EL_{2+k}(R)`, stabilization followed by the standard
reindexing.  The first two coordinates of the target carry the image. -/
noncomputable def blockEmbed (R : Type*) [Ring R] (k : ℕ) :
    elementaryGroup (Fin 2) R →* elementaryGroup (Fin (2 + k)) R :=
  (elementaryReindexEquiv (R := R)
      (finSumFinEquiv : Fin 2 ⊕ Fin k ≃ Fin (2 + k))).toMonoidHom.comp
    (elementaryStabilization (ι := Fin 2) (κ := Fin k) (R := R))

theorem blockEmbed_ne (k : ℕ) :
    (finSumFinEquiv (Sum.inl (0 : Fin 2)) : Fin (2 + k))
      ≠ finSumFinEquiv (Sum.inl (1 : Fin 2)) :=
  finSumFinEquiv.injective.ne (Sum.inl_injective.ne (by decide))

theorem blockEmbed_upperRoot (R : Type*) [Ring R] (k : ℕ) (r : R) :
    blockEmbed R k (upperRoot r)
      = elementaryRoot (finSumFinEquiv (Sum.inl (0 : Fin 2)))
          (finSumFinEquiv (Sum.inl (1 : Fin 2))) (blockEmbed_ne k) r := by
  show elementaryReindexEquiv finSumFinEquiv
      (elementaryStabilization (elementaryRoot 0 1 (by decide) r)) = _
  rw [elementaryStabilization_elementaryRoot, elementaryReindexEquiv_elementaryRoot]

/-! ## The descent, at a fixed ring and a fixed target -/

/-- **§4.**  If every homomorphism from `EL₄(R)` to `M` is trivial, then so is
every homomorphism from `EL_n(R)` to `M`, for every `n ≥ 2`.

The hypotheses on the ring are the printed ones: a one-sided pair `ts = 1` and
a fullness witness for `e = 1 - st`.  Neither countability nor property `(T)`
nor anything about `M` beyond the rank-four conclusion enters. -/
theorem hom_eq_one_of_rankFour {R : Type} [Ring R] (s t : R) (hts : t * s = 1)
    {m : ℕ} (a b : Fin m → R) (hab : ∑ k, a k * (1 - s * t) * b k = 1)
    {M : Type} [Group M]
    (h4 : ∀ (f : elementaryGroup (Fin 4) R →* M)
      (x : elementaryGroup (Fin 4) R), f x = 1)
    (n : ℕ) (hn : 2 ≤ n) (f : elementaryGroup (Fin n) R →* M)
    (x : elementaryGroup (Fin n) R) : f x = 1 := by
  set P : OneSidedInverse R := ⟨s, t, hts⟩ with hP
  have hab' : ∑ k, a k * P.e * b k = 1 := hab
  set Q : ProperlyInfiniteUnit R := ofFull P a b hab' with hQ
  -- rank two, by the descent homomorphism and §2
  have h2 : ∀ (g : elementaryGroup (Fin 2) R →* M)
      (y : elementaryGroup (Fin 2) R), g y = 1 := by
    intro g y
    have hker : descent Q (elementaryRoot 0 1 (by decide) 1) ∈ g.ker :=
      h4 (g.comp (descent Q)) (elementaryRoot 0 1 (by decide) 1)
    have hle : Subgroup.normalClosure
        ({descent Q (elementaryRoot 0 1 (by decide) 1)} :
          Set (elementaryGroup (Fin 2) R)) ≤ g.ker :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hker)
    rw [normalClosure_descent_root_eq_top Q] at hle
    exact hle (Subgroup.mem_top y)
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · have hn2 : n = 2 := by omega
    subst hn2
    exact h2 f x
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hk : 1 ≤ k := by omega
    have hroot : blockEmbed R k (upperRoot (Q.v 0)) ∈ f.ker :=
      h2 (f.comp (blockEmbed R k)) (upperRoot (Q.v 0))
    rw [blockEmbed_upperRoot R k (Q.v 0)] at hroot
    have hcard : 3 ≤ Fintype.card (Fin (2 + k)) := by
      rw [Fintype.card_fin]
      omega
    have hsand : ∃ c d : R, c * Q.v 0 * d = 1 :=
      ⟨Q.w 0, 1, by rw [mul_one]; exact Q.w_mul_v_self 0⟩
    have htop : f.ker = ⊤ :=
      elementaryGroup_normal_eq_top_of_elementaryRoot_mem hcard f.ker
        (blockEmbed_ne k) hroot hsand
    have hx : x ∈ f.ker := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hx

/-! ## The printed statements at `n ≥ 2` -/

/-- **`thm:full-defect-ring` at every rank `n ≥ 2`.**

> Let `R` be a countable unital associative ring.  Suppose that `s,t ∈ R`
> satisfy `ts = 1`, `R(1-st)R = R`.  For every `n ≥ 2`, every homomorphism
> from `EL_n(R)` to an MF group is trivial.

The property-`(T)` theorem is a hypothesis of the theorems below, not of this
proposition. -/
def PrintedFullComplementaryIdempotentsRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 2 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M) (x : elementaryGroup (Fin n) R),
          f x = 1

/-- **The rank descent, as a reduction.**  The printed theorem at `n ≥ 4`
gives the printed theorem at `n ≥ 2`, with no further input. -/
theorem rankTwo_of_rankFour
    (h4 : FullDefectRing.PrintedFullComplementaryIdempotents) :
    PrintedFullComplementaryIdempotentsRankTwo := by
  intro R _ _ s t hts hfull n hn M _ hM f x
  obtain ⟨m, a, b, hab⟩ := hfull
  exact hom_eq_one_of_rankFour s t hts a b hab
    (fun g y ↦ h4 R s t hts ⟨m, a, b, hab⟩ 4 (by norm_num) M hM g y) n hn f x

/-- **`thm:full-defect-ring` at `n ≥ 2` in prime characteristic, with no
hypothesis at all.** -/
def PrintedFullComplementaryIdempotentsPrimeCharRankTwo : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Countable R] [CharP R p]
    (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∀ (n : ℕ), 2 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ (f : elementaryGroup (Fin n) R →* M)
            (x : elementaryGroup (Fin n) R), f x = 1

theorem manuscriptFullComplementaryIdempotentsPrimeCharRankTwo :
    PrintedFullComplementaryIdempotentsPrimeCharRankTwo := by
  intro p hp R _ _ _ s t hts hfull n hn M _ hM f x
  obtain ⟨m, a, b, hab⟩ := hfull
  refine hom_eq_one_of_rankFour s t hts a b hab (fun g y ↦ ?_) n hn f x
  exact FullDefectRing.manuscriptFullComplementaryIdempotentsPrimeCharUnconditional
    p hp R s t hts ⟨m, a, b, hab⟩ 4 (by norm_num) M hM g y

/-- **`thm:full-defect-ring` at `n ≥ 2` exactly as printed**, with the
Ershov--Jaikin-Zapirain theorem as its only hypothesis. -/
theorem manuscriptFullComplementaryIdempotentsRankTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedFullComplementaryIdempotentsRankTwo :=
  rankTwo_of_rankFour
    (FullDefectRing.manuscriptFullComplementaryIdempotentsFromEJZ hEJZ)

end FullDefectRankTwo
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms
  FullDefectRankTwo.manuscriptFullComplementaryIdempotentsPrimeCharRankTwo
