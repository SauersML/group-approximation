import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNarrow
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepFourGonOpposite

/-!
# Relative short sides in Hull's Proposition 5.3

Hull's `ε`-pieces use words in the whole alphabet `X ⊔ ⨆ H_λ`.  Thus the
two short sides of the comparison quadrilateral may themselves contain
peripheral letters.  The older separation bridge assumed those sides consisted
of base letters, which is not available for a published piece.

The first source-faithful replacement is local.  A component strictly inside
the long side cannot merge across either corner, regardless of the labels on
the short sides.  If its relative span is deeper than the isolated-component
bound, it is connected to another component of the quadrilateral.  At this
stage all four possible sides are retained; Hull Lemma 5.1(2)'s finite counting
argument is what will discard the two short-side branches for a long run of
components.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- If a singleton component of the fourth side is already known to start a
component of the whole quadrilateral, its whole-polygon component has the
same one-edge range.  The strict lower index keeps the comparison away from
the cyclic seam; maximality on the fourth side then supplies the far end. -/
theorem isComp_fourGon_of_isComp_opposite_of_start
    (p q r s : List (RelLetter G Λ)) (lam : Λ) {j : ℕ}
    (hj1 : 1 < j) (hj : j ≤ s.length)
    (hcomp : IsComp lam s (j - 1) j)
    (hstart : IsCompStart lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - j))) :
    IsComp lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - j))
      (p.length + q.length + r.length + (s.length - (j - 1))) := by
  obtain ⟨k, hk⟩ := hstart
  have hstep : s.length - (j - 1) = s.length - j + 1 := by omega
  have hkge :
      p.length + q.length + r.length + (s.length - j) + 1 ≤ k := by
    exact Nat.succ_le_of_lt hk.1
  have hkle : k ≤
      p.length + q.length + r.length + (s.length - j) + 1 := by
    by_contra hnot
    have hnot' : p.length + q.length + r.length + (s.length - j) + 1 < k :=
      Nat.lt_of_not_ge hnot
    have hslt : s.length - j + 1 < s.length := by omega
    have hglobal : p.length + q.length + r.length + (s.length - j) + 1 <
        (p ++ q ++ r ++ revWord s).length := by
      rw [length_fourGon]
      omega
    have hrevlt : s.length - j + 1 < (revWord s).length := by
      rw [length_revWord]
      omega
    have hidxEq : s.length - 1 - (s.length - j + 1) = j - 2 := by omega
    have hside : s.length - 1 - (s.length - j + 1) < s.length := by omega
    have hletter := hk.2.2.1
      (p.length + q.length + r.length + (s.length - j) + 1)
      (by omega) (by omega) hglobal
    rw [getElem_fourGon_revs p q r s hrevlt (by omega) hglobal,
      getElem_revWord s hrevlt hside, isCompOf_invLetter] at hletter
    have hprev := hcomp.2.2.2.1 (j - 2) (by omega) (by omega)
    exact hprev (by
      simpa only [hidxEq] using hletter)
  have hkEq : k = p.length + q.length + r.length + (s.length - j) + 1 := by
    omega
  rw [hkEq] at hk
  have hend : p.length + q.length + r.length + (s.length - (j - 1)) =
      p.length + q.length + r.length + (s.length - j) + 1 := by omega
  rw [hend]
  exact hk

omit [Group G] in
/-- Coordinate form of the finite absorption step.  The two short sides occupy
`m + n` polygon positions.  If every selected component has either such a
target or an opposite-side target, and equal short targets force equal source
components, then `m + n + 1` selected components force an opposite target. -/
theorem exists_opposite_of_short_positions_absorb
    {m n : ℕ} {Opposite : Fin (m + n + 1) → Prop}
    (target : Fin (m + n + 1) → ℕ)
    (hclass : ∀ i, target i < m + n ∨ Opposite i)
    (hshort : ∀ i j, target i < m + n → target j < m + n →
      target i = target j → i = j) :
    ∃ i, Opposite i := by
  by_contra hnot
  push Not at hnot
  have hlt : ∀ i, target i < m + n := by
    intro i
    rcases hclass i with hi | hi
    · exact hi
    · exact False.elim (hnot i hi)
  let owner : Fin (m + n + 1) → Fin (m + n) :=
    fun i => ⟨target i, hlt i⟩
  have hinj : Function.Injective owner := by
    intro i j hij
    apply hshort i j (hlt i) (hlt j)
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective owner hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Polygon form of finite absorption.  Each selected component is connected
to a distinct component somewhere in the quadrilateral.  Same-side targets
are excluded explicitly.  Since distinct selected components are not
connected, no component of either short side can absorb two of them; hence an
opposite-side target exists. -/
theorem exists_opposite_component_of_finite_absorption
    (H : Λ → Subgroup G) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (source : Fin (p.length + r.length + 1) → ℕ)
    (hpairwise : ∀ i j, i ≠ j →
      ¬ Connected H lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j))
    (htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      Connected H lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))))
    (hnotSame : ∀ i i', i' ≤ q.length → i' ≠ source i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') →
      ¬ Connected H lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + i')) :
    ∃ i n j, IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      Connected H lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      j ≤ s.length ∧
      n = p.length + q.length + r.length + (s.length - j) := by
  choose target htarget_ne htarget_start htarget_conn htarget_loc using htarget
  by_contra hnone
  push Not at hnone
  have hshort : ∀ i, target i < p.length ∨
      ∃ m : ℕ, m < r.length ∧
        target i = p.length + q.length + m := by
    intro i
    rcases htarget_loc i with hp | hq | hr | hs
    · exact Or.inl hp
    · obtain ⟨i', hi', heq⟩ := hq
      exfalso
      apply hnotSame i i' hi'
      · intro hieq
        apply htarget_ne i
        rw [heq, hieq]
      · rw [← heq]
        exact htarget_start i
      · rw [← heq]
        exact htarget_conn i
    · exact Or.inr hr
    · obtain ⟨j, hj, heq⟩ := hs
      exact False.elim (hnone i (target i) j (htarget_start i)
        (htarget_conn i) hj heq)
  have howner : ∀ i, ∃ a : Fin (p.length + r.length),
      (target i < p.length ∧ a.val = target i) ∨
        ∃ m : ℕ, m < r.length ∧
          target i = p.length + q.length + m ∧ a.val = p.length + m := by
    intro i
    rcases hshort i with hp | ⟨m, hm, heq⟩
    · exact ⟨⟨target i, by omega⟩, Or.inl ⟨hp, rfl⟩⟩
    · exact ⟨⟨p.length + m, by omega⟩,
        Or.inr ⟨m, hm, heq, rfl⟩⟩
  choose owner howner_spec using howner
  have howner_inj : Function.Injective owner := by
    intro i j hij
    have htarget_eq : target i = target j := by
      rcases howner_spec i with ⟨hi, hoi⟩ | ⟨mi, hmi, hti, hoi⟩ <;>
        rcases howner_spec j with ⟨hj, hoj⟩ | ⟨mj, hmj, htj, hoj⟩
      · have hv := congrArg Fin.val hij
        omega
      · have hv := congrArg Fin.val hij
        omega
      · have hv := congrArg Fin.val hij
        omega
      · have hv := congrArg Fin.val hij
        omega
    by_contra hijne
    apply hpairwise i j hijne
    exact connected_trans (htarget_conn i)
      (connected_symm (htarget_eq ▸ htarget_conn j))
  have hcard := Fintype.card_le_of_injective owner howner_inj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Finite absorption with the peripheral index allowed to vary.  A short-side
component can absorb at most one selected source for each peripheral index, so
the capacity is `|I| (|p| + |r|)`.  This is the form used for the alternating
two-peripheral relator, where it avoids an artificial preliminary choice of
one parity. -/
theorem exists_opposite_component_of_indexed_finite_absorption
    {I : Type*} [Fintype I] (H : I → Subgroup G)
    (p q r s : List (RelLetter G I))
    (source : Fin (Fintype.card I * (p.length + r.length) + 1) → ℕ)
    (index : Fin (Fintype.card I * (p.length + r.length) + 1) → I)
    (hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j))
    (htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))))
    (hnotSame : ∀ i i', i' ≤ q.length → i' ≠ source i →
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) (p.length + i') →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + i')) :
    ∃ i n j, IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      j ≤ s.length ∧
      n = p.length + q.length + r.length + (s.length - j) := by
  choose target htarget_ne htarget_start htarget_conn htarget_loc using htarget
  by_contra hnone
  push Not at hnone
  have hshort : ∀ i, target i < p.length ∨
      ∃ m : ℕ, m < r.length ∧
        target i = p.length + q.length + m := by
    intro i
    rcases htarget_loc i with hp | hq | hr | hs
    · exact Or.inl hp
    · obtain ⟨i', hi', heq⟩ := hq
      exfalso
      apply hnotSame i i' hi'
      · intro hieq
        apply htarget_ne i
        rw [heq, hieq]
      · rw [← heq]
        exact htarget_start i
      · rw [← heq]
        exact htarget_conn i
    · exact Or.inr hr
    · obtain ⟨j, hj, heq⟩ := hs
      exact False.elim (hnone i (target i) j (htarget_start i)
        (htarget_conn i) hj heq)
  have hshortPosition : ∀ i, ∃ a : Fin (p.length + r.length),
      (target i < p.length ∧ a.val = target i) ∨
        ∃ m : ℕ, m < r.length ∧
          target i = p.length + q.length + m ∧ a.val = p.length + m := by
    intro i
    rcases hshort i with hp | ⟨m, hm, heq⟩
    · exact ⟨⟨target i, by omega⟩, Or.inl ⟨hp, rfl⟩⟩
    · exact ⟨⟨p.length + m, by omega⟩,
        Or.inr ⟨m, hm, heq, rfl⟩⟩
  choose shortPosition hshortPosition_spec using hshortPosition
  let owner : Fin (Fintype.card I * (p.length + r.length) + 1) →
      Fin (p.length + r.length) × I :=
    fun i => (shortPosition i, index i)
  have howner_inj : Function.Injective owner := by
    intro i j hij
    have hindex : index i = index j := congrArg Prod.snd hij
    have hposition : shortPosition i = shortPosition j := congrArg Prod.fst hij
    have htarget_eq : target i = target j := by
      rcases hshortPosition_spec i with ⟨hi, hoi⟩ |
          ⟨mi, hmi, hti, hoi⟩ <;>
        rcases hshortPosition_spec j with ⟨hj, hoj⟩ |
          ⟨mj, hmj, htj, hoj⟩
      · have hv := congrArg Fin.val hposition
        omega
      · have hv := congrArg Fin.val hposition
        omega
      · have hv := congrArg Fin.val hposition
        omega
      · have hv := congrArg Fin.val hposition
        omega
    by_contra hijne
    apply hpairwise i j hindex hijne
    exact connected_trans (htarget_conn i)
      (connected_symm (hindex ▸ htarget_eq ▸ htarget_conn j))
  have hcard := Fintype.card_le_of_injective owner howner_inj
  simp only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm] at hcard
  omega

/-- The strengthened finite-absorption conclusion used by the gap argument.
The selected source is *clean*: it is connected to no component of either
short side.  Since the source is deep, it has some other target; same-side
exclusion and cleanliness force that target onto the opposite long side. -/
theorem exists_clean_opposite_component_of_indexed_finite_absorption
    {I : Type*} [Fintype I] (H : I → Subgroup G)
    (p q r s : List (RelLetter G I))
    (source : Fin (Fintype.card I * (p.length + r.length) + 1) → ℕ)
    (index : Fin (Fintype.card I * (p.length + r.length) + 1) → I)
    (hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j))
    (htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))))
    (hnotSame : ∀ i i', i' ≤ q.length → i' ≠ source i →
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) (p.length + i') →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + i')) :
    ∃ i n j, IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      j ≤ s.length ∧
      n = p.length + q.length + r.length + (s.length - j) ∧
      ∀ m, IsCompStart (index i) (p ++ q ++ r ++ revWord s) m →
        Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
          (p.length + source i) m →
        ¬ (m < p.length ∨
          ∃ a : ℕ, a < r.length ∧ m = p.length + q.length + a) := by
  let Dirty := fun i ↦ ∃ m : ℕ,
    IsCompStart (index i) (p ++ q ++ r ++ revWord s) m ∧
    Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
      (p.length + source i) m ∧
    (m < p.length ∨
      ∃ a : ℕ, a < r.length ∧ m = p.length + q.length + a)
  have hclean : ∃ i, ¬ Dirty i := by
    by_contra hall
    push Not at hall
    dsimp only [Dirty] at hall
    choose dirty hdirty_start hdirty_conn hdirty_loc using hall
    have hshortPosition : ∀ i, ∃ a : Fin (p.length + r.length),
        (dirty i < p.length ∧ a.val = dirty i) ∨
          ∃ m : ℕ, m < r.length ∧
            dirty i = p.length + q.length + m ∧ a.val = p.length + m := by
      intro i
      rcases hdirty_loc i with hp | ⟨m, hm, heq⟩
      · exact ⟨⟨dirty i, by omega⟩, Or.inl ⟨hp, rfl⟩⟩
      · exact ⟨⟨p.length + m, by omega⟩,
          Or.inr ⟨m, hm, heq, rfl⟩⟩
    choose shortPosition hshortPosition_spec using hshortPosition
    let owner : Fin (Fintype.card I * (p.length + r.length) + 1) →
        Fin (p.length + r.length) × I :=
      fun i ↦ (shortPosition i, index i)
    have howner_inj : Function.Injective owner := by
      intro i j hij
      have hindex : index i = index j := congrArg Prod.snd hij
      have hposition : shortPosition i = shortPosition j := congrArg Prod.fst hij
      have hdirty_eq : dirty i = dirty j := by
        rcases hshortPosition_spec i with ⟨hi, hoi⟩ |
            ⟨mi, hmi, hti, hoi⟩ <;>
          rcases hshortPosition_spec j with ⟨hj, hoj⟩ |
            ⟨mj, hmj, htj, hoj⟩
        · have hv := congrArg Fin.val hposition
          omega
        · have hv := congrArg Fin.val hposition
          omega
        · have hv := congrArg Fin.val hposition
          omega
        · have hv := congrArg Fin.val hposition
          omega
      by_contra hijne
      apply hpairwise i j hindex hijne
      exact connected_trans (hdirty_conn i)
        (connected_symm (hindex ▸ hdirty_eq ▸ hdirty_conn j))
    have hcard := Fintype.card_le_of_injective owner howner_inj
    simp only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm] at hcard
    omega
  obtain ⟨i, hiClean⟩ := hclean
  obtain ⟨n, hn, hnstart, hnconn, hnloc⟩ := htarget i
  rcases hnloc with hp | hq | hr | hs
  · exact False.elim (hiClean ⟨n, hnstart, hnconn, Or.inl hp⟩)
  · obtain ⟨i', hi', heq⟩ := hq
    exfalso
    apply hnotSame i i' hi'
    · intro hieq
      apply hn
      rw [heq, hieq]
    · rw [← heq]
      exact hnstart
    · rw [← heq]
      exact hnconn
  · obtain ⟨m, hm, heq⟩ := hr
    exact False.elim (hiClean ⟨n, hnstart, hnconn, Or.inr ⟨m, hm, heq⟩⟩)
  · obtain ⟨j, hj, heq⟩ := hs
    exact ⟨i, n, j, hnstart, hnconn, hj, heq,
      fun m hmstart hmconn hmshort ↦ hiClean
        ⟨m, hmstart, hmconn, hmshort⟩⟩

/-- Clean finite absorption with the cyclic seam counted as one additional
position.  Besides avoiding both short sides, the selected source does not
connect to the last component of the opposite side (`j = 1`).  This is exactly
the extra slot needed when the matched-pair polygon is rotated to bound its
second connector. -/
theorem exists_seam_clean_opposite_component_of_indexed_finite_absorption
    {I : Type*} [Fintype I] (H : I → Subgroup G)
    (p q r s : List (RelLetter G I))
    (source : Fin (p.length + r.length + 2) → ℕ)
    (index : Fin (p.length + r.length + 2) → I)
    (hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j))
    (htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' < q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))))
    (hnotSame : ∀ i i', i' < q.length → i' ≠ source i →
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) (p.length + i') →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + i')) :
    ∃ i n j, IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      j ≤ s.length ∧ j ≠ 1 ∧
      n = p.length + q.length + r.length + (s.length - j) ∧
      ∀ m, IsCompStart (index i) (p ++ q ++ r ++ revWord s) m →
        Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
          (p.length + source i) m →
        ¬ (m < p.length ∨
          ∃ a : ℕ, a < r.length ∧ m = p.length + q.length + a) := by
  let seam := p.length + q.length + r.length + (s.length - 1)
  let Dirty := fun i ↦ ∃ m : ℕ,
    IsCompStart (index i) (p ++ q ++ r ++ revWord s) m ∧
    Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
      (p.length + source i) m ∧
    ((m < p.length ∨
      ∃ a : ℕ, a < r.length ∧ m = p.length + q.length + a) ∨
      m = seam)
  have hclean : ∃ i, ¬ Dirty i := by
    by_contra hall
    push Not at hall
    dsimp only [Dirty, seam] at hall
    choose dirty hdirty_start hdirty_conn hdirty_loc using hall
    have hposition : ∀ i, ∃ a : Fin (p.length + r.length + 1),
        (dirty i < p.length ∧ a.val = dirty i) ∨
        (∃ m : ℕ, m < r.length ∧
          dirty i = p.length + q.length + m ∧ a.val = p.length + m) ∨
        (dirty i = seam ∧ a.val = p.length + r.length) := by
      intro i
      by_cases hp : dirty i < p.length
      · exact ⟨⟨dirty i, by omega⟩, Or.inl ⟨hp, rfl⟩⟩
      · by_cases hr : ∃ m : ℕ, m < r.length ∧
            dirty i = p.length + q.length + m
        · obtain ⟨m, hm, heq⟩ := hr
          exact ⟨⟨p.length + m, by omega⟩,
            Or.inr (Or.inl ⟨m, hm, heq, rfl⟩)⟩
        · have hs : dirty i = seam :=
            (hdirty_loc i).resolve_left (fun h ↦ h.elim hp hr)
          exact ⟨⟨p.length + r.length, by omega⟩,
            Or.inr (Or.inr ⟨hs, rfl⟩)⟩
    choose position hposition_spec using hposition
    dsimp only [seam] at hposition_spec
    let owner : Fin (p.length + r.length + 2) →
        Fin (p.length + r.length + 1) := position
    have howner_inj : Function.Injective owner := by
      intro i j hij
      have hpositionEq : position i = position j := hij
      have hdirty_eq : dirty i = dirty j := by
        rcases hposition_spec i with ⟨hi, hoi⟩ |
            ⟨mi, hmi, hti, hoi⟩ | ⟨hti, hoi⟩ <;>
          rcases hposition_spec j with ⟨hj, hoj⟩ |
            ⟨mj, hmj, htj, hoj⟩ | ⟨htj, hoj⟩
        all_goals
          have hv := congrArg Fin.val hpositionEq
          omega
      obtain ⟨ki, hci⟩ := hdirty_start i
      obtain ⟨kj, hcj⟩ := hdirty_start j
      have hilt : dirty i < (p ++ q ++ r ++ revWord s).length :=
        lt_of_lt_of_le hci.1 hci.2.1
      have hjlt : dirty j < (p ++ q ++ r ++ revWord s).length :=
        lt_of_lt_of_le hcj.1 hcj.2.1
      have hcoi := hci.2.2.1 (dirty i) le_rfl hci.1 hilt
      have hcoj0 := hcj.2.2.1 (dirty j) le_rfl hcj.1 hjlt
      have hcoj : ((p ++ q ++ r ++ revWord s)[dirty i]'hilt).IsCompOf
          (index j) := by
        simpa only [hdirty_eq] using hcoj0
      have hindex : index i = index j := by
        cases hletter : (p ++ q ++ r ++ revWord s)[dirty i]'hilt with
        | base g => simp only [hletter, RelLetter.IsCompOf] at hcoi
        | comp nu g =>
            rw [hletter] at hcoi hcoj
            exact hcoi.symm.trans hcoj
      by_contra hijne
      apply hpairwise i j hindex hijne
      exact connected_trans (hdirty_conn i)
        (connected_symm (hindex ▸ hdirty_eq ▸ hdirty_conn j))
    have hcard := Fintype.card_le_of_injective owner howner_inj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, hiClean⟩ := hclean
  obtain ⟨n, hn, hnstart, hnconn, hnloc⟩ := htarget i
  rcases hnloc with hp | hq | hr | hs
  · exact False.elim (hiClean ⟨n, hnstart, hnconn, Or.inl (Or.inl hp)⟩)
  · obtain ⟨i', hi', heq⟩ := hq
    exfalso
    apply hnotSame i i' hi'
    · intro hieq
      apply hn
      rw [heq, hieq]
    · rw [← heq]
      exact hnstart
    · rw [← heq]
      exact hnconn
  · obtain ⟨m, hm, heq⟩ := hr
    exact False.elim
      (hiClean ⟨n, hnstart, hnconn, Or.inl (Or.inr ⟨m, hm, heq⟩)⟩)
  · obtain ⟨j, hj, heq⟩ := hs
    have hjne : j ≠ 1 := by
      intro hjeq
      apply hiClean
      refine ⟨n, hnstart, hnconn, Or.inr ?_⟩
      dsimp only [seam]
      rw [heq, hjeq]
    exact ⟨i, n, j, hnstart, hnconn, hj, hjne, heq,
      fun m hmstart hmconn hmshort ↦ hiClean
        ⟨m, hmstart, hmconn, Or.inl hmshort⟩⟩

/-- Among twice as many paired sources as there are short-side and seam
positions, one whole pair avoids those positions.  A target position has a
unique peripheral label, so its capacity is one, not one per index. -/
theorem exists_paired_seam_clean_sources
    {I : Type*} [Fintype I] (H : I → Subgroup G)
    (p q r s : List (RelLetter G I))
    (source : Fin (2 * (p.length + r.length + 2)) → ℕ)
    (index : Fin (2 * (p.length + r.length + 2)) → I)
    (hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j)) :
    ∃ a : Fin (p.length + r.length + 2),
      (∀ m, IsCompStart (index ⟨2 * a, by omega⟩)
          (p ++ q ++ r ++ revWord s) m →
        Connected H (index ⟨2 * a, by omega⟩) 1
          (p ++ q ++ r ++ revWord s) (p.length + source ⟨2 * a, by omega⟩) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
            m = p.length + q.length + b) ∨
          m = p.length + q.length + r.length + (s.length - 1))) ∧
      (∀ m, IsCompStart (index ⟨2 * a + 1, by omega⟩)
          (p ++ q ++ r ++ revWord s) m →
        Connected H (index ⟨2 * a + 1, by omega⟩) 1
          (p ++ q ++ r ++ revWord s)
          (p.length + source ⟨2 * a + 1, by omega⟩) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
            m = p.length + q.length + b) ∨
          m = p.length + q.length + r.length + (s.length - 1))) := by
  classical
  let left : Fin (p.length + r.length + 2) →
      Fin (2 * (p.length + r.length + 2)) := fun a ↦ ⟨2 * a, by omega⟩
  let right : Fin (p.length + r.length + 2) →
      Fin (2 * (p.length + r.length + 2)) := fun a ↦ ⟨2 * a + 1, by omega⟩
  let seam := p.length + q.length + r.length + (s.length - 1)
  let Dirty := fun i ↦ ∃ m : ℕ,
    IsCompStart (index i) (p ++ q ++ r ++ revWord s) m ∧
    Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
      (p.length + source i) m ∧
    ((m < p.length ∨ ∃ b, b < r.length ∧
      m = p.length + q.length + b) ∨ m = seam)
  have hpair : ∃ a, ¬ Dirty (left a) ∧ ¬ Dirty (right a) := by
    by_contra hnone
    push Not at hnone
    let chosen : Fin (p.length + r.length + 2) →
        Fin (2 * (p.length + r.length + 2)) := fun a ↦
      if h : Dirty (left a) then left a else right a
    have hchosenVal : ∀ a, (chosen a).val = 2 * a.val ∨
        (chosen a).val = 2 * a.val + 1 := by
      intro a
      dsimp only [chosen]
      split_ifs <;> simp only [left, right] <;> tauto
    have hchosenDirty : ∀ a, Dirty (chosen a) := by
      intro a
      dsimp only [chosen]
      split_ifs with h
      · exact h
      · exact hnone a h
    choose dirty hdirty_start hdirty_conn hdirty_loc using hchosenDirty
    have hposition : ∀ a, ∃ z : Fin (p.length + r.length + 1),
        (dirty a < p.length ∧ z.val = dirty a) ∨
        (∃ b, b < r.length ∧ dirty a = p.length + q.length + b ∧
          z.val = p.length + b) ∨
        (dirty a = seam ∧ z.val = p.length + r.length) := by
      intro a
      rcases hdirty_loc a with (hp | ⟨b, hb, heq⟩) | hs
      · exact ⟨⟨dirty a, by omega⟩, Or.inl ⟨hp, rfl⟩⟩
      · exact ⟨⟨p.length + b, by omega⟩,
          Or.inr (Or.inl ⟨b, hb, heq, rfl⟩)⟩
      · exact ⟨⟨p.length + r.length, by omega⟩,
          Or.inr (Or.inr ⟨hs, rfl⟩)⟩
    choose position hposition_spec using hposition
    have hposition_inj : Function.Injective position := by
      intro a b hab
      have hdirtyEq : dirty a = dirty b := by
        rcases hposition_spec a with ⟨ha, hoa⟩ |
            ⟨ma, hma, hta, hoa⟩ | ⟨hta, hoa⟩ <;>
          rcases hposition_spec b with ⟨hb, hob⟩ |
            ⟨mb, hmb, htb, hob⟩ | ⟨htb, hob⟩
        all_goals
          have hv := congrArg Fin.val hab
          omega
      by_contra habne
      obtain ⟨ka, hca⟩ := hdirty_start a
      obtain ⟨kb, hcb⟩ := hdirty_start b
      have halt : dirty a < (p ++ q ++ r ++ revWord s).length :=
        lt_of_lt_of_le hca.1 hca.2.1
      have hblt : dirty b < (p ++ q ++ r ++ revWord s).length :=
        lt_of_lt_of_le hcb.1 hcb.2.1
      have hcoa := hca.2.2.1 (dirty a) le_rfl hca.1 halt
      have hcob0 := hcb.2.2.1 (dirty b) le_rfl hcb.1 hblt
      have hcob : ((p ++ q ++ r ++ revWord s)[dirty a]'halt).IsCompOf
          (index (chosen b)) := by simpa only [hdirtyEq] using hcob0
      have hindex : index (chosen a) = index (chosen b) := by
        cases hletter : (p ++ q ++ r ++ revWord s)[dirty a]'halt with
        | base g => simp only [hletter, RelLetter.IsCompOf] at hcoa
        | comp nu g =>
            rw [hletter] at hcoa hcob
            exact hcoa.symm.trans hcob
      have hchosenNe : chosen a ≠ chosen b := by
        intro heq
        have hv := congrArg Fin.val heq
        rcases hchosenVal a with ha | ha <;>
          rcases hchosenVal b with hb | hb
        all_goals
          apply habne
          apply Fin.ext
          omega
      exact False.elim (hpairwise (chosen a) (chosen b) hindex hchosenNe
        (connected_trans (hdirty_conn a)
          (connected_symm (hindex ▸ hdirtyEq ▸ hdirty_conn b))))
    have hcard := Fintype.card_le_of_injective position hposition_inj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨a, hleft, hright⟩ := hpair
  refine ⟨a, ?_, ?_⟩
  · intro m hmstart hmconn hmloc
    exact hleft ⟨m, hmstart, hmconn, hmloc⟩
  · intro m hmstart hmconn hmloc
    exact hright ⟨m, hmstart, hmconn, hmloc⟩

/-- One exceptional source pair may contain the unique base letter of an
exact relator.  With one further pair in the finite grid, finite absorption
still leaves a valid pair whose two sources avoid both short sides and the
cyclic seam. -/
theorem exists_valid_paired_seam_clean_sources
    {I : Type*} [Fintype I] (H : I → Subgroup G)
    (p q r s : List (RelLetter G I))
    (source : Fin (2 * (p.length + r.length + 3)) → ℕ)
    (index : Fin (2 * (p.length + r.length + 3)) → I)
    (Valid : Fin (p.length + r.length + 3) → Prop)
    (hinvalid : ∀ a b, ¬ Valid a → ¬ Valid b → a = b)
    (hpairwise : ∀ a b, Valid a → Valid b →
      ∀ i j,
        (i = ⟨2 * a, by omega⟩ ∨ i = ⟨2 * a + 1, by omega⟩) →
        (j = ⟨2 * b, by omega⟩ ∨ j = ⟨2 * b + 1, by omega⟩) →
        index i = index j → i ≠ j →
        ¬ Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
          (p.length + source i) (p.length + source j)) :
    ∃ a : Fin (p.length + r.length + 3), Valid a ∧
      (∀ m, IsCompStart (index ⟨2 * a, by omega⟩)
          (p ++ q ++ r ++ revWord s) m →
        Connected H (index ⟨2 * a, by omega⟩) 1
          (p ++ q ++ r ++ revWord s) (p.length + source ⟨2 * a, by omega⟩) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
            m = p.length + q.length + b) ∨
          m = p.length + q.length + r.length + (s.length - 1))) ∧
      (∀ m, IsCompStart (index ⟨2 * a + 1, by omega⟩)
          (p ++ q ++ r ++ revWord s) m →
        Connected H (index ⟨2 * a + 1, by omega⟩) 1
          (p ++ q ++ r ++ revWord s)
          (p.length + source ⟨2 * a + 1, by omega⟩) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
            m = p.length + q.length + b) ∨
          m = p.length + q.length + r.length + (s.length - 1))) := by
  classical
  let left : Fin (p.length + r.length + 3) →
      Fin (2 * (p.length + r.length + 3)) := fun a ↦ ⟨2 * a, by omega⟩
  let right : Fin (p.length + r.length + 3) →
      Fin (2 * (p.length + r.length + 3)) := fun a ↦ ⟨2 * a + 1, by omega⟩
  let seam := p.length + q.length + r.length + (s.length - 1)
  let Dirty := fun i ↦ ∃ m : ℕ,
    IsCompStart (index i) (p ++ q ++ r ++ revWord s) m ∧
    Connected H (index i) 1 (p ++ q ++ r ++ revWord s)
      (p.length + source i) m ∧
    ((m < p.length ∨ ∃ b, b < r.length ∧
      m = p.length + q.length + b) ∨ m = seam)
  have hgood : ∃ a, Valid a ∧ ¬ Dirty (left a) ∧ ¬ Dirty (right a) := by
    by_contra hnone
    push Not at hnone
    let chosen : Fin (p.length + r.length + 3) →
        Fin (2 * (p.length + r.length + 3)) := fun a ↦
      if h : Dirty (left a) then left a else right a
    have hchosenVal : ∀ a, (chosen a).val = 2 * a.val ∨
        (chosen a).val = 2 * a.val + 1 := by
      intro a
      dsimp only [chosen]
      split_ifs <;> simp only [left, right] <;> tauto
    have hfailure : ∀ a, ¬ Valid a ∨ Dirty (chosen a) := by
      intro a
      by_cases hv : Valid a
      · right
        dsimp only [chosen]
        split_ifs with hd
        · exact hd
        · exact hnone a hv hd
      · exact Or.inl hv
    have htarget : ∀ a, ∃ z : Fin (p.length + r.length + 2),
        (¬ Valid a ∧ z.val = p.length + r.length + 1) ∨
        (Valid a ∧ ∃ d : ℕ,
          IsCompStart (index (chosen a)) (p ++ q ++ r ++ revWord s) d ∧
          Connected H (index (chosen a)) 1 (p ++ q ++ r ++ revWord s)
            (p.length + source (chosen a)) d ∧
          ((d < p.length ∧ z.val = d) ∨
            (∃ x, x < r.length ∧ d = p.length + q.length + x ∧
              z.val = p.length + x) ∨
            (d = seam ∧ z.val = p.length + r.length))) := by
      intro a
      by_cases hva : Valid a
      · have hda : Dirty (chosen a) :=
          (hfailure a).resolve_left (fun hna ↦ hna hva)
        obtain ⟨d, hdstart, hdconn, hdloc⟩ := hda
        rcases hdloc with (hp | ⟨x, hx, heq⟩) | hs
        · refine ⟨⟨d, by omega⟩, Or.inr ?_⟩
          exact ⟨hva, d, hdstart, hdconn, Or.inl ⟨hp, rfl⟩⟩
        · refine ⟨⟨p.length + x, by omega⟩, Or.inr ?_⟩
          exact ⟨hva, d, hdstart, hdconn,
            Or.inr (Or.inl ⟨x, hx, heq, rfl⟩)⟩
        · refine ⟨⟨p.length + r.length, by omega⟩, Or.inr ?_⟩
          exact ⟨hva, d, hdstart, hdconn,
            Or.inr (Or.inr ⟨hs, rfl⟩)⟩
      · refine ⟨⟨p.length + r.length + 1, by omega⟩, Or.inl ?_⟩
        exact ⟨hva, rfl⟩
    choose owner howner_spec using htarget
    have howner_inj : Function.Injective owner := by
      intro a b hab
      rcases howner_spec a with ⟨hva, haowner⟩ |
          ⟨hva, da, hdastart, hdaconn, hdaloc⟩ <;>
        rcases howner_spec b with ⟨hvb, hbowner⟩ |
          ⟨hvb, db, hdbstart, hdbconn, hdbloc⟩
      · exact hinvalid a b hva hvb
      · have hble : (owner b).val ≤ p.length + r.length := by
          rcases hdbloc with ⟨hpb, hob⟩ |
              ⟨xb, hxb, hbeq, hob⟩ | ⟨hsb, hob⟩ <;> omega
        have hv := congrArg Fin.val hab
        omega
      · have hale : (owner a).val ≤ p.length + r.length := by
          rcases hdaloc with ⟨hpa, hoa⟩ |
              ⟨xa, hxa, haeq, hoa⟩ | ⟨hsa, hoa⟩ <;> omega
        have hv := congrArg Fin.val hab
        omega
      · have hdab : da = db := by
          rcases hdaloc with ⟨hpa, hoa⟩ |
              ⟨xa, hxa, haeq, hoa⟩ | ⟨hsa, hoa⟩ <;>
            rcases hdbloc with ⟨hpb, hob⟩ |
              ⟨xb, hxb, hbeq, hob⟩ | ⟨hsb, hob⟩
          all_goals
            have hv := congrArg Fin.val hab
            omega
        by_contra habne
        obtain ⟨ka, hca⟩ := hdastart
        obtain ⟨kb, hcb⟩ := hdbstart
        have halt : da < (p ++ q ++ r ++ revWord s).length :=
          lt_of_lt_of_le hca.1 hca.2.1
        have hblt : db < (p ++ q ++ r ++ revWord s).length :=
          lt_of_lt_of_le hcb.1 hcb.2.1
        have hcoa := hca.2.2.1 da le_rfl hca.1 halt
        have hcob0 := hcb.2.2.1 db le_rfl hcb.1 hblt
        have hcob : ((p ++ q ++ r ++ revWord s)[da]'halt).IsCompOf
            (index (chosen b)) := by simpa only [hdab] using hcob0
        have hindex : index (chosen a) = index (chosen b) := by
          cases hletter : (p ++ q ++ r ++ revWord s)[da]'halt with
          | base g => simp only [hletter, RelLetter.IsCompOf] at hcoa
          | comp nu g =>
              rw [hletter] at hcoa hcob
              exact hcoa.symm.trans hcob
        have hchosenNe : chosen a ≠ chosen b := by
          intro heq
          have hv := congrArg Fin.val heq
          rcases hchosenVal a with ha | ha <;>
            rcases hchosenVal b with hb | hb
          all_goals
            apply habne
            apply Fin.ext
            omega
        have hchosenA : chosen a = ⟨2 * a, by omega⟩ ∨
            chosen a = ⟨2 * a + 1, by omega⟩ := by
          rcases hchosenVal a with ha | ha
          · exact Or.inl (Fin.ext ha)
          · exact Or.inr (Fin.ext ha)
        have hchosenB : chosen b = ⟨2 * b, by omega⟩ ∨
            chosen b = ⟨2 * b + 1, by omega⟩ := by
          rcases hchosenVal b with hb | hb
          · exact Or.inl (Fin.ext hb)
          · exact Or.inr (Fin.ext hb)
        exact False.elim (hpairwise a b hva hvb (chosen a) (chosen b)
          hchosenA hchosenB hindex hchosenNe
          (connected_trans hdaconn
            (connected_symm (hindex ▸ hdab ▸ hdbconn))))
    have hcard := Fintype.card_le_of_injective owner howner_inj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨a, hva, hleft, hright⟩ := hgood
  refine ⟨a, hva, ?_, ?_⟩
  · intro m hmstart hmconn hmloc
    exact hleft ⟨m, hmstart, hmconn, hmloc⟩
  · intro m hmstart hmconn hmloc
    exact hright ⟨m, hmstart, hmconn, hmloc⟩

/-- A component strictly inside the second side remains a component of the
whole quadrilateral, with no restriction on either short side. -/
theorem isComp_fourGon_of_isComp_side_of_interior
    (p q r s : List (RelLetter G Λ)) (lam : Λ) {i k : ℕ}
    (hi : 0 < i) (hk : k < q.length) (hcomp : IsComp lam q i k) :
    IsComp lam (p ++ q ++ r ++ revWord s) (p.length + i) (p.length + k) := by
  obtain ⟨hik, hkq, hrange, hpre, hpost⟩ := hcomp
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [length_fourGon]
    omega
  · intro j hj1 hj2 hj
    have hjq : j - p.length < q.length := by omega
    rw [getElem_fourGon_q p q r s hjq (by omega) hj]
    exact hrange (j - p.length) (by omega) (by omega) hjq
  · intro j hji hj hc
    have hjq : i - 1 < q.length := by omega
    rw [getElem_fourGon_q p q r s hjq (by omega) hj] at hc
    exact hpre (i - 1) (by omega) hjq hc
  · intro hkl hc
    rw [getElem_fourGon_q p q r s hk rfl hkl] at hc
    exact hpost hk hc

/-- A deep interior component is connected to a distinct component somewhere
on the four sides.  Unlike the historical two-branch bridge, this theorem does
not silently erase components of the short sides. -/
theorem exists_other_component_of_deep_fourGon_relativeSides
    (D : RelGenSet G Λ) (lam : Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (rho : ℕ) (p q r s : List (RelLetter G Λ)) (i k : ℕ),
        C * 4 ≤ rho → 0 < i → k < q.length → IsComp lam q i k →
        IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1
          (p ++ q ++ r ++ revWord s) →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k
            ∉ D.relBall lam rho →
        ∃ n : ℕ, n ≠ p.length + i ∧
          IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
          (n < p.length ∨
            (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
            (∃ m : ℕ, m < r.length ∧
              n = p.length + q.length + m) ∨
            (∃ j : ℕ, j ≤ s.length ∧
              n = p.length + q.length + r.length + (s.length - j))) ∧
          ∃ h : G, h ∈ D.fam lam ∧
            RelLetter.listVal p * vertex (1 : G) q i * h =
              vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
  let C := 15 * (25 * (δ + bn + 1))
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro rho p q r s i k hrho hi hk hcomp hpoly hdeep
  have hbridge := isComp_fourGon_of_isComp_side_of_interior
    p q r s lam hi hk hcomp
  have hiq : i ≤ q.length := le_trans (Nat.le_of_lt hcomp.1) hcomp.2.1
  apply exists_other_component_fourGon_general D lam p q r s hiq
    ⟨p.length + k, hbridge⟩
  intro hisolated
  have hspan := isolatedComponentBound_of_fourPointHyperbolic_at
    D hsymm bn hδ 4 (by omega) 1 (p ++ q ++ r ++ revWord s) hpoly
      lam (p.length + i) (p.length + k) hbridge hisolated
  rw [span_fourGon_side p q r s (by omega) (by omega)] at hspan
  exact hdeep (relBall_mono_radius D lam hrho hspan)

/-- A run containing one more deep component than the total length of the two
short sides has a component connected across to the opposite long side.  This
is Hull Lemma 5.1(2)'s finite absorption mechanism in the coordinates used by
the relator quadrilateral. -/
theorem exists_opposite_match_of_deep_run_relativeSides
    (D : RelGenSet G Λ) (lam : Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (rho : ℕ) (p q r s : List (RelLetter G Λ)),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
          RelLetter.listVal r →
        IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1
          (p ++ q ++ r ++ revWord s) →
        ∀ (source : Fin (p.length + r.length + 1) → ℕ),
          (∀ i, 0 < source i) →
          (∀ i, source i + 1 < q.length) →
          (∀ i, IsComp lam q (source i) (source i + 1)) →
          Function.Injective source →
          (∀ i, (vertex (1 : G) q (source i))⁻¹ *
              vertex (1 : G) q (source i + 1) ∉ D.relBall lam rho) →
          C * 4 ≤ rho →
          (∀ i i', i' ≤ q.length → i' ≠ source i →
            IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') →
            ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
              (p.length + source i) (p.length + i')) →
          ∃ i : Fin (p.length + r.length + 1), ∃ j : ℕ,
            j ≤ s.length ∧
            IsCompStart lam (p ++ q ++ r ++ revWord s)
              (p.length + q.length + r.length + (s.length - j)) ∧
            ∃ h : G, h ∈ D.fam lam ∧
              RelLetter.listVal p * vertex (1 : G) q (source i) * h =
                vertex (1 : G) s j := by
  obtain ⟨C, hC, hdeepTarget⟩ :=
    exists_other_component_of_deep_fourGon_relativeSides D lam hsymm hδ
  refine ⟨C, hC, ?_⟩
  intro rho p q r s hclose hpoly source hsource_pos hsource_end hsource_comp
    hsource_inj hsource_deep hrho hnotSame
  have htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) := by
    intro i
    obtain ⟨n, hn, hnstart, hnloc, h, hh, heq⟩ :=
      hdeepTarget rho p q r s (source i) (source i + 1) hrho
        (hsource_pos i) (hsource_end i) (hsource_comp i) hpoly
        (hsource_deep i)
    refine ⟨n, hn, hnstart, ?_, hnloc⟩
    show (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + source i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) n ∈ D.fam lam
    rw [vertex_fourGon_side p q r s 1 (by
      exact le_trans (Nat.le_of_lt (hsource_comp i).1)
        (hsource_comp i).2.1)]
    rw [← heq]
    have hcancel :
        (RelLetter.listVal p * vertex (1 : G) q (source i))⁻¹ *
          (RelLetter.listVal p * vertex (1 : G) q (source i) * h) = h := by
      group
    simp only [one_mul]
    rw [hcancel]
    exact hh
  have hpairwise : ∀ i j, i ≠ j →
      ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j) := by
    intro i j hij
    apply hnotSame i (source j)
    · exact le_trans (Nat.le_of_lt (hsource_comp j).1)
        (hsource_comp j).2.1
    · exact fun heq => hij (hsource_inj heq.symm)
    · exact ⟨p.length + source j + 1,
        isComp_fourGon_of_isComp_side_of_interior p q r s lam
          (hsource_pos j) (hsource_end j) (hsource_comp j)⟩
  obtain ⟨i, n, j, hnstart, hnconn, hj, hn⟩ :=
    exists_opposite_component_of_finite_absorption D.fam lam p q r s source
      hpairwise htarget hnotSame
  refine ⟨i, j, hj, ?_, ?_⟩
  · rw [← hn]
    exact hnstart
  · exact exists_connector_fourGon D lam p q r s hclose
      (by
        exact le_trans (Nat.le_of_lt (hsource_comp i).1)
          (hsource_comp i).2.1) (hn ▸ hnconn)

/-- The alternating-family form of the deep-run argument.  The selected
components may alternate between the two peripheral subgroups.  A component
of either short side can absorb at most one source component of each index,
so `|Bool| (|p| + |r|) + 1` deep sources force a match on the opposite long
side. -/
theorem exists_opposite_match_of_indexed_deep_run_relativeSides
    (D : RelGenSet G Bool) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (rho : ℕ) (p q r s : List (RelLetter G Bool)),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
          RelLetter.listVal r →
        IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1
          (p ++ q ++ r ++ revWord s) →
        ∀ (source : Fin (Fintype.card Bool * (p.length + r.length) + 1) → ℕ)
          (index : Fin (Fintype.card Bool * (p.length + r.length) + 1) → Bool),
          (∀ i, 0 < source i) →
          (∀ i, source i + 1 < q.length) →
          (∀ i, IsComp (index i) q (source i) (source i + 1)) →
          Function.Injective source →
          (∀ i, (vertex (1 : G) q (source i))⁻¹ *
              vertex (1 : G) q (source i + 1) ∉
                D.relBall (index i) rho) →
          C * 4 ≤ rho →
          (∀ i i', i' ≤ q.length → i' ≠ source i →
            IsCompStart (index i) (p ++ q ++ r ++ revWord s)
              (p.length + i') →
            ¬ Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
              (p.length + source i) (p.length + i')) →
          ∃ i, ∃ j : ℕ, j ≤ s.length ∧
            IsCompStart (index i) (p ++ q ++ r ++ revWord s)
              (p.length + q.length + r.length + (s.length - j)) ∧
            (∃ h : G, h ∈ D.fam (index i) ∧
              RelLetter.listVal p * vertex (1 : G) q (source i) * h =
                vertex (1 : G) s j) ∧
            ∀ m, IsCompStart (index i) (p ++ q ++ r ++ revWord s) m →
              Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
                (p.length + source i) m →
              ¬ (m < p.length ∨
                ∃ a : ℕ, a < r.length ∧
                  m = p.length + q.length + a) := by
  obtain ⟨Cfalse, hCfalse, hfalse⟩ :=
    exists_other_component_of_deep_fourGon_relativeSides D false hsymm hδ
  obtain ⟨Ctrue, hCtrue, htrue⟩ :=
    exists_other_component_of_deep_fourGon_relativeSides D true hsymm hδ
  refine ⟨max Cfalse Ctrue, lt_of_lt_of_le hCfalse (Nat.le_max_left _ _), ?_⟩
  intro rho p q r s hclose hpoly source index hsource_pos hsource_end
    hsource_comp hsource_inj hsource_deep hrho hnotSame
  have hraw : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) ∧
      ∃ h : G, h ∈ D.fam (index i) ∧
        RelLetter.listVal p * vertex (1 : G) q (source i) * h =
          vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
    intro i
    cases hindex : index i with
    | false =>
        simpa [hindex] using
          hfalse rho p q r s (source i) (source i + 1)
            (by omega) (hsource_pos i) (hsource_end i)
            (by simpa [hindex] using hsource_comp i) hpoly
            (by simpa [hindex] using hsource_deep i)
    | true =>
        simpa [hindex] using
          htrue rho p q r s (source i) (source i + 1)
            (by omega) (hsource_pos i) (hsource_end i)
            (by simpa [hindex] using hsource_comp i) hpoly
            (by simpa [hindex] using hsource_deep i)
  have htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) := by
    intro i
    obtain ⟨n, hn, hnstart, hnloc, h, hh, heq⟩ := hraw i
    refine ⟨n, hn, hnstart, ?_, hnloc⟩
    show (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + source i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) n ∈ D.fam (index i)
    rw [vertex_fourGon_side p q r s 1 (by
      exact le_trans (Nat.le_of_lt (hsource_comp i).1)
        (hsource_comp i).2.1)]
    rw [← heq]
    have hcancel :
        (RelLetter.listVal p * vertex (1 : G) q (source i))⁻¹ *
          (RelLetter.listVal p * vertex (1 : G) q (source i) * h) = h := by
      group
    simp only [one_mul]
    rw [hcancel]
    exact hh
  have hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j) := by
    intro i j hindex hij
    apply hnotSame i (source j)
    · exact le_trans (Nat.le_of_lt (hsource_comp j).1)
        (hsource_comp j).2.1
    · exact fun heq => hij (hsource_inj heq.symm)
    · rw [hindex]
      exact ⟨p.length + source j + 1,
        isComp_fourGon_of_isComp_side_of_interior p q r s (index j)
          (hsource_pos j) (hsource_end j) (hsource_comp j)⟩
  obtain ⟨i, n, j, hnstart, hnconn, hj, hn, hclean⟩ :=
    exists_clean_opposite_component_of_indexed_finite_absorption D.fam p q r s
      source index hpairwise htarget hnotSame
  refine ⟨i, j, hj, ?_, ?_, hclean⟩
  · rw [← hn]
    exact hnstart
  · exact exists_connector_fourGon D (index i) p q r s hclose
      (by
        exact le_trans (Nat.le_of_lt (hsource_comp i).1)
          (hsource_comp i).2.1) (hn ▸ hnconn)

/-- The cyclic-seam-safe indexed deep-run match.  One additional target slot
per peripheral index excludes the last component of the opposite side, so the
matched pair can be rotated without a base-letter assumption. -/
theorem exists_seam_clean_match_of_indexed_deep_run_relativeSides
    (D : RelGenSet G Bool) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (rho : ℕ) (p q r s : List (RelLetter G Bool)),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q *
          RelLetter.listVal r →
        IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1
          (p ++ q ++ r ++ revWord s) →
        ∀ (source : Fin (p.length + r.length + 2) → ℕ)
          (index : Fin (p.length + r.length + 2) → Bool),
          (∀ i, 0 < source i) →
          (∀ i, source i + 1 < q.length) →
          (∀ i, IsComp (index i) q (source i) (source i + 1)) →
          Function.Injective source →
          (∀ i, (vertex (1 : G) q (source i))⁻¹ *
              vertex (1 : G) q (source i + 1) ∉
                D.relBall (index i) rho) →
          C * 4 ≤ rho →
          (∀ i i', i' < q.length → i' ≠ source i →
            IsCompStart (index i) (p ++ q ++ r ++ revWord s)
              (p.length + i') →
            ¬ Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
              (p.length + source i) (p.length + i')) →
          ∃ i, ∃ j : ℕ, j ≤ s.length ∧ j ≠ 1 ∧
            IsCompStart (index i) (p ++ q ++ r ++ revWord s)
              (p.length + q.length + r.length + (s.length - j)) ∧
            (∃ h : G, h ∈ D.fam (index i) ∧
              RelLetter.listVal p * vertex (1 : G) q (source i) * h =
                vertex (1 : G) s j) ∧
            ∀ m, IsCompStart (index i) (p ++ q ++ r ++ revWord s) m →
              Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
                (p.length + source i) m →
              ¬ (m < p.length ∨
                ∃ a : ℕ, a < r.length ∧
                  m = p.length + q.length + a) := by
  obtain ⟨Cfalse, hCfalse, hfalse⟩ :=
    exists_other_component_of_deep_fourGon_relativeSides D false hsymm hδ
  obtain ⟨Ctrue, hCtrue, htrue⟩ :=
    exists_other_component_of_deep_fourGon_relativeSides D true hsymm hδ
  refine ⟨max Cfalse Ctrue, lt_of_lt_of_le hCfalse (Nat.le_max_left _ _), ?_⟩
  intro rho p q r s hclose hpoly source index hsource_pos hsource_end
    hsource_comp hsource_inj hsource_deep hrho hnotSame
  have hraw : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) ∧
      ∃ h : G, h ∈ D.fam (index i) ∧
        RelLetter.listVal p * vertex (1 : G) q (source i) * h =
          vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
    intro i
    cases hindex : index i with
    | false =>
        simpa [hindex] using
          hfalse rho p q r s (source i) (source i + 1)
            (by omega) (hsource_pos i) (hsource_end i)
            (by simpa [hindex] using hsource_comp i) hpoly
            (by simpa [hindex] using hsource_deep i)
    | true =>
        simpa [hindex] using
          htrue rho p q r s (source i) (source i + 1)
            (by omega) (hsource_pos i) (hsource_end i)
            (by simpa [hindex] using hsource_comp i) hpoly
            (by simpa [hindex] using hsource_deep i)
  have htarget : ∀ i, ∃ n : ℕ, n ≠ p.length + source i ∧
      IsCompStart (index i) (p ++ q ++ r ++ revWord s) n ∧
      Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' < q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) := by
    intro i
    obtain ⟨n, hn, hnstart, _hnloc, h, hh, heq⟩ := hraw i
    obtain ⟨kend, hncomp⟩ := hnstart
    have hnlt : n < p.length + q.length + r.length + s.length := by
      rw [← length_fourGon p q r s]
      exact lt_of_lt_of_le hncomp.1 hncomp.2.1
    have hnloc : n < p.length ∨
        (∃ i' : ℕ, i' < q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j)) := by
      by_cases hp : n < p.length
      · exact Or.inl hp
      by_cases hq : n < p.length + q.length
      · exact Or.inr (Or.inl ⟨n - p.length, by omega, by omega⟩)
      by_cases hr : n < p.length + q.length + r.length
      · exact Or.inr (Or.inr (Or.inl
          ⟨n - (p.length + q.length), by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨p.length + q.length + r.length + s.length - n,
            by omega, by omega⟩))
    refine ⟨n, hn, ⟨kend, hncomp⟩, ?_, hnloc⟩
    show (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + source i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) n ∈ D.fam (index i)
    rw [vertex_fourGon_side p q r s 1 (by
      exact le_trans (Nat.le_of_lt (hsource_comp i).1)
        (hsource_comp i).2.1), ← heq]
    have hcancel :
        (RelLetter.listVal p * vertex (1 : G) q (source i))⁻¹ *
          (RelLetter.listVal p * vertex (1 : G) q (source i) * h) = h := by
      group
    simp only [one_mul]
    rw [hcancel]
    exact hh
  have hpairwise : ∀ i j, index i = index j → i ≠ j →
      ¬ Connected D.fam (index i) 1 (p ++ q ++ r ++ revWord s)
        (p.length + source i) (p.length + source j) := by
    intro i j hindex hij
    apply hnotSame i (source j)
    · exact lt_trans (Nat.lt_succ_self _) (hsource_end j)
    · exact fun heq ↦ hij (hsource_inj heq.symm)
    · rw [hindex]
      exact ⟨p.length + source j + 1,
        isComp_fourGon_of_isComp_side_of_interior p q r s (index j)
          (hsource_pos j) (hsource_end j) (hsource_comp j)⟩
  obtain ⟨i, n, j, hnstart, hnconn, hj, hjne, hn, hclean⟩ :=
    exists_seam_clean_opposite_component_of_indexed_finite_absorption
      D.fam p q r s source index hpairwise htarget hnotSame
  refine ⟨i, j, hj, hjne, ?_, ?_, hclean⟩
  · rw [← hn]
    exact hnstart
  · exact exists_connector_fourGon D (index i) p q r s hclose
      (by
        exact le_trans (Nat.le_of_lt (hsource_comp i).1)
          (hsource_comp i).2.1) (hn ▸ hnconn)

end OsinComponents
end GGT
end GroupApproximation
