import GroupApproximation.GGT.DGOCorollary427FiniteExtension
import GroupApproximation.GGT.OsinTheorem54SepFiniteFam
import GroupApproximation.GGT.OsinTheorem54SepSurgery

/-!
# Local finiteness after adjoining one pair of base letters

This file proves the relative-metric half left open in
`DGOCorollary427FiniteExtension`.  The proof is the direct word version of the
finite-presentation argument in Dahmani--Guirardel--Osin, Corollary 4.27.

Choose fixed old-relative-alphabet spellings of `t` and `t⁻¹`.  Only finitely
many peripheral letters occur in those spellings.  First move their values into
the base.  This is a finite enlargement *inside the peripheral family*, so
`OsinComponents.relBall_finite_of_base_subset'` applies.  After that move, both
fixed spellings demote to words made entirely of base letters.  Replacing every
new `t`- or `t⁻¹`-edge by the corresponding demoted word preserves avoidance:
base letters never traverse the forbidden peripheral subgraph.  The replacement
has a uniform length bound, so every ball for the pair-enlarged base is contained
in a finite ball for the intermediate base.

No finiteness assumption on the index type is used.  Only the finitely many
peripheral letters in the two chosen spellings are moved.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u w

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## A finite enlargement by specified peripheral values -/

/-- Values of the peripheral letters occurring in a relative word. -/
def peripheralValues (w : List (RelLetter G Λ)) : Set G :=
  {x : G | ∃ a ∈ w, ∃ mu : Λ, a = RelLetter.comp mu x}

omit [Group G] in
theorem peripheralValues_finite (w : List (RelLetter G Λ)) :
    (peripheralValues w).Finite := by
  classical
  refine (w.toFinset.finite_toSet.image RelLetter.val).subset ?_
  rintro x ⟨a, ha, mu, rfl⟩
  exact ⟨RelLetter.comp mu x, by simpa using ha, rfl⟩

theorem peripheralValues_mem_family (D : RelGenSet G Λ)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) :
    ∀ x ∈ peripheralValues w, ∃ mu : Λ, x ∈ D.fam mu := by
  rintro x ⟨a, ha, mu, rfl⟩
  exact ⟨mu, hlet (RelLetter.comp mu x) ha⟩

/-- Add a set already contained in the peripheral family to the base.  The
carrier of the total relative alphabet is unchanged. -/
def adjoinPeripheralSet (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu) : RelGenSet G Λ where
  base := D.base ∪ N
  fam := D.fam
  symmetricGenerating := by
    have heq : (D.base ∪ N) ∪
        (⋃ mu : Λ, ((D.fam mu : Subgroup G) : Set G)) =
        D.base ∪ (⋃ mu : Λ, ((D.fam mu : Subgroup G) : Set G)) := by
      apply Set.Subset.antisymm
      · rintro x ((hx | hx) | hx)
        · exact Or.inl hx
        · obtain ⟨mu, hmu⟩ := hN x hx
          exact Or.inr (Set.mem_iUnion.mpr ⟨mu, hmu⟩)
        · exact Or.inr hx
      · rintro x (hx | hx)
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
    rw [heq]
    exact D.symmetricGenerating

@[simp] theorem adjoinPeripheralSet_base (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu) :
    (D.adjoinPeripheralSet N hN).base = D.base ∪ N := rfl

@[simp] theorem adjoinPeripheralSet_fam (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu) :
    (D.adjoinPeripheralSet N hN).fam = D.fam := rfl

/-! ## Expanding a bounded base spelling -/

/-- Every base letter of `D'` has a uniformly bounded spelling consisting only
of base letters of `D`. -/
def HasBoundedBaseSpellings (D D' : RelGenSet G Λ) (M : ℕ) : Prop :=
  ∀ x ∈ D'.base, ∃ q : List (RelLetter G Λ),
    (∀ a ∈ q, ∃ y ∈ D.base, a = RelLetter.base y) ∧
      RelLetter.listVal q = x ∧ q.length ≤ M

/-- Expand a word one letter at a time.  Base letters use the supplied
all-base spelling and peripheral letters stay singleton peripheral letters. -/
theorem exists_word_of_boundedBaseSpellings (D D' : RelGenSet G Λ)
    (hfam : D'.fam = D.fam) {M : ℕ} (hM : 1 ≤ M)
    (hbase : HasBoundedBaseSpellings D D' M) (lam : Λ) :
    ∀ (w : List (RelLetter G Λ)) (v : G),
      (∀ a ∈ w, D'.IsLetter a) → AvoidsFrom D'.fam lam w v →
      ∃ q : List (RelLetter G Λ),
        (∀ a ∈ q, D.IsLetter a) ∧
          RelLetter.listVal q = RelLetter.listVal w ∧
          AvoidsFrom D.fam lam q v ∧ q.length ≤ M * w.length := by
  intro w
  induction w with
  | nil =>
      intro v _ _
      exact ⟨[], by simp, rfl, trivial, by simp⟩
  | cons a t ih =>
      intro v hlet hav
      obtain ⟨havHead, havTail⟩ := hav
      have hletTail : ∀ b ∈ t, D'.IsLetter b :=
        fun b hb => hlet b (List.mem_cons_of_mem a hb)
      obtain ⟨qTail, hqTailLet, hqTailVal, hqTailAv, hqTailLen⟩ :=
        ih (v * a.val) hletTail havTail
      cases a with
      | base x =>
          obtain ⟨qHead, hqHeadBase, hqHeadVal, hqHeadLen⟩ :=
            hbase x (hlet (RelLetter.base x) List.mem_cons_self)
          have hqHeadLet : ∀ b ∈ qHead, D.IsLetter b := by
            intro b hb
            obtain ⟨y, hy, rfl⟩ := hqHeadBase b hb
            exact hy
          have hqHeadAv : AvoidsFrom D.fam lam qHead v :=
            OsinComponents.avoidsFrom_of_forall_base D.fam lam qHead v
              (fun b hb => by
                obtain ⟨y, -, hby⟩ := hqHeadBase b hb
                exact ⟨y, hby⟩)
          refine ⟨qHead ++ qTail, ?_, ?_, ?_, ?_⟩
          · intro b hb
            rcases List.mem_append.mp hb with hb | hb
            · exact hqHeadLet b hb
            · exact hqTailLet b hb
          · rw [OsinComponents.listVal_append, hqHeadVal, hqTailVal,
              OsinComponents.listVal_cons]
            rfl
          · rw [OsinComponents.avoidsFrom_append]
            refine ⟨hqHeadAv, ?_⟩
            rwa [hqHeadVal]
          · rw [List.length_append, List.length_cons, Nat.mul_succ]
            omega
      | comp mu x =>
          have hx : x ∈ D.fam mu := by
            have hx' : x ∈ D'.fam mu :=
              hlet (RelLetter.comp mu x) List.mem_cons_self
            rw [hfam] at hx'
            exact hx'
          refine ⟨RelLetter.comp mu x :: qTail, ?_, ?_, ?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hx
            · exact hqTailLet b hb
          · rw [OsinComponents.listVal_cons, hqTailVal]
            rfl
          · exact ⟨by simpa [hfam] using havHead, hqTailAv⟩
          · rw [List.length_cons, List.length_cons, Nat.mul_succ]
            omega

theorem relBall_subset_of_boundedBaseSpellings (D D' : RelGenSet G Λ)
    (hfam : D'.fam = D.fam) {M : ℕ} (hM : 1 ≤ M)
    (hbase : HasBoundedBaseSpellings D D' M) (lam : Λ) (n : ℕ) :
    D'.relBall lam n ⊆ D.relBall lam (M * n) := by
  rintro h ⟨hh, w, hlet, hval, hav, hlen⟩
  obtain ⟨q, hqlet, hqval, hqav, hqlen⟩ :=
    exists_word_of_boundedBaseSpellings D D' hfam hM hbase lam w 1 hlet hav
  refine ⟨?_, q, hqlet, ?_, hqav, hqlen.trans ?_⟩
  · rwa [← hfam]
  · rwa [hqval]
  · exact Nat.mul_le_mul_left M hlen

theorem relBall_finite_of_boundedBaseSpellings (D D' : RelGenSet G Λ)
    (hfam : D'.fam = D.fam) {M : ℕ} (hM : 1 ≤ M)
    (hbase : HasBoundedBaseSpellings D D' M) (lam : Λ)
    (hfin : ∀ n : ℕ, (D.relBall lam n).Finite) :
    ∀ n : ℕ, (D'.relBall lam n).Finite := by
  intro n
  exact (hfin (M * n)).subset
    (relBall_subset_of_boundedBaseSpellings D D' hfam hM hbase lam n)

/-! ## The one-pair local-finiteness theorem -/

/-- Demoting a word over `D` gives an all-base word after adjoining all of its
peripheral values to the base. -/
theorem forall_base_demote_adjoinPeripheralSet (D : RelGenSet G Λ)
    (N : Set G) (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hvals : peripheralValues w ⊆ N) :
    ∀ b ∈ OsinComponents.demote w, ∃ x ∈ (D.adjoinPeripheralSet N hN).base,
      b = RelLetter.base x := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  refine ⟨a.val, ?_, rfl⟩
  cases a with
  | base x => exact Or.inl (hlet (RelLetter.base x) ha)
  | comp mu x =>
      exact Or.inr (hvals ⟨RelLetter.comp mu x, ha, mu, rfl⟩)

/-- **The relative-metric half of DGO Corollary 4.27 for adjoining one pair.** -/
theorem pairLocalFiniteness : PairLocalFiniteness.{u, w} := by
  intro G _ Λ D hemb t lam n
  obtain ⟨wt, hwt⟩ := OsinComponents.existsGeodesicWord D 1 t
  obtain ⟨wi, hwi⟩ := OsinComponents.existsGeodesicWord D 1 t⁻¹
  let N : Set G := peripheralValues wt ∪ peripheralValues wi
  have hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu := by
    intro x hx
    rcases hx with hx | hx
    · exact peripheralValues_mem_family D hwt.1 x hx
    · exact peripheralValues_mem_family D hwi.1 x hx
  let D₀ : RelGenSet G Λ := D.adjoinPeripheralSet N hN
  have hNfin : N.Finite :=
    (peripheralValues_finite wt).union (peripheralValues_finite wi)
  have hD₀fin : ∀ m : ℕ, (D₀.relBall lam m).Finite :=
    OsinComponents.relBall_finite_of_base_subset' D D₀ lam rfl hN hNfin
      (by intro x hx; exact hx) (hemb.locallyFinite lam)
  let M : ℕ := max 1 (max wt.length wi.length)
  have hM : 1 ≤ M := le_max_left _ _
  have hbase : HasBoundedBaseSpellings D₀ (D.adjoinPair t) M := by
    intro x hx
    rcases hx with hx | hx | hx
    · refine ⟨[RelLetter.base x], ?_, ?_, ?_⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst a
        exact ⟨x, Or.inl hx, rfl⟩
      · simp [RelLetter.listVal, RelLetter.val]
      · simp [M, hM]
    · subst x
      refine ⟨OsinComponents.demote wt, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := forall_base_demote_adjoinPeripheralSet D N hN
          hwt.1 (Set.subset_union_left) a ha
        exact ⟨x, hx, rfl⟩
      · rw [OsinComponents.listVal_demote]
        simpa using hwt.2.1
      · rw [OsinComponents.length_demote]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
    · subst x
      refine ⟨OsinComponents.demote wi, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := forall_base_demote_adjoinPeripheralSet D N hN
          hwi.1 (Set.subset_union_right) a ha
        exact ⟨x, hx, rfl⟩
      · rw [OsinComponents.listVal_demote]
        simpa using hwi.2.1
      · rw [OsinComponents.length_demote]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
  exact relBall_finite_of_boundedBaseSpellings D₀ (D.adjoinPair t) rfl hM
    hbase lam hD₀fin n

end RelGenSet

end GGT
end GroupApproximation
