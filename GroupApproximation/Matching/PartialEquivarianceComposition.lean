import GroupApproximation.Matching.PartialEquivarianceBoundary

/-!
# Equivariance defects under partial composition

A labeled defect of a composite occurs either in its first arrow or pulls
back from a defect of its second arrow.  Injectivity of the first partial
bijection makes this pullback cardinality no larger than the second defect.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {Y Z W : FiniteModel}

/-- Defects of the second arrow pulled back through the first partial
bijection. -/
noncomputable def pulledEquivarianceDefect
    (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W)
    (actZ : L → Equiv.Perm Z) (actW : L → Equiv.Perm W) :
    Finset (L × Y) := by
  classical
  exact Finset.univ.filter fun p ↦
    ∃ hy : p.2 ∈ b.source,
      (p.1, b.apply p.2 hy) ∈ c.equivarianceDefect actZ actW

@[simp] theorem mem_pulledEquivarianceDefect
    (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W)
    (actZ : L → Equiv.Perm Z) (actW : L → Equiv.Perm W)
    (p : L × Y) :
    p ∈ b.pulledEquivarianceDefect c actZ actW ↔
      ∃ hy : p.2 ∈ b.source,
        (p.1, b.apply p.2 hy) ∈ c.equivarianceDefect actZ actW := by
  classical
  simp [pulledEquivarianceDefect]

theorem card_pulledEquivarianceDefect_le
    (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W)
    (actZ : L → Equiv.Perm Z) (actW : L → Equiv.Perm W) :
    (b.pulledEquivarianceDefect c actZ actW).card ≤
      (c.equivarianceDefect actZ actW).card := by
  classical
  let F : {p // p ∈ b.pulledEquivarianceDefect c actZ actW} →
      {q // q ∈ c.equivarianceDefect actZ actW} := fun p ↦ by
    let hp := (mem_pulledEquivarianceDefect b c actZ actW p.1).mp p.2
    exact ⟨(p.1.1, b.apply p.1.2 hp.choose), hp.choose_spec⟩
  have hF : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun r ↦ r.1.1) hpq
    · apply b.apply_injective
        ((mem_pulledEquivarianceDefect b c actZ actW p.1).mp p.2).choose
        ((mem_pulledEquivarianceDefect b c actZ actW q.1).mp q.2).choose
      exact congrArg (fun r ↦ r.1.2) hpq
  have hcard := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe] using hcard

/-- Every composite defect is charged to a first-arrow defect or a pulled
second-arrow defect. -/
theorem equivarianceDefect_trans_subset
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (actW : L → Equiv.Perm W)
    (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    (b.trans c).equivarianceDefect actY actW ⊆
      b.equivarianceDefect actY actZ ∪
        b.pulledEquivarianceDefect c actZ actW := by
  classical
  intro p hp
  by_cases hb : p ∈ b.equivarianceDefect actY actZ
  · exact Finset.mem_union_left _ hb
  by_cases hc : p ∈ b.pulledEquivarianceDefect c actZ actW
  · exact Finset.mem_union_right _ hc
  rw [mem_equivarianceDefect] at hp hb
  push Not at hb
  obtain ⟨hby, hbsy, hbeq⟩ := hb
  have hcnot : (p.1, b.apply p.2 hby) ∉
      c.equivarianceDefect actZ actW := by
    intro hbad
    apply hc
    exact (mem_pulledEquivarianceDefect b c actZ actW p).mpr ⟨hby, hbad⟩
  rw [mem_equivarianceDefect] at hcnot
  push Not at hcnot
  obtain ⟨hcy, hcsy, hceq⟩ := hcnot
  have hsource : p.2 ∈ (b.trans c).source :=
    (b.mem_trans_source c p.2).mpr ⟨hby, hcy⟩
  have hcsy' : b.apply (actY p.1 p.2) hbsy ∈ c.source := by
    simpa only [hbeq] using hcsy
  have hssource : actY p.1 p.2 ∈ (b.trans c).source :=
    (b.mem_trans_source c (actY p.1 p.2)).mpr ⟨hbsy, hcsy'⟩
  exfalso
  apply hp hsource hssource
  simp only [trans_apply]
  calc
    c.apply (b.apply (actY p.1 p.2) _) _ =
        c.apply (actZ p.1 (b.apply p.2 hby)) hcsy := by
          congr
    _ = actW p.1 (c.apply (b.apply p.2 hby) hcy) := hceq
    _ = actW p.1 ((b.trans c).apply p.2 hsource) := by
          congr

/-- Cardinal subadditivity of labeled equivariance defects under partial
composition. -/
theorem card_equivarianceDefect_trans_le
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (actW : L → Equiv.Perm W)
    (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    ((b.trans c).equivarianceDefect actY actW).card ≤
      (b.equivarianceDefect actY actZ).card +
        (c.equivarianceDefect actZ actW).card := by
  calc
    ((b.trans c).equivarianceDefect actY actW).card ≤
        (b.equivarianceDefect actY actZ ∪
          b.pulledEquivarianceDefect c actZ actW).card :=
      Finset.card_le_card (equivarianceDefect_trans_subset
        actY actZ actW b c)
    _ ≤ (b.equivarianceDefect actY actZ).card +
        (b.pulledEquivarianceDefect c actZ actW).card :=
      Finset.card_union_le _ _
    _ ≤ (b.equivarianceDefect actY actZ).card +
        (c.equivarianceDefect actZ actW).card :=
      Nat.add_le_add_left
        (card_pulledEquivarianceDefect_le b c actZ actW) _

end FinitePartialBijection
end GroupApproximation
