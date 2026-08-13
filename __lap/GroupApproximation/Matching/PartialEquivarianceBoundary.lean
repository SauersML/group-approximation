import GroupApproximation.Matching.FinitePartialBijection

/-!
# Agreement boundaries for partial intertwiners

For two partial bijections between labeled finite models, every labeled arc
crossing their agreement set is an equivariance failure of at least one map.
This is the finite combinatorial input for the component-cluster gap.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {L : Type*} [Fintype L]
variable {Y Z : FiniteModel}

/-- Tagged directed boundary for a finite family of actions. -/
noncomputable def taggedBoundary (act : L → Equiv.Perm Y)
    (A : Finset Y) : Finset (L × Y) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p ↦
    (p.2 ∈ A ∧ act p.1 p.2 ∉ A) ∨
      (p.2 ∉ A ∧ act p.1 p.2 ∈ A)

@[simp] theorem mem_taggedBoundary (act : L → Equiv.Perm Y)
    (A : Finset Y) (p : L × Y) :
    p ∈ taggedBoundary act A ↔
      (p.2 ∈ A ∧ act p.1 p.2 ∉ A) ∨
        (p.2 ∉ A ∧ act p.1 p.2 ∈ A) := by
  classical
  simp [taggedBoundary]

/-- Points where two partial maps are both defined and agree. -/
noncomputable def agreement (b c : FinitePartialBijection Y Z) : Finset Y :=
  Finset.univ \ b.disagreement c

@[simp] theorem mem_agreement (b c : FinitePartialBijection Y Z) (y : Y) :
    y ∈ b.agreement c ↔
      ∃ hb : y ∈ b.source, ∃ hc : y ∈ c.source,
        b.apply y hb = c.apply y hc := by
  classical
  simp only [agreement, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_disagreement]
  push Not
  rfl

@[simp] theorem mem_equivarianceDefect
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (p : L × Y) :
    p ∈ b.equivarianceDefect actY actZ ↔
      ∀ hx : p.2 ∈ b.source, ∀ hsx : actY p.1 p.2 ∈ b.source,
        b.apply (actY p.1 p.2) hsx ≠ actZ p.1 (b.apply p.2 hx) := by
  classical
  simp [equivarianceDefect]

/-- Every missing source point contributes one equivariance defect for every
label.  This lower bound is useful when small labelled defect must force a
partial bijection to be co-large. -/
theorem card_mul_sourceDefect_le_card_equivarianceDefect
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    Fintype.card L * b.sourceDefect ≤
      (b.equivarianceDefect actY actZ).card := by
  classical
  let Missing := {y // y ∈ Finset.univ \ b.source}
  let charge : L × Missing →
      {p // p ∈ b.equivarianceDefect actY actZ} := fun p ↦ by
    refine ⟨(p.1, p.2.1), ?_⟩
    rw [mem_equivarianceDefect]
    intro hy
    exact ((Finset.mem_sdiff.mp p.2.2).2 hy).elim
  have hcharge : Function.Injective charge := by
    intro p q hpq
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1.1) hpq
    · apply Subtype.ext
      exact congrArg (fun x ↦ x.1.2) hpq
  have hcard := Fintype.card_le_of_injective charge hcharge
  have hmissing : (Finset.univ \ b.source).card = b.sourceDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ b.source)]
    simp [FinitePartialBijection.sourceDefect]
  dsimp only [Missing] at hcard
  simpa only [Fintype.card_prod, Fintype.card_coe, hmissing] using hcard

/-- Backward equivariance defects likewise contain every missing target for
every label. -/
theorem card_mul_targetDefect_le_card_symm_equivarianceDefect
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    Fintype.card L * b.targetDefect ≤
      (b.symm.equivarianceDefect actZ actY).card := by
  simpa only [sourceDefect_symm] using
    card_mul_sourceDefect_le_card_equivarianceDefect
      b.symm actZ actY

/-- Every labeled boundary arc of the agreement set is an equivariance
failure of one of the two partial maps. -/
theorem taggedBoundary_agreement_subset_equivarianceDefect_union
    [DecidableEq L]
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b c : FinitePartialBijection Y Z) :
    taggedBoundary actY (b.agreement c) ⊆
      b.equivarianceDefect actY actZ ∪
        c.equivarianceDefect actY actZ := by
  classical
  intro p hp
  rw [mem_taggedBoundary] at hp
  by_cases hbdef : p ∈ b.equivarianceDefect actY actZ
  · exact Finset.mem_union_left _ hbdef
  by_cases hcdef : p ∈ c.equivarianceDefect actY actZ
  · exact Finset.mem_union_right _ hcdef
  rw [mem_equivarianceDefect] at hbdef hcdef
  push Not at hbdef hcdef
  obtain ⟨hby, hbsy, hbeq⟩ := hbdef
  obtain ⟨hcy, hcsy, hceq⟩ := hcdef
  rcases hp with ⟨hy, hsy⟩ | ⟨hy, hsy⟩
  · obtain ⟨hby', hcy', hyEq⟩ := (mem_agreement b c p.2).1 hy
    have hcontra : b.apply (actY p.1 p.2) hbsy =
        c.apply (actY p.1 p.2) hcsy := by
      calc
        b.apply (actY p.1 p.2) hbsy = actZ p.1 (b.apply p.2 hby) := hbeq
        _ = actZ p.1 (b.apply p.2 hby') := by congr
        _ = actZ p.1 (c.apply p.2 hcy') := congrArg (actZ p.1) hyEq
        _ = actZ p.1 (c.apply p.2 hcy) := by congr
        _ = c.apply (actY p.1 p.2) hcsy := hceq.symm
    exact (hsy ((mem_agreement b c _).2 ⟨hbsy, hcsy, hcontra⟩)).elim
  · obtain ⟨hbsy', hcsy', hsyEq⟩ :=
      (mem_agreement b c (actY p.1 p.2)).1 hsy
    have himage : actZ p.1 (b.apply p.2 hby) =
        actZ p.1 (c.apply p.2 hcy) := by
      calc
        actZ p.1 (b.apply p.2 hby) = b.apply (actY p.1 p.2) hbsy := hbeq.symm
        _ = b.apply (actY p.1 p.2) hbsy' := by congr
        _ = c.apply (actY p.1 p.2) hcsy' := hsyEq
        _ = c.apply (actY p.1 p.2) hcsy := by congr
        _ = actZ p.1 (c.apply p.2 hcy) := hceq
    have hyEq : b.apply p.2 hby = c.apply p.2 hcy :=
      (actZ p.1).injective himage
    exact (hy ((mem_agreement b c _).2 ⟨hby, hcy, hyEq⟩)).elim

/-- Cardinal form of the agreement-boundary estimate. -/
theorem card_taggedBoundary_agreement_le
    [DecidableEq L]
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b c : FinitePartialBijection Y Z) :
    (taggedBoundary actY (b.agreement c)).card ≤
      (b.equivarianceDefect actY actZ).card +
        (c.equivarianceDefect actY actZ).card := by
  exact (Finset.card_le_card
    (taggedBoundary_agreement_subset_equivarianceDefect_union
      actY actZ b c)).trans (Finset.card_union_le _ _)

/-- Tagged expansion at and above a chosen finite scale. -/
def HasTaggedExpansionAtScale (act : L → Equiv.Perm Y) (h : ℝ)
    (m : ℕ) : Prop :=
  0 < h ∧ ∀ A : Finset Y, m ≤ A.card →
    2 * A.card ≤ Fintype.card Y →
      h * A.card ≤ (taggedBoundary act A).card

theorem taggedBoundary_compl (act : L → Equiv.Perm Y) (A : Finset Y) :
    taggedBoundary act (Finset.univ \ A) = taggedBoundary act A := by
  classical
  ext p
  simp only [mem_taggedBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases hy : p.2 ∈ A <;> by_cases hsy : act p.1 p.2 ∈ A <;>
    simp [hy, hsy]

theorem agreement_union_disagreement
    (b c : FinitePartialBijection Y Z) :
    b.agreement c ∪ b.disagreement c = Finset.univ := by
  classical
  simp [agreement]

theorem agreement_disjoint_disagreement
    (b c : FinitePartialBijection Y Z) :
    Disjoint (b.agreement c) (b.disagreement c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hy hdis
  exact (Finset.mem_sdiff.mp hy).2 hdis

theorem card_agreement_add_card_disagreement
    (b c : FinitePartialBijection Y Z) :
    (b.agreement c).card + (b.disagreement c).card = Fintype.card Y := by
  rw [← Finset.card_union_of_disjoint (agreement_disjoint_disagreement b c),
    agreement_union_disagreement]
  exact Finset.card_univ

/-- Partial-intertwiner separation on an expanding source model: two maps
with small combined equivariance defect cannot have both a large agreement
set and a large disagreement set. -/
theorem agreement_or_disagreement_small
    [DecidableEq L]
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    {h : ℝ} (b c : FinitePartialBijection Y Z) (m : ℕ)
    (hexp : HasTaggedExpansionAtScale actY h m)
    (hdefect : (((b.equivarianceDefect actY actZ).card +
      (c.equivarianceDefect actY actZ).card : ℕ) : ℝ) < h * m) :
    (b.agreement c).card < m ∨ (b.disagreement c).card < m := by
  by_contra hsmall
  push Not at hsmall
  have hboundary := card_taggedBoundary_agreement_le actY actZ b c
  by_cases hhalf : 2 * (b.agreement c).card ≤ Fintype.card Y
  · have hexpand := hexp.2 (b.agreement c) hsmall.1 hhalf
    have hmcast : (m : ℝ) ≤ ((b.agreement c).card : ℝ) := by
      exact_mod_cast hsmall.1
    have hscale : h * m ≤ h * (b.agreement c).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundarycast : ((taggedBoundary actY (b.agreement c)).card : ℝ) ≤
        ((b.equivarianceDefect actY actZ).card +
          (c.equivarianceDefect actY actZ).card : ℕ) := by
      exact_mod_cast hboundary
    linarith
  · have hhalf' : 2 * (b.disagreement c).card ≤ Fintype.card Y := by
      have hpartition := card_agreement_add_card_disagreement b c
      omega
    have hexpand := hexp.2 (b.disagreement c) hsmall.2 hhalf'
    have hmcast : (m : ℝ) ≤ ((b.disagreement c).card : ℝ) := by
      exact_mod_cast hsmall.2
    have hscale : h * m ≤ h * (b.disagreement c).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundaries : taggedBoundary actY (b.disagreement c) =
        taggedBoundary actY (b.agreement c) := by
      rw [agreement]
      exact (taggedBoundary_compl actY (b.disagreement c)).symm
    have hboundarycast : ((taggedBoundary actY (b.disagreement c)).card : ℝ) ≤
        ((b.equivarianceDefect actY actZ).card +
          (c.equivarianceDefect actY actZ).card : ℕ) := by
      rw [hboundaries]
      exact_mod_cast hboundary
    linarith

/-- Applying partial-intertwiner separation in both directions gives the
eight-radius gap required by `FinitePartialClusterData`.  The factor
seventeen leaves sixteen scales of disagreement when an agreement set has
size below `m`; the near radius is `2m`, one copy for each direction. -/
theorem twoSidedDisagreement_lt_two_mul_or_eight_radius_le
    [DecidableEq L]
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    {h : ℝ} (b c : FinitePartialBijection Y Z) (m : ℕ)
    (hexpY : HasTaggedExpansionAtScale actY h m)
    (hexpZ : HasTaggedExpansionAtScale actZ h m)
    (hsizeY : 17 * m ≤ Fintype.card Y)
    (hsizeZ : 17 * m ≤ Fintype.card Z)
    (hforward : (((b.equivarianceDefect actY actZ).card +
      (c.equivarianceDefect actY actZ).card : ℕ) : ℝ) < h * m)
    (hbackward : (((b.symm.equivarianceDefect actZ actY).card +
      (c.symm.equivarianceDefect actZ actY).card : ℕ) : ℝ) < h * m) :
    b.twoSidedDisagreement c < 2 * m ∨
      8 * (2 * m) ≤ b.twoSidedDisagreement c := by
  have hsource := agreement_or_disagreement_small
    actY actZ b c m hexpY hforward
  have htarget := agreement_or_disagreement_small
    actZ actY b.symm c.symm m hexpZ hbackward
  rcases hsource with hsourceAgree | hsourceDis
  · right
    have hpartition := card_agreement_add_card_disagreement b c
    unfold FinitePartialBijection.twoSidedDisagreement
    omega
  · rcases htarget with htargetAgree | htargetDis
    · right
      have hpartition := card_agreement_add_card_disagreement b.symm c.symm
      unfold FinitePartialBijection.twoSidedDisagreement
      omega
    · left
      unfold FinitePartialBijection.twoSidedDisagreement
      omega

end FinitePartialBijection
end GroupApproximation
