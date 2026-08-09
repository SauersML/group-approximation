import NonsoficGroupsExist.Kazhdan.Kazhdan

/-!
# Quantitative quasi-cocycle rigidity

This file isolates two general mechanisms used in the Leavitt rigidity
argument.

* A quasi-cocycle into a representation without invariant vectors is
  quantitatively bounded on the centre of a group carrying a Kazhdan pair.
* Relative `(TT)/T` globalizes whenever the group is a bounded product of
  finitely many fixed conjugates of the relatively rigid subgroup.

The second statement is deliberately independent of any matrix calculation.
The strong-division Gaussian elimination for the binary Leavitt group is the
algebraic input which supplies its bounded-product hypothesis.
-/

namespace NonsoficGroupsExist

universe u v

section Definitions

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `b` is a quasi-cocycle of defect at most `D` for the orthogonal
representation `π`. -/
def IsQuasiCocycleWithDefect (π : G →* (E ≃ₗᵢ[ℝ] E))
    (b : G → E) (D : ℝ) : Prop :=
  ∀ g h : G, ‖b (g * h) - (b g + π g (b h))‖ ≤ D

/-- A map is uniformly bounded on a subset. -/
def IsBoundedOn (b : G → E) (S : Set G) : Prop :=
  ∃ C : ℝ, ∀ g ∈ S, ‖b g‖ ≤ C

/-- The union of the conjugates of `H` by a fixed finite set. -/
def finiteConjugates (H : Subgroup G) (C : Finset G) : Set G :=
  {x | ∃ c ∈ C, ∃ h ∈ H, x = c * h * c⁻¹}

/-- A set boundedly generates the group in at most `n` factors. -/
def IsBoundedlyGeneratedBy (S : Set G) (n : ℕ) : Prop :=
  ∀ g : G, ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = g

/-- Relative property `(TT)/T`, in the no-invariant-vectors formulation. -/
def HasRelativePropertyTTModuloT (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ (π : G →* (E ≃ₗᵢ[ℝ] E)),
      IsKazhdanPair.HasNoInvariantVectors G π →
      ∀ (b : G → E), (∃ D : ℝ, IsQuasiCocycleWithDefect π b D) →
        IsBoundedOn b (H : Set G)

/-- Property `(TT)/T`, in the no-invariant-vectors formulation. -/
def HasPropertyTTModuloT (G : Type u) [Group G] : Prop :=
  HasRelativePropertyTTModuloT.{u, v} G ⊤

end Definitions

namespace IsQuasiCocycleWithDefect

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {π : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} {D : ℝ}

/-- The quasi-cocycle inequality in triangle-inequality form. -/
theorem norm_mul_le (hb : IsQuasiCocycleWithDefect π b D) (g h : G) :
    ‖b (g * h)‖ ≤ ‖b g‖ + ‖b h‖ + D := by
  have hdef := hb g h
  have hsplit : b (g * h) =
      (b (g * h) - (b g + π g (b h))) + (b g + π g (b h)) := by
    abel
  rw [hsplit]
  calc
    ‖(b (g * h) - (b g + π g (b h))) + (b g + π g (b h))‖ ≤
        ‖b (g * h) - (b g + π g (b h))‖ +
          ‖b g + π g (b h)‖ := norm_add_le _ _
    _ ≤ D + (‖b g‖ + ‖π g (b h)‖) := add_le_add hdef (norm_add_le _ _)
    _ = ‖b g‖ + ‖b h‖ + D := by
      rw [(π g).norm_map]
      ring

/-- Even without normalizing `b 1 = 0`, its value at the identity is at
most the defect. -/
theorem norm_one_le (hb : IsQuasiCocycleWithDefect π b D) : ‖b 1‖ ≤ D := by
  have h := hb 1 1
  simpa using h

/-- A product of `m` elements on which `b` is bounded by `M` has the
expected linear quasi-cocycle bound. -/
theorem norm_list_prod_le (hb : IsQuasiCocycleWithDefect π b D)
    {S : Set G} {M : ℝ} (hS : ∀ g ∈ S, ‖b g‖ ≤ M)
    (l : List G) (hl : ∀ g ∈ l, g ∈ S) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * M + (l.length + 1 : ℕ) * D := by
  induction l with
  | nil =>
      simpa using hb.norm_one_le
  | cons g l ih =>
      have hgS : g ∈ S := hl g (by simp)
      have hlS : ∀ x ∈ l, x ∈ S := by
        intro x hx
        exact hl x (by simp [hx])
      calc
        ‖b (g :: l).prod‖ = ‖b (g * l.prod)‖ := by simp
        _ ≤ ‖b g‖ + ‖b l.prod‖ + D := hb.norm_mul_le g l.prod
        _ ≤ M + ((l.length : ℝ) * M + (l.length + 1 : ℕ) * D) + D :=
          add_le_add (add_le_add (hS g hgS) (ih hlS)) le_rfl
        _ = (((g :: l).length : ℝ) * M +
            ((g :: l).length + 1 : ℕ) * D) := by
          simp
          ring

/-- Boundedness on a set globalizes across a bounded product. -/
theorem boundedOn_of_boundedlyGenerated
    (hb : IsQuasiCocycleWithDefect π b D)
    {S : Set G} {n : ℕ} (hgen : IsBoundedlyGeneratedBy S n)
    (hS : IsBoundedOn b S) : IsBoundedOn b Set.univ := by
  obtain ⟨M, hM⟩ := hS
  let M' : ℝ := max M 0
  have hM' : ∀ g ∈ S, ‖b g‖ ≤ M' := by
    intro g hg
    exact (hM g hg).trans (le_max_left _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  refine ⟨(n : ℝ) * M' + (n + 1 : ℕ) * D, ?_⟩
  intro g _
  obtain ⟨l, hlen, hl, rfl⟩ := hgen g
  have hbound := hb.norm_list_prod_le hM' l hl
  calc
    ‖b l.prod‖ ≤ (l.length : ℝ) * M' + (l.length + 1 : ℕ) * D := hbound
    _ ≤ (n : ℝ) * M' + (n + 1 : ℕ) * D := by
      have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hb.norm_one_le)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hM'0)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hlen 1) hD0)

/-- A bound transfers to a fixed conjugate, with an explicit cost for the
conjugator and two additional defects. -/
theorem norm_conjugate_le (hb : IsQuasiCocycleWithDefect π b D)
    (c h : G) :
    ‖b (c * h * c⁻¹)‖ ≤ ‖b c‖ + ‖b h‖ + ‖b c⁻¹‖ + 2 * D := by
  calc
    ‖b (c * h * c⁻¹)‖ ≤ ‖b (c * h)‖ + ‖b c⁻¹‖ + D :=
      hb.norm_mul_le (c * h) c⁻¹
    _ ≤ (‖b c‖ + ‖b h‖ + D) + ‖b c⁻¹‖ + D :=
      add_le_add (add_le_add (hb.norm_mul_le c h) le_rfl) le_rfl
    _ = ‖b c‖ + ‖b h‖ + ‖b c⁻¹‖ + 2 * D := by ring

end IsQuasiCocycleWithDefect

/-! ### The quantitative central bound -/

theorem quasiCocycle_norm_le_on_center
    {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (π : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G π)
    (b : G → E) {D M : ℝ} (hb : IsQuasiCocycleWithDefect π b D)
    (hD0 : 0 ≤ D) (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ Q, ‖b q‖ ≤ M) (z : Subgroup.center G) :
    ‖b z‖ ≤ (2 * D + 2 * M) / ε := by
  by_cases hz0 : b z = 0
  · rw [hz0, norm_zero]
    exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) hD0)
      (mul_nonneg (by norm_num) hM0)) hQ.1.le
  obtain ⟨q, hqQ, hmove⟩ :=
    hQ.exists_moved_mul_norm_of_noInvariant π hno (b z) hz0
  have hcentral : q * (z : G) = (z : G) * q :=
    (Semigroup.mem_center_iff.mp z.property) q
  let e₁ : E := b (q * (z : G)) - (b q + π q (b z))
  let e₂ : E := b ((z : G) * q) - (b z + π z (b q))
  have he₁ : ‖e₁‖ ≤ D := hb q z
  have he₂ : ‖e₂‖ ≤ D := hb z q
  have hid : π q (b z) - b z = (π z (b q) - b q) + (e₂ - e₁) := by
    dsimp [e₁, e₂]
    rw [hcentral]
    abel
  have hdisp : ‖π q (b z) - b z‖ ≤ 2 * M + 2 * D := by
    rw [hid]
    calc
      ‖(π z (b q) - b q) + (e₂ - e₁)‖ ≤
          ‖π z (b q) - b q‖ + ‖e₂ - e₁‖ := norm_add_le _ _
      _ ≤ (‖π z (b q)‖ + ‖b q‖) + (‖e₂‖ + ‖e₁‖) :=
        add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ ≤ (M + M) + (D + D) := by
        rw [(π z).norm_map]
        exact add_le_add (add_le_add (hM q hqQ) (hM q hqQ))
          (add_le_add he₂ he₁)
      _ = 2 * M + 2 * D := by ring
  have hmul : ε * ‖b z‖ ≤ 2 * D + 2 * M := by
    calc
      ε * ‖b z‖ ≤ ‖π q (b z) - b z‖ := hmove
      _ ≤ 2 * M + 2 * D := hdisp
      _ = 2 * D + 2 * M := by ring
  exact (le_div_iff₀ hQ.1).mpr (by simpa [mul_comm] using hmul)

/-- **Kazhdan central boundedness.** Every quasi-cocycle into a complete
orthogonal representation without invariant vectors is uniformly bounded on
the centre.  The witness is completely explicit in terms of the Kazhdan pair,
the defect, and the values on the finite Kazhdan set. -/
theorem quasiCocycle_boundedOn_center
    {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (π : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G π)
    (b : G → E) {D : ℝ} (hb : IsQuasiCocycleWithDefect π b D) :
    IsBoundedOn b (Subgroup.center G : Set G) := by
  classical
  let D' : ℝ := max D 0
  let M : ℝ := ∑ q ∈ Q, ‖b q‖
  have hD0 : 0 ≤ D' := le_max_right _ _
  have hb' : IsQuasiCocycleWithDefect π b D' := by
    intro g h
    exact (hb g h).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hM : ∀ q ∈ Q, ‖b q‖ ≤ M := by
    intro q hq
    exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (b i)) hq
  refine ⟨(2 * D' + 2 * M) / ε, ?_⟩
  intro z hz
  exact quasiCocycle_norm_le_on_center hQ π hno b hb' hD0 hM0 hM ⟨z, hz⟩

/-! ### Globalization from finitely many conjugates -/

theorem boundedOn_finiteConjugates
    {G : Type u} [Group G]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (π : G →* (E ≃ₗᵢ[ℝ] E)) (b : G → E) {D : ℝ}
    (hb : IsQuasiCocycleWithDefect π b D) (H : Subgroup G)
    (C : Finset G) (hH : IsBoundedOn b (H : Set G)) :
    IsBoundedOn b (finiteConjugates H C) := by
  classical
  obtain ⟨M, hM⟩ := hH
  let K : ℝ := ∑ c ∈ C, (‖b c‖ + ‖b c⁻¹‖)
  refine ⟨M + K + 2 * D, ?_⟩
  intro x hx
  obtain ⟨c, hc, h, hh, rfl⟩ := hx
  have hcK : ‖b c‖ + ‖b c⁻¹‖ ≤ K := by
    exact Finset.single_le_sum (fun i _ ↦ add_nonneg (norm_nonneg (b i))
      (norm_nonneg (b i⁻¹))) hc
  calc
    ‖b (c * (h : G) * c⁻¹)‖ ≤
        ‖b c‖ + ‖b h‖ + ‖b c⁻¹‖ + 2 * D := hb.norm_conjugate_le c h
    _ ≤ M + K + 2 * D := by linarith [hM h hh]

/-- **Finite-conjugate globalization.** Relative `(TT)/T` becomes global
`(TT)/T` as soon as finitely many fixed conjugates of the relative subgroup
boundedly generate the group. -/
theorem hasPropertyTTModuloT_of_finiteConjugates
    {G : Type u} [Group G] (H : Subgroup G) (C : Finset G) (n : ℕ)
    (hrel : HasRelativePropertyTTModuloT.{u, v} G H)
    (hgen : IsBoundedlyGeneratedBy (finiteConjugates H C) n) :
    HasPropertyTTModuloT.{u, v} G := by
  intro E _ _ _ π hno b hb
  obtain ⟨D, hD⟩ := hb
  have hH := hrel E π hno b ⟨D, hD⟩
  have hconj := boundedOn_finiteConjugates π b hD H C hH
  exact hD.boundedOn_of_boundedlyGenerated hgen hconj

end NonsoficGroupsExist
