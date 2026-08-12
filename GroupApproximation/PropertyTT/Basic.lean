import GroupApproximation.Kazhdan.KazhdanComplex

/-!
# Quasi-cocycles and property `(TT)/T`

This file defines property `(TT)/T` directly for complex unitary
representations and proves the elementary globalization mechanism used for
Leavitt elementary groups.  No rigidity theorem is imported: in particular,
the relative `(TT)/T` input required by an application must itself be proved
in Lean.
-/

namespace GroupApproximation

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A complex unitary representation has no nonzero invariant vector. -/
def HasNoInvariantVectorsComplex
    (G : Type u) [Group G] (rho : G →* (E ≃ₗᵢ[ℂ] E)) : Prop :=
  ∀ x : E, (∀ g : G, rho g x = x) → x = 0

/-- A map is a quasi-cocycle of defect at most `D` for `rho`. -/
def IsQuasiCocycle (rho : G →* (E ≃ₗᵢ[ℂ] E))
    (b : G → E) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ g h : G,
    ‖b (g * h) - b g - rho g (b h)‖ ≤ D

/-- Norm-boundedness of a map on a subset. -/
def IsNormBoundedOn (b : G → E) (S : Set G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ S, ‖b g‖ ≤ C

/-- Relative `(TT)` for a subgroup: every quasi-cocycle into every unitary
representation is bounded on the subgroup.  Unlike relative `(TT)/T`, this
does not discard representations with invariant vectors. -/
def HasRelativeTT (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E],
    ∀ (rho : G →* (E ≃ₗᵢ[ℂ] E)),
      ∀ (b : G → E) (D : ℝ), IsQuasiCocycle rho b D →
        IsNormBoundedOn b (H : Set G)

/-- Relative `(TT)/T` for a subgroup: every quasi-cocycle into a unitary
representation without invariant vectors is bounded on the subgroup. -/
def HasRelativeTTmodT (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E],
    ∀ (rho : G →* (E ≃ₗᵢ[ℂ] E)),
      HasNoInvariantVectorsComplex G rho →
      ∀ (b : G → E) (D : ℝ), IsQuasiCocycle rho b D →
        IsNormBoundedOn b (H : Set G)

/-- Full relative `(TT)` implies relative `(TT)/T` by forgetting the
no-invariant-vector hypothesis. -/
theorem HasRelativeTT.toRelativeTTmodT {H : Subgroup G}
    (h : HasRelativeTT.{u, v} G H) : HasRelativeTTmodT.{u, v} G H := by
  intro E _ _ _ rho _ b D hb
  exact h E rho b D hb

/-- Relative `(TT)/T` for a subset rather than a subgroup. -/
def HasRelativeTTmodTOnSet (G : Type u) [Group G] (S : Set G) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E],
    ∀ (rho : G →* (E ≃ₗᵢ[ℂ] E)),
      HasNoInvariantVectorsComplex G rho →
      ∀ (b : G → E) (D : ℝ), IsQuasiCocycle rho b D →
        IsNormBoundedOn b S

/-- Property `(TT)/T`: every quasi-cocycle into a unitary representation
without invariant vectors is bounded on the whole group. -/
def HasTTmodT (G : Type u) [Group G] : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E],
    ∀ (rho : G →* (E ≃ₗᵢ[ℂ] E)),
      HasNoInvariantVectorsComplex G rho →
      ∀ (b : G → E) (D : ℝ), IsQuasiCocycle rho b D →
        IsNormBoundedOn b Set.univ

/-! ## Quotient permanence -/

namespace HasTTmodT

variable {H : Type*} [Group H]

/-- Property `(TT)/T` descends through a surjective homomorphism. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (hG : HasTTmodT.{u, v} G) : HasTTmodT.{_, v} H := by
  intro E _ _ _ rho hno b D hb
  let rhoG : G →* (E ≃ₗᵢ[ℂ] E) := rho.comp f
  have hnoG : HasNoInvariantVectorsComplex G rhoG := by
    intro x hx
    apply hno x
    intro h
    obtain ⟨g, rfl⟩ := hf h
    exact hx g
  have hbG : IsQuasiCocycle rhoG (b ∘ f) D := by
    refine ⟨hb.1, ?_⟩
    intro g k
    simpa [rhoG, Function.comp_apply] using hb.2 (f g) (f k)
  obtain ⟨C, hC, hbound⟩ := hG E rhoG hnoG (b ∘ f) D hbG
  refine ⟨C, hC, ?_⟩
  intro h _
  obtain ⟨g, rfl⟩ := hf h
  exact hbound g (Set.mem_univ g)

/-- Property `(TT)/T` transports across a group isomorphism. -/
theorem of_mulEquiv (e : G ≃* H) (hH : HasTTmodT.{_, v} H) :
    HasTTmodT.{u, v} G :=
  hH.of_surjective e.symm.toMonoidHom e.symm.surjective

end HasTTmodT

namespace HasRelativeTTmodT

variable {H : Type*} [Group H]

/-- Relative `(TT)/T` descends through a surjection when the source
subgroup maps onto the target subgroup. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (K : Subgroup G) (L : Subgroup H) (himage : L ≤ K.map f)
    (hrel : HasRelativeTTmodT.{u, v} G K) :
    HasRelativeTTmodT.{_, v} H L := by
  intro E _ _ _ rho hno b D hb
  let rhoG : G →* (E ≃ₗᵢ[ℂ] E) := rho.comp f
  have hnoG : HasNoInvariantVectorsComplex G rhoG := by
    intro x hx
    apply hno x
    intro h
    obtain ⟨g, rfl⟩ := hf h
    exact hx g
  have hbG : IsQuasiCocycle rhoG (b ∘ f) D := by
    refine ⟨hb.1, ?_⟩
    intro g k
    simpa [rhoG, Function.comp_apply] using hb.2 (f g) (f k)
  obtain ⟨C, hC, hbound⟩ := hrel E rhoG hnoG (b ∘ f) D hbG
  refine ⟨C, hC, ?_⟩
  intro h hh
  obtain ⟨g, hgK, hgf⟩ := himage hh
  rw [← hgf]
  exact hbound g hgK

end HasRelativeTTmodT

namespace IsQuasiCocycle

variable {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}

/-- One quasi-cocycle multiplication step. -/
theorem norm_mul_le (hb : IsQuasiCocycle rho b D) (g h : G) :
    ‖b (g * h)‖ ≤ ‖b g‖ + ‖b h‖ + D := by
  have herr := hb.2 g h
  have hid : b (g * h) =
      (b (g * h) - b g - rho g (b h)) + b g + rho g (b h) := by
    abel
  rw [hid]
  calc
    ‖(b (g * h) - b g - rho g (b h)) + b g + rho g (b h)‖ ≤
        ‖(b (g * h) - b g - rho g (b h)) + b g‖ +
          ‖rho g (b h)‖ := norm_add_le _ _
    _ ≤ (‖b (g * h) - b g - rho g (b h)‖ + ‖b g‖) +
          ‖rho g (b h)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ D + ‖b g‖ + ‖b h‖ := by
      rw [(rho g).norm_map]
      gcongr
    _ = ‖b g‖ + ‖b h‖ + D := by ring

/-- The value at the identity is bounded by the defect. -/
theorem norm_one_le (hb : IsQuasiCocycle rho b D) : ‖b 1‖ ≤ D := by
  have h := hb.2 1 1
  simpa using h

/-- A product of a bounded list has a bound linear in its length. -/
theorem norm_list_prod_le (hb : IsQuasiCocycle rho b D)
    (l : List G) {C : ℝ} (hl : ∀ g ∈ l, ‖b g‖ ≤ C) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * C + (l.length + 1 : ℕ) * D := by
  induction l with
  | nil =>
      simpa using hb.norm_one_le
  | cons g l ih =>
      rw [List.prod_cons]
      have hg : ‖b g‖ ≤ C := hl g (by simp)
      have htail : ∀ h ∈ l, ‖b h‖ ≤ C := by
        intro h hh
        exact hl h (by simp [hh])
      calc
        ‖b (g * l.prod)‖ ≤ ‖b g‖ + ‖b l.prod‖ + D := hb.norm_mul_le g l.prod
        _ ≤ C + ((l.length : ℝ) * C + (l.length + 1 : ℕ) * D) + D := by
          gcongr
          exact ih htail
        _ = ((g :: l).length : ℝ) * C +
            ((g :: l).length + 1 : ℕ) * D := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Boundedness transports to a fixed conjugate of a subset. -/
theorem boundedOn_conjugate (hb : IsQuasiCocycle rho b D)
    {S : Set G} (hS : IsNormBoundedOn b S) (a : G) :
    IsNormBoundedOn b {x | ∃ h ∈ S, x = a * h * a⁻¹} := by
  obtain ⟨C, hC, hbound⟩ := hS
  refine ⟨‖b a‖ + C + ‖b a⁻¹‖ + 2 * D, ?_, ?_⟩
  · exact add_nonneg
      (add_nonneg (add_nonneg (norm_nonneg _) hC) (norm_nonneg _))
      (mul_nonneg (by norm_num) hb.1)
  intro x hx
  obtain ⟨h, hh, rfl⟩ := hx
  calc
    ‖b (a * h * a⁻¹)‖ ≤ ‖b (a * h)‖ + ‖b a⁻¹‖ + D :=
      hb.norm_mul_le (a * h) a⁻¹
    _ ≤ (‖b a‖ + ‖b h‖ + D) + ‖b a⁻¹‖ + D := by
      gcongr
      exact hb.norm_mul_le a h
    _ ≤ ‖b a‖ + C + ‖b a⁻¹‖ + 2 * D := by
      have := hbound h hh
      linarith

/-- If two group elements commute, the action of one on the quasi-cocycle
value of the other is controlled solely by the first value and the defect. -/
theorem norm_action_sub_of_commute_le (hb : IsQuasiCocycle rho b D)
    {s r : G} (hsr : Commute s r) :
    ‖rho s (b r) - b r‖ ≤ 2 * ‖b s‖ + 2 * D := by
  let e₁ : E := b (s * r) - b s - rho s (b r)
  let e₂ : E := b (r * s) - b r - rho r (b s)
  have he₁ : ‖e₁‖ ≤ D := hb.2 s r
  have he₂ : ‖e₂‖ ≤ D := hb.2 r s
  have hid : rho s (b r) - b r =
      (e₂ - e₁) + (rho r (b s) - b s) := by
    dsimp [e₁, e₂]
    rw [hsr.eq]
    abel
  rw [hid]
  calc
    ‖(e₂ - e₁) + (rho r (b s) - b s)‖ ≤
        ‖e₂ - e₁‖ + ‖rho r (b s) - b s‖ := norm_add_le _ _
    _ ≤ (‖e₂‖ + ‖e₁‖) + (‖rho r (b s)‖ + ‖b s‖) := by
      gcongr
      · exact norm_sub_le e₂ e₁
      · exact norm_sub_le (rho r (b s)) (b s)
    _ ≤ (D + D) + (‖b s‖ + ‖b s‖) := by
      rw [(rho r).norm_map]
      gcongr
    _ = 2 * ‖b s‖ + 2 * D := by ring

end IsQuasiCocycle

namespace IsKazhdanPairComplex

variable {Q : Finset G} {ε : ℝ}

/-- Homogeneous Kazhdan displacement in a complex unitary representation. -/
theorem exists_moved_mul_norm_of_noInvariant
    (hQ : IsKazhdanPairComplex.{u, v} G Q ε)
    [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℂ] E))
    (hno : HasNoInvariantVectorsComplex G rho) (x : E) (hx : x ≠ 0) :
    ∃ q ∈ Q, ε * ‖x‖ ≤ ‖rho q x - x‖ := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : E := (‖x‖⁻¹ : ℂ) • x
  have hz : ‖z‖ = 1 := by
    rw [show ‖z‖ = ‖(‖x‖⁻¹ : ℂ)‖ * ‖x‖ by simp [z, norm_smul]]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hnorm.ne']
  have hmoved : ∃ q ∈ Q, ε ≤ ‖rho q z - z‖ := by
    by_contra h
    have hnear : ∀ q ∈ Q, ‖rho q z - z‖ < ε := by
      intro q hq
      exact lt_of_not_ge (fun hge ↦ h ⟨q, hq, hge⟩)
    obtain ⟨y, hy0, hy⟩ := hQ.2 E rho z hz hnear
    exact hy0 (hno y hy)
  obtain ⟨q, hq, hmove⟩ := hmoved
  refine ⟨q, hq, ?_⟩
  have hnormalized : ‖rho q z - z‖ = ‖rho q x - x‖ / ‖x‖ := by
    rw [show rho q z - z = (‖x‖⁻¹ : ℂ) • (rho q x - x) by
      simp [z, smul_sub]]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x)]
    rw [div_eq_mul_inv, mul_comm]
  rw [hnormalized] at hmove
  exact (le_div_iff₀ hnorm).mp hmove

end IsKazhdanPairComplex

/-- The symmetric set generated by `S`, written without pointwise-set
notation so membership is easy to use in word inductions. -/
def symmetrized (S : Set G) : Set G := {g | g ∈ S ∨ g⁻¹ ∈ S}

@[simp] theorem mem_symmetrized {S : Set G} {g : G} :
    g ∈ symmetrized S ↔ g ∈ S ∨ g⁻¹ ∈ S := Iff.rfl

/-- Membership in the subgroup generated by `S` supplies a finite word in
`S ∪ S⁻¹`. -/
theorem exists_list_of_mem_closure {S : Set G} {g : G}
    (hg : g ∈ Subgroup.closure S) :
    ∃ l : List G, (∀ x ∈ l, x ∈ symmetrized S) ∧ l.prod = g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[x], by simpa [symmetrized] using Or.inl hx, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
      obtain ⟨lx, hlx, hpx⟩ := hx
      obtain ⟨ly, hly, hpy⟩ := hy
      refine ⟨lx ++ ly, ?_, ?_⟩
      · intro z hz
        rw [List.mem_append] at hz
        exact hz.elim (hlx z) (hly z)
      · rw [List.prod_append, hpx, hpy]
  | inv x _ hx =>
      obtain ⟨l, hl, hp⟩ := hx
      refine ⟨l.reverse.map Inv.inv, ?_, ?_⟩
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        have hys : y ∈ symmetrized S := hl y (by simpa using hy)
        rcases hys with hys | hys
        · exact Or.inr (by simpa using hys)
        · exact Or.inl hys
      · rw [List.map_reverse, ← List.prod_inv_reverse, hp]

/-- Displacement by a product is at most the sum of the displacements by
its letters. -/
theorem norm_unitary_prod_sub_le
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (v : E) (l : List G) {A : ℝ}
    (hl : ∀ g ∈ l, ‖rho g v - v‖ ≤ A) :
    ‖rho l.prod v - v‖ ≤ (l.length : ℝ) * A := by
  induction l with
  | nil => simp
  | cons g l ih =>
      have hg := hl g (by simp)
      have htail : ∀ h ∈ l, ‖rho h v - v‖ ≤ A := by
        intro h hh
        exact hl h (by simp [hh])
      rw [List.prod_cons, map_mul]
      calc
        ‖(rho g) ((rho l.prod) v) - v‖ =
            ‖(rho g) ((rho l.prod) v - v) + ((rho g) v - v)‖ := by
              congr 1
              simp [map_sub]
        _ ≤ ‖(rho g) ((rho l.prod) v - v)‖ + ‖(rho g) v - v‖ :=
          norm_add_le _ _
        _ = ‖(rho l.prod) v - v‖ + ‖(rho g v - v)‖ := by
          rw [(rho g).norm_map]
        _ ≤ (l.length : ℝ) * A + A := add_le_add (ih htail) hg
        _ = ((g :: l).length : ℝ) * A := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- A unitary moves a vector by the same amount as its inverse. -/
theorem norm_unitary_inv_sub (rho : G →* (E ≃ₗᵢ[ℂ] E)) (g : G) (v : E) :
    ‖rho g⁻¹ v - v‖ = ‖rho g v - v‖ := by
  calc
    ‖rho g⁻¹ v - v‖ = ‖rho g (rho g⁻¹ v - v)‖ :=
      ((rho g).norm_map _).symm
    _ = ‖v - rho g v‖ := by simp [map_sub]
    _ = ‖rho g v - v‖ := norm_sub_rev _ _

/-- Mimura's elementary displacement estimate: if `H` normalizes `S` and a
quasi-cocycle is bounded on `S`, then every `b(h)` is uniformly almost
`S`-invariant.  This is proved here directly from the two quasi-cocycle
inequalities. -/
theorem quasiCocycle_displacement_le_of_normalizes
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D C : ℝ}
    (hb : IsQuasiCocycle rho b D) {S : Set G} {h q : G}
    (hq : q ∈ S) (hnorm : h⁻¹ * q * h ∈ S)
    (hbound : ∀ s ∈ S, ‖b s‖ ≤ C) :
    ‖rho q (b h) - b h‖ ≤ 2 * C + 2 * D := by
  let r := h⁻¹ * q * h
  have hqr : q * h = h * r := by
    dsimp [r]
    group
  have heq : rho q (b h) - b h =
      -(b (q * h) - b q - rho q (b h)) +
        (b (h * r) - b h - rho h (b r)) + rho h (b r) - b q := by
    rw [hqr]
    abel
  rw [heq]
  calc
    ‖-(b (q * h) - b q - rho q (b h)) +
          (b (h * r) - b h - rho h (b r)) + rho h (b r) - b q‖ ≤
        ‖b (q * h) - b q - rho q (b h)‖ +
          ‖b (h * r) - b h - rho h (b r)‖ + ‖rho h (b r)‖ + ‖b q‖ := by
      calc
        _ ≤ ‖-(b (q * h) - b q - rho q (b h)) +
              (b (h * r) - b h - rho h (b r)) + rho h (b r)‖ + ‖b q‖ :=
          norm_sub_le _ _
        _ ≤ (‖-(b (q * h) - b q - rho q (b h)) +
              (b (h * r) - b h - rho h (b r))‖ + ‖rho h (b r)‖) +
              ‖b q‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ((‖b (q * h) - b q - rho q (b h)‖ +
              ‖b (h * r) - b h - rho h (b r)‖) + ‖rho h (b r)‖) +
              ‖b q‖ := by
          apply add_le_add
          · apply add_le_add
            · simpa only [norm_neg] using norm_add_le
                (-(b (q * h) - b q - rho q (b h)))
                (b (h * r) - b h - rho h (b r))
            · exact le_rfl
          · exact le_rfl
    _ ≤ D + D + C + C := by
      rw [(rho h).norm_map]
      exact add_le_add
        (add_le_add (add_le_add (hb.2 q h) (hb.2 h r))
          (hbound r hnorm))
        (hbound q hq)
    _ = 2 * C + 2 * D := by ring

/-- Every member of `G` is a product of at most `N` elements of `S`. -/
def IsBoundedProduct (G : Type u) [Group G] (S : Set G) (N : ℕ) : Prop :=
  ∀ g : G, ∃ l : List G, l.length ≤ N ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = g

omit [Group G] [InnerProductSpace ℂ E] in
theorem IsNormBoundedOn.mono {b : G → E} {S T : Set G}
    (h : IsNormBoundedOn b T) (hST : S ⊆ T) : IsNormBoundedOn b S := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun g hg ↦ hb g (hST hg)⟩

omit [Group G] [InnerProductSpace ℂ E] in
/-- A set covered by finitely many bounded sets is bounded. -/
theorem isNormBoundedOn_of_finite_cover {b : G → E}
    {I : Type*} (F : Finset I) (S : Set G) (T : I → Set G)
    (hcover : ∀ x ∈ S, ∃ i ∈ F, x ∈ T i)
    (hT : ∀ i ∈ F, IsNormBoundedOn b (T i)) :
    IsNormBoundedOn b S := by
  classical
  have hex : ∀ i : I, ∃ C : ℝ, 0 ≤ C ∧
      (i ∈ F → ∀ x ∈ T i, ‖b x‖ ≤ C) := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨C, hC, hb⟩ := hT i hi
      exact ⟨C, hC, fun _ ↦ hb⟩
    · exact ⟨0, le_rfl, fun h ↦ (hi h).elim⟩
  choose C hC hbound using hex
  let M : ℝ := ∑ i ∈ F, C i
  refine ⟨M, Finset.sum_nonneg fun i _ ↦ hC i, ?_⟩
  intro x hx
  obtain ⟨i, hiF, hxi⟩ := hcover x hx
  exact (hbound i hiF x hxi).trans
    (Finset.single_le_sum (fun j _ ↦ hC j) hiF)

/-- Boundedness on `S` and bounded product width imply global boundedness. -/
theorem isNormBoundedOn_univ_of_boundedProduct
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D) {S : Set G} {N : ℕ}
    (hS : IsNormBoundedOn b S) (hprod : IsBoundedProduct G S N) :
    IsNormBoundedOn b Set.univ := by
  obtain ⟨C, hC, hbound⟩ := hS
  refine ⟨(N : ℝ) * C + (N + 1 : ℕ) * D, ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hC)
      (mul_nonneg (Nat.cast_nonneg _) hb.1)
  intro g _
  obtain ⟨l, hlen, hl, rfl⟩ := hprod g
  have hlist := hb.norm_list_prod_le l fun x hx ↦ hbound x (hl x hx)
  calc
    ‖b l.prod‖ ≤ (l.length : ℝ) * C + (l.length + 1 : ℕ) * D := hlist
    _ ≤ (N : ℝ) * C + (N + 1 : ℕ) * D := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hC
      · exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.add_le_add_right hlen 1) hb.1

/-- **Finite-conjugate globalization.**  Relative `(TT)/T` for `H`
becomes global `(TT)/T` when the group is a bounded product of a set covered
by finitely many fixed conjugates of `H`. -/
theorem hasTTmodT_of_relative_of_bounded_conjugates
    (H : Subgroup G) (hrel : HasRelativeTTmodT.{u, v} G H)
    (Q : Finset G) (S : Set G) (N : ℕ)
    (hcover : ∀ x ∈ S, ∃ a ∈ Q, ∃ h : G, h ∈ H ∧ x = a * h * a⁻¹)
    (hprod : IsBoundedProduct G S N) : HasTTmodT.{u, v} G := by
  intro E _ _ _ rho hno b D hb
  have hH : IsNormBoundedOn b (H : Set G) := hrel E rho hno b D hb
  have hconj : ∀ a ∈ Q,
      IsNormBoundedOn b {x | ∃ h ∈ (H : Set G), x = a * h * a⁻¹} := by
    intro a _
    exact hb.boundedOn_conjugate hH a
  have hS : IsNormBoundedOn b S := isNormBoundedOn_of_finite_cover Q S
    (fun a ↦ {x | ∃ h ∈ (H : Set G), x = a * h * a⁻¹})
    (by
      intro x hx
      obtain ⟨a, ha, h, hh, rfl⟩ := hcover x hx
      exact ⟨a, ha, h, hh, rfl⟩)
    hconj
  exact isNormBoundedOn_univ_of_boundedProduct hb hS hprod

end GroupApproximation
