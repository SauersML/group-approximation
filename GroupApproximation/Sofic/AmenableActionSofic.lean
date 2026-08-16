import GroupApproximation.Sofic.SoficAction
import GroupApproximation.Sofic.NearActionFolner
import GroupApproximation.Matching.Localization
import GroupApproximation.Algebra.Amenable

/-!
# Lemma 30.6: every action of an amenable group is sofic

An amenable group has finite sets almost invariant under any prescribed finite
set of translations.  Such a set is already a model for *every* action of the
group: translations act on it by completed partial bijections, the almost
invariant part is the good set, and the charts `π_a(y) = a⁻¹ • y` map the
tested window injectively into the finite set `{a⁻¹ • y : a ∈ A, y ∈ E}`.
Nothing about the acted-on set is used beyond finiteness of the window, which
is why amenability alone forces soficity of all of a group's actions.

The Følner sets come from the repository's Tarski--Hall theorem applied to the
left-translation permutations of the group itself; the completion of a partial
bijection to a permutation is `Localization.exists_completion`.

The acting group and the acted-on set are placed in the same universe because
`SoficActionModel` builds its model set in the universe of the acted-on set,
while the model here is a subset of the group.
-/

namespace GroupApproximation

namespace AmenableActionSofic

open Amenability

universe u

variable {Q : Type u} [Group Q]

/-! ## Følner sets from an invariant mean -/

/-- An invariant mean is a finitely additive probability on the full power
set. -/
def meanMeasure (m : InvariantMean Q) : FullFinitelyAdditiveProbability Q where
  measure := m.measure
  empty := by
    have h := m.additive ∅ ∅ (by simp)
    rw [Set.union_self] at h
    linarith
  univ := m.measure_univ
  nonnegative := m.nonneg
  union_of_disjoint := m.additive

theorem preservesFullMeasure_mulLeft (m : InvariantMean Q) (q : Q) :
    PreservesFullMeasure (meanMeasure m) (Equiv.mulLeft q) := by
  intro A
  show m.measure ((Equiv.mulLeft q) '' A) = m.measure A
  exact m.invariant q A

/-- The points of `A` that leave `A` under left translation by `q`. -/
noncomputable def boundary (A : Finset Q) (q : Q) : Finset Q :=
  haveI := Classical.decEq Q
  A.filter fun a => q * a ∉ A

theorem mem_boundary {A : Finset Q} {q a : Q} :
    a ∈ boundary A q ↔ a ∈ A ∧ q * a ∉ A := by
  classical
  simp [boundary]

theorem card_boundary_eq_escape (A : Finset Q) (q : Q) :
    (boundary A q).card = (TarskiHall.escape (Equiv.mulLeft q) A).card := by
  classical
  have himg : TarskiHall.escape (Equiv.mulLeft q) A
      = (boundary A q).image fun a => q * a := by
    ext b
    simp only [TarskiHall.escape, Finset.mem_sdiff, Finset.mem_image,
      mem_boundary, Equiv.coe_mulLeft]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hb⟩
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hb⟩
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective q)]

/-- **Følner sets.**  An amenable group has a nonempty finite set whose
boundary under any prescribed finite family of left translations is
arbitrarily small. -/
theorem exists_folner (hQ : IsAmenable Q) (T : Finset Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Finset Q, A.Nonempty ∧ ∀ q ∈ T,
      ((boundary A q).card : ℝ) < δ * A.card := by
  classical
  obtain ⟨m⟩ := hQ
  obtain ⟨A, hAne, -, hsmall⟩ :=
    TarskiHall.exists_finite_small_boundary_avoiding_null (meanMeasure m)
      (T.image fun q => Equiv.mulLeft q)
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact preservesFullMeasure_mulLeft m q)
      (N := (∅ : Set Q)) (by simp) hδ
  refine ⟨A, hAne, fun q hq => ?_⟩
  rw [card_boundary_eq_escape]
  exact hsmall _ (Finset.mem_image_of_mem _ hq)

/-! ## Completed translations of a Følner set -/

/-- A completion of left translation by `q`, restricted to `A`, to a
permutation of `A`. -/
noncomputable def folnerPerm (A : Finset Q) (q : Q) : Equiv.Perm ↥A :=
  Classical.choose (Localization.exists_completion A (Equiv.mulLeft q))

theorem folnerPerm_agrees (A : Finset Q) (q : Q) (a : ↥A)
    (ha : q * (a : Q) ∈ A) : ((folnerPerm A q a : ↥A) : Q) = q * (a : Q) := by
  have h := Classical.choose_spec
    (Localization.exists_completion A (Equiv.mulLeft q)) a (by simpa using ha)
  simpa [folnerPerm] using h

/-! ## The model -/

variable {G : Type u} [Group G] {Y : Type u} [MulAction G Y]

/-- **Lemma 30.6, in the form the co-amenable case needs.**  If an action of
`G` factors through a surjection onto an amenable group -- that is, elements
with the same image act identically -- then the action is sofic.

The model set is a Følner set of the amenable quotient, translations act by the
completed partial bijections, and the charts use any set-theoretic section of
the surjection: the choice is immaterial precisely because elements with equal
image act identically. -/
theorem isSoficAction_of_amenable_surjHom {Q : Type u} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (hQ : IsAmenable Q)
    (hcompat : ∀ g₁ g₂ : G, f g₁ = f g₂ → ∀ y : Y, g₁ • y = g₂ • y) :
    IsSoficAction G Y := by
  classical
  intro F E ε hε
  set lift : Q → G := Function.surjInv hf with hlift
  have hliftf : ∀ q : Q, f (lift q) = q := fun q => Function.surjInv_eq hf q
  -- the translations that must be tested, in the amenable quotient
  set Fq : Finset Q := F.image f with hFq
  set T : Finset Q := Fq ∪ (Fq ×ˢ Fq).image (fun p => p.1 * p.2) with hT
  have hFT : ∀ g ∈ F, f g ∈ T :=
    fun g hg => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)
  have hFFT : ∀ g ∈ F, ∀ h ∈ F, f g * f h ∈ T := by
    intro g hg h hh
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(f g, f h), ?_, rfl⟩)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hg, Finset.mem_image_of_mem _ hh⟩
  set δ : ℝ := ε / (T.card + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨A, hAne, hsmall⟩ := exists_folner hQ T hδ
  have hcardA : 0 < A.card := Finset.card_pos.mpr hAne
  have hcardAR : (0 : ℝ) < A.card := by exact_mod_cast hcardA
  have hcardCoe : Fintype.card ↥A = A.card := Fintype.card_coe A
  -- the almost-invariant part of the Følner set
  set S : Finset Q := A.filter (fun a => ∀ q ∈ T, q * a ∈ A) with hS
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hmemS : ∀ a : Q, a ∈ S ↔ a ∈ A ∧ ∀ q ∈ T, q * a ∈ A := by
    intro a; simp [hS]
  have hsdiff : A \ S ⊆ T.biUnion (boundary A) := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    obtain ⟨haA, haS⟩ := ha
    have hnot : ¬ ∀ q ∈ T, q * a ∈ A :=
      fun hcon => haS ((hmemS a).mpr ⟨haA, hcon⟩)
    push Not at hnot
    obtain ⟨q, hq, hqa⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨q, hq, mem_boundary.mpr ⟨haA, hqa⟩⟩
  have hdefect : ((A \ S).card : ℝ) ≤ ε * A.card := by
    have hsum : (A \ S).card ≤ ∑ q ∈ T, (boundary A q).card :=
      le_trans (Finset.card_le_card hsdiff) Finset.card_biUnion_le
    have hsumR : ∑ q ∈ T, ((boundary A q).card : ℝ) ≤ T.card * (δ * A.card) := by
      calc ∑ q ∈ T, ((boundary A q).card : ℝ)
          ≤ ∑ _q ∈ T, δ * A.card :=
            Finset.sum_le_sum fun q hq => (hsmall q hq).le
        _ = T.card * (δ * A.card) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hchain : ((A \ S).card : ℝ) ≤ T.card * (δ * A.card) := by
      refine le_trans ?_ hsumR
      exact_mod_cast hsum
    refine hchain.trans ?_
    have hfrac : (T.card : ℝ) / (T.card + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) T.card]
    calc (T.card : ℝ) * (δ * A.card)
        = ((T.card : ℝ) / (T.card + 1)) * (ε * A.card) := by
          rw [hδdef]; ring
      _ ≤ 1 * (ε * A.card) := by
          apply mul_le_mul_of_nonneg_right hfrac
          positivity
      _ = ε * A.card := one_mul _
  have hScard : (1 - ε) * (A.card : ℝ) ≤ S.card := by
    have hcards : (A \ S).card = A.card - S.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSA]
    have hle : S.card ≤ A.card := Finset.card_le_card hSA
    have hR : ((A \ S).card : ℝ) = (A.card : ℝ) - S.card := by
      rw [hcards]; exact Nat.cast_sub hle
    rw [hR] at hdefect
    linarith
  -- the good model points
  set good : Finset ↥A := S.subtype (· ∈ A) with hgood
  have hgoodcard : good.card = S.card := by
    rw [hgood, Finset.card_subtype, Finset.filter_true_of_mem fun a ha => hSA ha]
  have hmem_good : ∀ a : ↥A, a ∈ good ↔ ∀ q ∈ T, q * (a : Q) ∈ A := by
    intro a
    rw [hgood, Finset.mem_subtype, hmemS]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  -- the chart target
  set B : Finset Y := (A ×ˢ E).image (fun p => (lift p.1)⁻¹ • p.2) with hB
  have hmemB : ∀ a ∈ A, ∀ y ∈ E, (lift a)⁻¹ • y ∈ B := by
    intro a ha y hy
    exact Finset.mem_image.mpr ⟨(a, y), Finset.mem_product.mpr ⟨ha, hy⟩, rfl⟩
  have hact_apply : ∀ (q : Q) (a : ↥A), q * (a : Q) ∈ A →
      ((folnerPerm A q a : ↥A) : Q) = q * (a : Q) := folnerPerm_agrees A
  refine ⟨{
    Site := ↥A
    siteFintype := inferInstance
    siteDecEq := inferInstance
    siteNonempty := by rw [hcardCoe]; exact hcardA
    act := fun g => folnerPerm A (f g)
    act_one := ?_
    act_mul := ?_
    good := good
    good_card := ?_
    Chart := Option ↥B
    chartFintype := inferInstance
    chart := fun s y => if h : (lift (s : Q))⁻¹ • y ∈ B then some ⟨_, h⟩ else none
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · -- the identity is modelled exactly
    refine Equiv.ext fun a => ?_
    have hmem : f 1 * (a : Q) ∈ A := by simp
    have h1 := hact_apply (f 1) a hmem
    refine Subtype.ext ?_
    rw [h1, map_one, one_mul]
    rfl
  · -- multiplicativity is exact on the good set
    intro g hg h hh
    have hsubset :
        (Finset.univ.filter fun a : ↥A =>
          folnerPerm A (f (g * h)) a
            ≠ (folnerPerm A (f g) * folnerPerm A (f h)) a)
          ⊆ Finset.univ \ good := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hgood' => ha ?_⟩
      have hall := (hmem_good a).mp hgood'
      have hha : f h * (a : Q) ∈ A := hall (f h) (hFT h hh)
      have hgha : (f g * f h) * (a : Q) ∈ A := hall _ (hFFT g hg h hh)
      have h1 : ((folnerPerm A (f (g * h)) a : ↥A) : Q) = (f g * f h) * (a : Q) := by
        rw [map_mul]
        exact hact_apply _ a hgha
      have h2 : ((folnerPerm A (f h) a : ↥A) : Q) = f h * (a : Q) :=
        hact_apply _ a hha
      have hg2 : f g * ((folnerPerm A (f h) a : ↥A) : Q) ∈ A := by
        rw [h2, ← mul_assoc]; exact hgha
      have h3 : ((folnerPerm A (f g) (folnerPerm A (f h) a) : ↥A) : Q)
          = f g * ((folnerPerm A (f h) a : ↥A) : Q) := hact_apply _ _ hg2
      refine Subtype.ext ?_
      rw [Equiv.Perm.mul_apply, h1, h3, h2, ← mul_assoc]
    have hcompl : ((Finset.univ \ good).card : ℝ) ≤ ε * A.card := by
      have hsdiffcard : (Finset.univ \ good).card
          = Fintype.card ↥A - good.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      have hle : good.card ≤ Fintype.card ↥A :=
        Finset.card_le_card (Finset.subset_univ _)
      have hR : ((Finset.univ \ good).card : ℝ)
          = (Fintype.card ↥A : ℝ) - good.card := by
        rw [hsdiffcard]; exact Nat.cast_sub hle
      rw [hR, hcardCoe, hgoodcard]
      linarith
    have hcard : ((Finset.univ.filter fun a : ↥A =>
        folnerPerm A (f (g * h)) a
          ≠ (folnerPerm A (f g) * folnerPerm A (f h)) a).card : ℝ)
        ≤ ε * A.card :=
      le_trans (by exact_mod_cast Finset.card_le_card hsubset) hcompl
    rw [permDist, div_le_iff₀ (by rw [hcardCoe]; exact hcardAR), hcardCoe]
    exact hcard
  · -- the good set is large
    rw [hcardCoe, hgoodcard]
    exact hScard
  · -- charts are injective on the window
    intro s hs x hx y hy hxy
    have hxB : (lift (s : Q))⁻¹ • x ∈ B := hmemB _ s.2 _ hx
    have hyB : (lift (s : Q))⁻¹ • y ∈ B := hmemB _ s.2 _ hy
    rw [dif_pos hxB, dif_pos hyB, Option.some.injEq, Subtype.mk.injEq] at hxy
    exact MulAction.injective (lift (s : Q))⁻¹ hxy
  · -- the orbit-chart identity
    intro g hg s hs hgs x hx hgx
    have hall := (hmem_good s).mp hs
    have hgsA : f g * (s : Q) ∈ A := hall (f g) (hFT g hg)
    have hactgs : ((folnerPerm A (f g) s : ↥A) : Q) = f g * (s : Q) :=
      hact_apply _ _ hgsA
    -- the two chart values agree because their translations have equal image
    have hfeq : f (lift (f g * (s : Q)))⁻¹ = f (g * lift (s : Q))⁻¹ := by
      rw [map_inv, map_inv, hliftf, map_mul, hliftf]
    have hsmulEq : (lift (f g * (s : Q)))⁻¹ • x = (lift (s : Q))⁻¹ • (g⁻¹ • x) := by
      have := hcompat (lift (f g * (s : Q)))⁻¹ (g * lift (s : Q))⁻¹ hfeq x
      rw [this, mul_inv_rev, mul_smul]
    have hmem1 : (lift ((folnerPerm A (f g) s : ↥A) : Q))⁻¹ • x ∈ B := by
      rw [hactgs]
      exact hmemB _ hgsA _ hx
    have hmem2 : (lift (s : Q))⁻¹ • (g⁻¹ • x) ∈ B := hmemB _ s.2 _ hgx
    have hval : (lift ((folnerPerm A (f g) s : ↥A) : Q))⁻¹ • x
        = (lift (s : Q))⁻¹ • (g⁻¹ • x) := by
      rw [hactgs]
      exact hsmulEq
    rw [dif_pos hmem1, dif_pos hmem2]
    simp only [Option.some.injEq, Subtype.mk.injEq]
    exact hval

/-- **Lemma 30.6.**  Every action of an amenable group on any set is sofic. -/
theorem isSoficAction_of_isAmenable {Q : Type u} [Group Q] {Y : Type u}
    [MulAction Q Y] (hQ : IsAmenable Q) : IsSoficAction Q Y :=
  isSoficAction_of_amenable_surjHom (MonoidHom.id Q) Function.surjective_id hQ
    (fun g₁ g₂ h y => by rw [show g₁ = g₂ from h])

end AmenableActionSofic

end GroupApproximation
