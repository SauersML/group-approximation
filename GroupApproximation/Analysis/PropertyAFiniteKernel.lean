import GroupApproximation.Analysis.PropertyALocality

/-!
# Property A lifts along a surjection with finite kernel

The exactness paragraph's fourth step is

> Since `⟨ζ⟩` is finite, extension permanence \cite{KWPermanence} then gives
> exactness of `C(𝒢)`.

Extension permanence for property A is in general a substantial theorem.  The
case the sentence actually uses is not: the kernel is **finite**, and then the
lift is a two-line construction once the right one is chosen.

## The construction, and the choice that makes it work

Fix a set-theoretic section `sec` of `π`, and put

`weight g x = W.weight (π g) (π x)` when `x = sec (π x)`, and `0` otherwise.

The point is that the chosen lift depends on `x` alone and **not** on the base
point `g`.  The obvious alternative -- put the mass at `g · sec ((π g)⁻¹ π x)`,
the lift chosen relative to `g` -- also has the right mass and support, but it
fails the closeness clause outright: the measures at two different base points
would then live on two disjoint sets and their `ℓ¹` distance would be `2`, not
small.  With a base-point-independent section both measures live on `sec '' G'`,
where they are literally the pushforwards of the quotient's measures, so the
`ℓ¹` estimate is the quotient's own.

Finiteness of the kernel enters in exactly one place: the support clause.  The
displacement `g⁻¹x` of a charged point lies in `π⁻¹(t)` for some `t` in the
quotient's template, and `π⁻¹(t)` is a coset of the kernel, so the union of them
over the template is finite.  That is the whole use of `Finite π.ker`, and no
counting of fibres is needed anywhere -- which is what keeps the argument short.

## Statement

`hasPropertyA_of_finite_ker` -- if `π : G →* G'` is surjective with finite
kernel and `G'` has property A, then so does `G`.

Unconditional; the finiteness of the kernel is the hypothesis the printed
sentence itself supplies.
-/

namespace GroupApproximation
namespace PropertyAFiniteKernel

open ExactnessPermanence

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/-! ## A section of the projection -/

/-- A set-theoretic section of a surjection. -/
noncomputable def sec (π : G →* G') (hsurj : Function.Surjective π) : G' → G :=
  Function.surjInv hsurj

theorem pi_sec (π : G →* G') (hsurj : Function.Surjective π) (y : G') :
    π (sec π hsurj y) = y :=
  Function.surjInv_eq hsurj y

theorem sec_injective (π : G →* G') (hsurj : Function.Surjective π) :
    Function.Injective (sec π hsurj) := by
  intro y₁ y₂ hy
  rw [← pi_sec π hsurj y₁, ← pi_sec π hsurj y₂, hy]

/-! ## The lifted weight system -/

variable {R' : Finset G'} {ε : ℝ}

/-- The quotient's measure system, pulled back and supported on the section. -/
noncomputable def liftWeight (π : G →* G') (hsurj : Function.Surjective π)
    (W : PropertyAWitness G' R' ε) (g x : G) : ℝ :=
  @ite ℝ (x = sec π hsurj (π x)) (Classical.dec _) (W.weight (π g) (π x)) 0

theorem liftWeight_of_eq {π : G →* G'} {hsurj : Function.Surjective π}
    (W : PropertyAWitness G' R' ε) {g x : G} (hx : x = sec π hsurj (π x)) :
    liftWeight π hsurj W g x = W.weight (π g) (π x) := by
  unfold liftWeight
  rw [if_pos hx]

theorem liftWeight_of_ne {π : G →* G'} {hsurj : Function.Surjective π}
    (W : PropertyAWitness G' R' ε) {g x : G} (hx : ¬ x = sec π hsurj (π x)) :
    liftWeight π hsurj W g x = 0 := by
  unfold liftWeight
  rw [if_neg hx]

/-- On the section the lifted system *is* the quotient's system. -/
theorem liftWeight_sec (π : G →* G') (hsurj : Function.Surjective π)
    (W : PropertyAWitness G' R' ε) (g : G) (y : G') :
    liftWeight π hsurj W g (sec π hsurj y) = W.weight (π g) y := by
  have hx : sec π hsurj y = sec π hsurj (π (sec π hsurj y)) := by
    rw [pi_sec]
  rw [liftWeight_of_eq W hx, pi_sec]

/-- Everything the lifted system charges sits on the section, at a point the
quotient's system charges. -/
theorem liftWeight_ne_zero {π : G →* G'} {hsurj : Function.Surjective π}
    (W : PropertyAWitness G' R' ε) (g x : G)
    (hne : liftWeight π hsurj W g x ≠ 0) :
    W.weight (π g) (π x) ≠ 0 ∧ x = sec π hsurj (π x) := by
  by_cases hx : x = sec π hsurj (π x)
  · refine ⟨?_, hx⟩
    rw [liftWeight_of_eq W hx] at hne
    exact hne
  · exact absurd (liftWeight_of_ne W hx) hne

theorem liftWeight_nonneg (π : G →* G') (hsurj : Function.Surjective π)
    (W : PropertyAWitness G' R' ε) (g x : G) :
    0 ≤ liftWeight π hsurj W g x := by
  by_cases hx : x = sec π hsurj (π x)
  · rw [liftWeight_of_eq W hx]
    exact W.weight_nonneg _ _
  · exact le_of_eq (liftWeight_of_ne W hx).symm

/-! ## The lift -/

/-- **Property A lifts along a surjection with finite kernel.**  This is the
printed extension-permanence step in the case the printed sentence supplies:
`⟨ζ⟩` is finite. -/
theorem hasPropertyA_of_finite_ker (π : G →* G')
    (hsurj : Function.Surjective π) (hfin : Finite π.ker)
    (h : HasPropertyA G') : HasPropertyA G := by
  classical
  intro R ε hε
  obtain ⟨W⟩ := h (R.image π) ε hε
  -- the kernel, as a finite set of `G`
  obtain ⟨K, hK⟩ : ∃ K : Finset G, ∀ x : G, x ∈ K ↔ π x = 1 := by
    haveI : Finite π.ker := hfin
    haveI : Fintype π.ker := Fintype.ofFinite _
    refine ⟨Finset.image (fun y : π.ker ↦ (y : G)) Finset.univ, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx
      rw [← ha]
      exact MonoidHom.mem_ker.mp a.2
    · intro hx
      exact Finset.mem_image.mpr
        ⟨⟨x, MonoidHom.mem_ker.mpr hx⟩, Finset.mem_univ _, rfl⟩
  refine ⟨{
    template := W.template.biUnion fun t ↦ K.image fun k ↦ sec π hsurj t * k
    weight := liftWeight π hsurj W
    weight_nonneg := liftWeight_nonneg π hsurj W
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · -- support: a charged displacement lies in a kernel coset over the template
    intro g x hx
    by_contra hne
    obtain ⟨hw, hxsec⟩ := liftWeight_ne_zero W g x hne
    have ht : (π g)⁻¹ * π x ∈ W.template := by
      by_contra hcon
      exact hw (W.weight_eq_zero _ _ hcon)
    refine hx (Finset.mem_biUnion.mpr ⟨(π g)⁻¹ * π x, ht, ?_⟩)
    refine Finset.mem_image.mpr
      ⟨(sec π hsurj ((π g)⁻¹ * π x))⁻¹ * (g⁻¹ * x), ?_, ?_⟩
    · rw [hK]
      simp only [map_mul, map_inv, pi_sec]
      group
    · rw [mul_inv_cancel_left]
  · -- total mass
    intro g
    set A : Finset G := W.template.image fun t ↦ g⁻¹ * sec π hsurj (π g * t)
      with hAdef
    have hAsub : A ⊆ W.template.biUnion fun t ↦ K.image fun k ↦
        sec π hsurj t * k := by
      intro s hs
      rw [hAdef] at hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
      refine Finset.mem_image.mpr
        ⟨(sec π hsurj t)⁻¹ * (g⁻¹ * sec π hsurj (π g * t)), ?_, ?_⟩
      · rw [hK]
        simp only [map_mul, map_inv, pi_sec]
        group
      · rw [mul_inv_cancel_left]
    have hvanish : ∀ s ∈ (W.template.biUnion fun t ↦ K.image fun k ↦
        sec π hsurj t * k), s ∉ A → liftWeight π hsurj W g (g * s) = 0 := by
      intro s _ hs
      by_contra hne
      obtain ⟨hw, hxsec⟩ := liftWeight_ne_zero W g (g * s) hne
      have ht : (π g)⁻¹ * π (g * s) ∈ W.template := by
        by_contra hcon
        exact hw (W.weight_eq_zero _ _ hcon)
      refine hs ?_
      rw [hAdef]
      refine Finset.mem_image.mpr ⟨(π g)⁻¹ * π (g * s), ht, ?_⟩
      have hmul : π g * ((π g)⁻¹ * π (g * s)) = π (g * s) := by group
      rw [hmul, ← hxsec]
      group
    have hinj : ∀ a ∈ W.template, ∀ b ∈ W.template,
        g⁻¹ * sec π hsurj (π g * a) = g⁻¹ * sec π hsurj (π g * b) → a = b := by
      intro a _ b _ hab
      exact mul_left_cancel (sec_injective π hsurj (mul_left_cancel hab))
    rw [← Finset.sum_subset hAsub hvanish, hAdef, Finset.sum_image hinj,
      ← W.weight_sum (π g)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hx : g * (g⁻¹ * sec π hsurj (π g * t)) = sec π hsurj (π g * t) := by
      group
    rw [hx, liftWeight_sec]
  · -- closeness: both measures live on the section, where they are the
    -- quotient's own measures
    intro g h hgh T hTg hTh
    have hmem : (π g)⁻¹ * π h ∈ R.image π := by
      refine Finset.mem_image.mpr ⟨g⁻¹ * h, hgh, ?_⟩
      rw [map_mul, map_inv]
    obtain ⟨T', hT'g, hT'h⟩ := W.exists_window (π g) (π h)
    have hclose := W.weight_close (π g) (π h) hmem T' hT'g hT'h
    have hSg : ∀ x, liftWeight π hsurj W g x ≠ 0 →
        x ∈ T'.image (sec π hsurj) := by
      intro x hx
      obtain ⟨hw, hxsec⟩ := liftWeight_ne_zero W g x hx
      exact Finset.mem_image.mpr ⟨π x, hT'g _ hw, hxsec.symm⟩
    have hSh : ∀ x, liftWeight π hsurj W h x ≠ 0 →
        x ∈ T'.image (sec π hsurj) := by
      intro x hx
      obtain ⟨hw, hxsec⟩ := liftWeight_ne_zero W h x hx
      exact Finset.mem_image.mpr ⟨π x, hT'h _ hw, hxsec.symm⟩
    have hzeroS : ∀ x : G, x ∉ T'.image (sec π hsurj) →
        |liftWeight π hsurj W g x - liftWeight π hsurj W h x| = 0 := by
      intro x hx
      have h1 : liftWeight π hsurj W g x = 0 := by
        by_contra hc
        exact hx (hSg x hc)
      have h2 : liftWeight π hsurj W h x = 0 := by
        by_contra hc
        exact hx (hSh x hc)
      rw [h1, h2, sub_self, abs_zero]
    have hzeroT : ∀ x : G, x ∉ T →
        |liftWeight π hsurj W g x - liftWeight π hsurj W h x| = 0 := by
      intro x hx
      have h1 : liftWeight π hsurj W g x = 0 := by
        by_contra hc
        exact hx (hTg x hc)
      have h2 : liftWeight π hsurj W h x = 0 := by
        by_contra hc
        exact hx (hTh x hc)
      rw [h1, h2, sub_self, abs_zero]
    have hTsum : ∑ x ∈ T ∩ T'.image (sec π hsurj),
          |liftWeight π hsurj W g x - liftWeight π hsurj W h x|
        = ∑ x ∈ T, |liftWeight π hsurj W g x - liftWeight π hsurj W h x| :=
      Finset.sum_subset Finset.inter_subset_left fun x hxT hx ↦
        hzeroS x fun hmem' ↦ hx (Finset.mem_inter.mpr ⟨hxT, hmem'⟩)
    have hSsum : ∑ x ∈ T ∩ T'.image (sec π hsurj),
          |liftWeight π hsurj W g x - liftWeight π hsurj W h x|
        = ∑ x ∈ T'.image (sec π hsurj),
            |liftWeight π hsurj W g x - liftWeight π hsurj W h x| :=
      Finset.sum_subset Finset.inter_subset_right fun x hx hx' ↦
        hzeroT x fun hmem' ↦ hx' (Finset.mem_inter.mpr ⟨hmem', hx⟩)
    rw [← hTsum, hSsum,
      Finset.sum_image fun a _ b _ hab ↦ sec_injective π hsurj hab]
    calc ∑ y ∈ T', |liftWeight π hsurj W g (sec π hsurj y)
            - liftWeight π hsurj W h (sec π hsurj y)|
        = ∑ y ∈ T', |W.weight (π g) y - W.weight (π h) y| := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [liftWeight_sec, liftWeight_sec]
      _ ≤ ε := hclose

/-- The same statement for a finite normal subgroup, which is the shape the
printed sentence has: `C(𝒢)` modulo the finite central `⟨ζ⟩`. -/
theorem hasPropertyA_of_finite_normal (N : Subgroup G) [N.Normal] (hN : Finite N)
    (h : HasPropertyA (G ⧸ N)) : HasPropertyA G := by
  refine hasPropertyA_of_finite_ker (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) ?_ h
  rw [QuotientGroup.ker_mk']
  exact hN

end PropertyAFiniteKernel
end GroupApproximation
