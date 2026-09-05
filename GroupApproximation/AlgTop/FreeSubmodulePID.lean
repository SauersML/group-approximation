import Mathlib

/-!
# Submodules of free modules over a principal ideal domain are free

Mathlib at the pinned revision proves this only in **finite rank**
(`Submodule.basisOfPid`, which carries a `[Finite ι]` hypothesis, in
`Mathlib/LinearAlgebra/FreeModule/PID.lean`). The singular chain groups of a
topological space are free of uncountable rank, so the finite-rank statement is
useless for algebraic topology: it is exactly what is needed to split

```text
0 → Zₙ(C) → Cₙ → Bₙ₋₁(C) → 0
```

and hence to prove the universal coefficient theorem, which in turn is what
computes `H^*(Sⁿ; ℤ)` and gives the free-case Künneth theorem. This file supplies
the general-rank statement.

## Main results

* `free_of_submodule_finsupp` — a submodule of `ι →₀ R` is free, for `R` a PID
  and `ι` well-ordered.
* `free_of_submodule_of_pid` — a submodule of any free module over a PID is free.

## Method

The classical transfinite argument. Well-order the basis index set `ι`. For each
`i`, the elements of the submodule `N` supported in the initial segment
`{j | j ≤ i}` have `i`-th coefficients forming an ideal `leadIdeal N i` of `R`;
choose a generator `leadGen N i` of it and an element `lead N i ∈ N` realising it.
Then `{lead N i : leadGen N i ≠ 0}` is a basis of `N`:

* **Independence.** In a vanishing finite combination, look at the largest index
  `i₀` with a nonzero coefficient and evaluate at `i₀`. Every `lead N i` with
  `i < i₀` is supported below `i₀`, so only the `i₀` term survives, giving
  `g i₀ · leadGen N i₀ = 0` with `leadGen N i₀ ≠ 0` in a domain.
* **Spanning.** Transfinite induction on the largest index of the support:
  subtract the right multiple of `lead N i` to kill the top coefficient, which
  strictly lowers that index.
-/

namespace GroupApproximation.AlgTop.PID

section FinsuppCase

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
variable (N : Submodule R (ι →₀ R))

/-! ## 1. Initial segments of the submodule -/

/-- The elements of `N` supported in the initial segment `{j | j ≤ i}`. -/
def below (i : ι) : Submodule R (ι →₀ R) :=
  N ⊓ Finsupp.supported R R {j : ι | j ≤ i}

theorem mem_below {i : ι} {x : ι →₀ R} :
    x ∈ below N i ↔ x ∈ N ∧ ∀ j ∈ x.support, j ≤ i := by
  simp only [below, Submodule.mem_inf, Finsupp.mem_supported, Set.subset_def, Finset.mem_coe,
    Set.mem_setOf_eq]

theorem apply_eq_zero_of_mem_below {i : ι} {x : ι →₀ R} (hx : x ∈ below N i) {j : ι}
    (hj : i < j) : x j = 0 := by
  by_contra h
  exact absurd (((mem_below N).mp hx).2 j (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)

/-! ## 2. The leading-coefficient ideal and its chosen generator -/

/-- The ideal of `i`-th coefficients of elements of `N` supported in `{j | j ≤ i}`. -/
def leadIdeal (i : ι) : Ideal R := Submodule.map (Finsupp.lapply i) (below N i)

theorem mem_leadIdeal {i : ι} {c : R} :
    c ∈ leadIdeal N i ↔ ∃ x ∈ below N i, x i = c := by
  simp [leadIdeal, Submodule.mem_map]

theorem exists_leadGen (i : ι) : ∃ a : R, leadIdeal N i = Submodule.span R {a} :=
  (IsPrincipalIdealRing.principal (leadIdeal N i)).principal

/-- A chosen generator of the leading-coefficient ideal at `i`. -/
noncomputable def leadGen (i : ι) : R := (exists_leadGen N i).choose

theorem leadIdeal_eq_span (i : ι) : leadIdeal N i = Submodule.span R {leadGen N i} :=
  (exists_leadGen N i).choose_spec

theorem leadGen_mem (i : ι) : leadGen N i ∈ leadIdeal N i := by
  rw [leadIdeal_eq_span]
  exact Submodule.mem_span_singleton_self _

/-- A chosen element of `N`, supported in `{j | j ≤ i}`, whose `i`-th coefficient is
the leading generator at `i`. -/
noncomputable def lead (i : ι) : ι →₀ R :=
  ((mem_leadIdeal N).mp (leadGen_mem N i)).choose

theorem lead_mem_below (i : ι) : lead N i ∈ below N i :=
  ((mem_leadIdeal N).mp (leadGen_mem N i)).choose_spec.1

theorem lead_apply (i : ι) : (lead N i) i = leadGen N i :=
  ((mem_leadIdeal N).mp (leadGen_mem N i)).choose_spec.2

theorem lead_mem (i : ι) : lead N i ∈ N := ((mem_below N).mp (lead_mem_below N i)).1

theorem lead_apply_of_lt {i j : ι} (h : i < j) : (lead N i) j = 0 :=
  apply_eq_zero_of_mem_below N (lead_mem_below N i) h

/-- The indices that carry a basis vector: those whose leading generator is nonzero. -/
def leadSupport : Set ι := {i : ι | leadGen N i ≠ 0}

/-- The candidate basis family, as elements of the ambient module `ι →₀ R`. -/
noncomputable def leadFam (i : leadSupport N) : ι →₀ R := lead N i.1

/-! ## 3. Linear independence -/

theorem linearIndependent_leadFam : LinearIndependent R (leadFam N) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  set t := s.filter (fun j => g j ≠ 0) with ht
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have htne : t.Nonempty := ⟨i, hit⟩
  set j0 := t.max' htne with hj0
  have hj0t : j0 ∈ t := t.max'_mem htne
  have hj0s : j0 ∈ s := (Finset.mem_filter.mp hj0t).1
  have hgj0 : g j0 ≠ 0 := (Finset.mem_filter.mp hj0t).2
  have heval : (∑ j ∈ s, g j • leadFam N j) (j0 : ι) = 0 := by rw [hg]; simp
  rw [Finsupp.finsetSum_apply] at heval
  have hsplit : ∑ j ∈ s, (g j • leadFam N j) (j0 : ι) = g j0 * leadGen N (j0 : ι) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finsupp.smul_apply, smul_eq_mul, leadFam, lead_apply]
    · intro j hjs hjne
      rcases eq_or_ne (g j) 0 with h0 | h0
      · simp [h0]
      · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, h0⟩
        have hlt : j < j0 := lt_of_le_of_ne (Finset.le_max' t j hjt) hjne
        rw [Finsupp.smul_apply, leadFam,
          lead_apply_of_lt N (Subtype.coe_lt_coe.mpr hlt), smul_zero]
    · intro h; exact absurd hj0s h
  rw [hsplit] at heval
  exact hgj0 ((mul_eq_zero.mp heval).resolve_right j0.2)

/-! ## 4. Spanning -/

theorem mem_span_leadFam_of_mem_below (i : ι) :
    ∀ x ∈ below N i, x ∈ Submodule.span R (Set.range (leadFam N)) := by
  induction i using WellFoundedLT.induction with
  | ind i IH =>
    -- The case where the top coefficient already vanishes: the support drops.
    have key : ∀ z ∈ below N i, z i = 0 →
        z ∈ Submodule.span R (Set.range (leadFam N)) := by
      intro z hz hzi
      by_cases hz0 : z = 0
      · rw [hz0]; exact Submodule.zero_mem _
      · have hsupp : z.support.Nonempty := Finsupp.support_nonempty_iff.mpr hz0
        have hi'mem : z.support.max' hsupp ∈ z.support := z.support.max'_mem hsupp
        have hi'le : z.support.max' hsupp ≤ i := ((mem_below N).mp hz).2 _ hi'mem
        have hi'ne : z.support.max' hsupp ≠ i := by
          intro h
          rw [h] at hi'mem
          exact (Finsupp.mem_support_iff.mp hi'mem) hzi
        refine IH (z.support.max' hsupp) (lt_of_le_of_ne hi'le hi'ne) z ?_
        exact (mem_below N).mpr ⟨((mem_below N).mp hz).1,
          fun j hj => Finset.le_max' _ j hj⟩
    intro x hx
    by_cases hxi : x i = 0
    · exact key x hx hxi
    · have hmem : x i ∈ leadIdeal N i := (mem_leadIdeal N).mpr ⟨x, hx, rfl⟩
      have hgen : leadGen N i ≠ 0 := by
        intro h0
        rw [leadIdeal_eq_span, h0] at hmem
        simp only [Submodule.span_zero_singleton, Submodule.mem_bot] at hmem
        exact hxi hmem
      obtain ⟨c, hc⟩ : ∃ c : R, c • leadGen N i = x i := by
        rw [leadIdeal_eq_span] at hmem
        exact Submodule.mem_span_singleton.mp hmem
      have hybelow : x - c • lead N i ∈ below N i :=
        (below N i).sub_mem hx ((below N i).smul_mem c (lead_mem_below N i))
      have hce : (c • lead N i) i = x i := by
        rw [Finsupp.smul_apply, lead_apply]
        exact hc
      have hyi : (x - c • lead N i) i = 0 := by
        rw [Finsupp.sub_apply, hce, sub_self]
      have hleadspan : lead N i ∈ Submodule.span R (Set.range (leadFam N)) :=
        Submodule.subset_span ⟨⟨i, hgen⟩, rfl⟩
      have hxeq : x = (x - c • lead N i) + c • lead N i := by abel
      rw [hxeq]
      exact Submodule.add_mem _ (key _ hybelow hyi) (Submodule.smul_mem _ c hleadspan)

theorem span_leadFam : Submodule.span R (Set.range (leadFam N)) = N := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact lead_mem N i.1
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    · have hsupp : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hx0
      refine mem_span_leadFam_of_mem_below N (x.support.max' hsupp) x ?_
      exact (mem_below N).mpr ⟨hx, fun j hj => Finset.le_max' _ j hj⟩

/-! ## 5. The basis of the submodule -/

/-- The candidate basis family, as elements of the submodule itself. -/
noncomputable def leadFamN (i : leadSupport N) : N := ⟨lead N i.1, lead_mem N i.1⟩

theorem linearIndependent_leadFamN : LinearIndependent R (leadFamN N) := by
  apply LinearIndependent.of_comp N.subtype
  have h : ⇑(N.subtype) ∘ leadFamN N = leadFam N := by funext i; rfl
  rw [h]
  exact linearIndependent_leadFam N

theorem span_leadFamN : ⊤ ≤ Submodule.span R (Set.range (leadFamN N)) := by
  have hinj : Function.Injective (N.subtype) := fun _ _ h => Subtype.ext h
  have himg : (N.subtype '' Set.range (leadFamN N)) = Set.range (leadFam N) := by
    rw [← Set.range_comp]; rfl
  have hmap : Submodule.map N.subtype (Submodule.span R (Set.range (leadFamN N)))
      = Submodule.map N.subtype (⊤ : Submodule R N) := by
    rw [Submodule.map_span, himg, Submodule.map_subtype_top]
    exact span_leadFam N
  exact le_of_eq (Submodule.map_injective_of_injective hinj hmap).symm

/-- A basis of a submodule of `ι →₀ R`, for `R` a principal ideal domain. -/
noncomputable def basisOfSubmoduleFinsupp : Basis (leadSupport N) R N :=
  Basis.mk (linearIndependent_leadFamN N) (span_leadFamN N)

/-- **A submodule of `ι →₀ R` is free**, for `R` a principal ideal domain. -/
theorem free_of_submodule_finsupp : Module.Free R N :=
  Module.Free.of_basis (basisOfSubmoduleFinsupp N)

end FinsuppCase

/-- **Every submodule of a free module over a principal ideal domain is free.**

Mathlib has this only for finite rank; the singular chain complex needs it for
arbitrary rank. -/
theorem free_of_submodule_of_pid {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] (N : Submodule R M) :
    Module.Free R N := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    WellOrderingRel.isWellOrder.linearOrder
  haveI : WellFoundedLT (Module.Free.ChooseBasisIndex R M) :=
    ⟨(WellOrderingRel.isWellOrder (α := Module.Free.ChooseBasisIndex R M)).wf⟩
  let e : M ≃ₗ[R] (Module.Free.ChooseBasisIndex R M →₀ R) := (Module.Free.chooseBasis R M).repr
  haveI : Module.Free R (Submodule.map (e : M →ₗ[R] _) N) := free_of_submodule_finsupp _
  exact Module.Free.of_equiv
    (Submodule.equivMapOfInjective (e : M →ₗ[R] _) e.injective N).symm

/-! ## 6. Splitting off a submodule with projective quotient

These are the two lemmas the universal coefficient theorem is built from: the
splitting `Cₙ = Zₙ ⊕ (complement)` is exactly `exists_retraction_of_projective_quotient`
applied to `Q = ker ∂ₙ`, whose quotient `Cₙ/Q ≅ Bₙ₋₁` is a submodule of the free
module `Cₙ₋₁` and hence projective by the theorem above. -/

/-- A submodule with projective quotient is a direct summand: there is a
retraction of its inclusion. -/
theorem exists_retraction_of_projective_quotient {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (Q : Submodule R M) [Module.Projective R (M ⧸ Q)] :
    ∃ r : M →ₗ[R] Q, ∀ x : Q, r x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  have hs' : ∀ z : M ⧸ Q, Q.mkQ (s z) = z := fun z => LinearMap.congr_fun hs z
  have hmem : ∀ x : M, x - s (Q.mkQ x) ∈ Q := by
    intro x
    rw [← Submodule.ker_mkQ Q, LinearMap.mem_ker, map_sub, hs', sub_self]
  refine ⟨(LinearMap.id - s.comp Q.mkQ).codRestrict Q (fun x => by simpa using hmem x), ?_⟩
  intro x
  apply Subtype.ext
  have hx : Q.mkQ (x : M) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact x.2
  simp [LinearMap.codRestrict_apply, hx]

/-- A linear map defined on a submodule with projective quotient extends to the
whole module. -/
theorem exists_extend_of_projective_quotient {R M P : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] (Q : Submodule R M)
    [Module.Projective R (M ⧸ Q)] (f : Q →ₗ[R] P) :
    ∃ F : M →ₗ[R] P, ∀ x : Q, F x = f x := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient Q
  exact ⟨f.comp r, fun x => by rw [LinearMap.comp_apply, hr]⟩

/-- A submodule of a free module over a principal ideal domain is projective. -/
theorem projective_of_submodule_of_pid {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (N : Submodule R M) : Module.Projective R N :=
  haveI := free_of_submodule_of_pid N
  Module.Projective.of_basis (Module.Free.chooseBasis R N)

end GroupApproximation.AlgTop.PID
