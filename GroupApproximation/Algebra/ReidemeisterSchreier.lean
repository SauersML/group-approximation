import GroupApproximation.Algebra.SchreierGenerators
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Reidemeister--Schreier: relators of a finite-index subgroup

`Algebra/SchreierGenerators.lean` produces the generators of a finite-index
subgroup.  This module produces the *relators*, which is the other half of the
Reidemeister--Schreier rewriting process, and assembles the two into finite
presentation.

## The rewriting theorem

`normalClosure_subgroupOf_eq` is the mathematical content:

> if `N = ⟪R⟫^F` is the normal closure in `F` of a set `R`, and `N ≤ P`, then
> inside `P` the subgroup `N` is the normal closure of the **transversal
> conjugates** `{ t · r · t⁻¹ : t ∈ reps, r ∈ R }`.

Its proof is one line of algebra: an arbitrary conjugate `f · r · f⁻¹` factors
as `λ · (t · r · t⁻¹) · λ⁻¹` with `λ = f·sec(f)⁻¹ ∈ P` and `t = sec(f) ∈ reps`,
so it is a `P`-conjugate of a transversal conjugate.  Since `reps` is finite and
`R` is finite, the new relator set is finite --- which is exactly why finite
presentation survives a finite-index passage.

## What is still an input

`isFinitelyPresented_subgroup_of_finiteIndex` needs one further fact, and only
one: that a finite-index subgroup of a *free* group of finite rank is finitely
presented.  Mathlib supplies the freeness --- `subgroupIsFreeOfIsFree`, the
Nielsen--Schreier theorem --- but not the *rank*: the Schreier index formula
`rank = 1 + [F:P](n-1)` is not in Mathlib at this revision, and "finitely
generated and free" does not reduce to "free on a finite basis" without an
argument Mathlib also does not have.  `FreeFiniteIndexFinitelyPresented` names
that input; nothing here assumes it, and every theorem that uses it takes it
explicitly.

Note that `Algebra/SchreierGenerators.lean` *does* prove such a subgroup is
finitely generated (`group_fg_of_finiteIndex`), so what is missing is genuinely
the passage from "finitely generated and free" to "free on a finite basis", and
not the generation.
-/

namespace GroupApproximation
namespace FiniteIndex

universe u

/-! ## The transversal conjugates -/

/-- The **transversal conjugates** of a relator set: the conjugates of `R` by the
chosen coset representatives, viewed inside the subgroup. -/
def transversalConjugates {F : Type u} [Group F] {P : Subgroup F}
    (tr : RightTransversal F P) (R : Set F) : Set ↥P :=
  {u : ↥P | ∃ t ∈ tr.reps, ∃ r ∈ R, (u : F) = t * r * t⁻¹}

/-- **The transversal conjugates of a finite relator set are finite.**  This is
the whole reason finite presentation survives a finite-index passage: the index
is finite, so `reps` is. -/
theorem transversalConjugates_finite {F : Type u} [Group F] {P : Subgroup F}
    (tr : RightTransversal F P) {R : Set F} (hR : R.Finite) :
    (transversalConjugates tr R).Finite := by
  refine Set.Finite.of_finite_image ?_ Subtype.coe_injective.injOn
  refine Set.Finite.subset
    (((tr.reps.finite_toSet).prod hR).image fun p : F × F => p.1 * p.2 * p.1⁻¹) ?_
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨t, ht, r, hr, hval⟩ := hu
  exact ⟨(t, r), ⟨Finset.mem_coe.mpr ht, hr⟩, hval.symm⟩

/-! ## The rewriting theorem -/

/-- **Reidemeister--Schreier.**  A normal closure contained in a subgroup is,
inside that subgroup, the normal closure of the transversal conjugates.

The inclusion `⊇` is normality of `N`; the inclusion `⊆` is the factorisation
`f = (f·sec(f)⁻¹) · sec(f)` of an arbitrary conjugating element into a subgroup
part and a coset representative. -/
theorem normalClosure_subgroupOf_eq {F : Type u} [Group F] {P : Subgroup F}
    (tr : RightTransversal F P) {R : Set F}
    (hle : Subgroup.normalClosure R ≤ P) :
    (Subgroup.normalClosure R).subgroupOf P =
      Subgroup.normalClosure (transversalConjugates tr R) := by
  have hNnormal : (Subgroup.normalClosure R).Normal := Subgroup.normalClosure_normal
  have hmemN : ∀ t : F, ∀ r ∈ R, t * r * t⁻¹ ∈ Subgroup.normalClosure R := by
    intro t r hr
    exact hNnormal.conj_mem r (Subgroup.subset_normalClosure hr) t
  refine le_antisymm ?_ ?_
  · -- `N ∩ P ≤ ⟪transversal conjugates⟫^P`, by factoring each conjugating element
    have hmain : Subgroup.normalClosure R ≤
        (Subgroup.normalClosure (transversalConjugates tr R)).map P.subtype := by
      have hclosure : Subgroup.normalClosure R =
          Subgroup.closure (Group.conjugatesOfSet R) := rfl
      rw [hclosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨r, hr, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨f, rfl⟩ := isConj_iff.mp hconj
      obtain ⟨lam, hlam, t, ht, hft⟩ : ∃ lam ∈ P, ∃ t ∈ tr.reps, f = lam * t :=
        ⟨tr.retract f, tr.retract_mem f, tr.sec f, tr.sec_mem_reps f,
          (tr.retract_mul_sec f).symm⟩
      subst hft
      have htmem : t * r * t⁻¹ ∈ P := hle (hmemN t r hr)
      have hw : (⟨t * r * t⁻¹, htmem⟩ : ↥P) ∈ transversalConjugates tr R :=
        ⟨t, ht, r, hr, rfl⟩
      refine ⟨⟨lam, hlam⟩ * ⟨t * r * t⁻¹, htmem⟩ * (⟨lam, hlam⟩ : ↥P)⁻¹, ?_, ?_⟩
      · exact Subgroup.normalClosure_normal.conj_mem _
          (Subgroup.subset_normalClosure hw) _
      · show lam * (t * r * t⁻¹) * lam⁻¹ = lam * t * r * (lam * t)⁻¹
        group
    intro u hu
    obtain ⟨v, hv, hvu⟩ := hmain hu
    have hvu' : v = u := Subtype.ext hvu
    exact hvu' ▸ hv
  · -- `⟪transversal conjugates⟫^P ≤ N ∩ P`, by normality of `N`
    haveI : ((Subgroup.normalClosure R).subgroupOf P).Normal := hNnormal.comap P.subtype
    refine Subgroup.normalClosure_le_normal ?_
    rintro u ⟨t, -, r, hr, hval⟩
    show (u : F) ∈ Subgroup.normalClosure R
    rw [hval]
    exact hmemN t r hr

/-! ## Finite presentation -/

/-- **The one input this module does not prove**: a finite-index subgroup of a
finitely generated free group is finitely presented.  Equivalently, by
Nielsen--Schreier (`subgroupIsFreeOfIsFree`, which Mathlib has), such a subgroup
is free *of finite rank* --- Schreier's index formula, which Mathlib does not
have. -/
def FreeFiniteIndexFinitelyPresented : Prop :=
  ∀ (n : ℕ) (P : Subgroup (FreeGroup (Fin n))), P.FiniteIndex →
    Group.IsFinitelyPresented ↥P

/-- **Finite presentation passes to finite-index subgroups**, given the free
case.  The relator set produced is the set of transversal conjugates of the
original relators, which is finite because the index is. -/
theorem isFinitelyPresented_subgroup_of_finiteIndex
    (hfree : FreeFiniteIndexFinitelyPresented) {Γ : Type u} [Group Γ] (Λ : Subgroup Γ)
    [Λ.FiniteIndex] (hΓ : Group.IsFinitelyPresented Γ) :
    Group.IsFinitelyPresented ↥Λ := by
  classical
  obtain ⟨n, φ, hsurj, R, hRfin, hR⟩ := hΓ.out
  haveI hPfi : (Λ.comap φ).FiniteIndex := by
    apply Subgroup.finiteIndex_iff.mpr
    simpa only [Subgroup.index_comap_of_surjective Λ hsurj] using
      Subgroup.finiteIndex_iff.mp ‹Λ.FiniteIndex›
  obtain ⟨tr⟩ := exists_rightTransversal (Λ.comap φ)
  -- the surjection of the preimage onto the subgroup
  let ψ : ↥(Λ.comap φ) →* ↥Λ :=
    MonoidHom.codRestrict (φ.comp (Λ.comap φ).subtype) Λ fun x => Subgroup.mem_comap.mp x.2
  have hψsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨f, hf⟩ := hsurj (a : Γ)
    have hfmem : f ∈ Λ.comap φ := Subgroup.mem_comap.mpr (by rw [hf]; exact a.2)
    exact ⟨⟨f, hfmem⟩, Subtype.ext hf⟩
  have hkerψ : ψ.ker = (φ.ker).subgroupOf (Λ.comap φ) := by
    ext x
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  -- the kernel is the normal closure of the transversal conjugates
  have hle : Subgroup.normalClosure R ≤ Λ.comap φ := by
    rw [hR]
    intro x hx
    refine Subgroup.mem_comap.mpr ?_
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem Λ
  have hkerfng : ψ.ker.IsFinitelyNormallyGenerated := by
    refine ⟨transversalConjugates tr R, transversalConjugates_finite tr hRfin, ?_⟩
    rw [hkerψ, ← hR]
    exact (normalClosure_subgroupOf_eq tr hle).symm
  haveI : Group.IsFinitelyPresented ↥(Λ.comap φ) := hfree n (Λ.comap φ) hPfi
  exact Group.IsFinitelyPresented.of_surjective ψ hψsurj hkerfng

end FiniteIndex
end GroupApproximation
