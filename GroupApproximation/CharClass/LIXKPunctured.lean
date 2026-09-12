import GroupApproximation.CharClass.MayerVietorisElement
import GroupApproximation.CharClass.ThomToolkitInstance
import GroupApproximation.Meta.AxiomGuard

/-!
# Punctured acyclicity at finitely many points

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4, item 2 of the first deliverable).

`CharClass/ThomPuncturedRecursion.lean` gives `PuncturedAcyclic Z d z`, whose third field
says `H^k(Z ∖ {z}; F₂) = 0` for `k ≥ d`.  The `k`-zero Step C needs the same statement for
the complement of the `k+1` zeros, and the recursion does not provide it.  This file adds
it, by induction on the finite set, with one Mayer–Vietoris step.

## The Mayer–Vietoris direction that was missing

`MayerVietorisVanishing.isZero_cohomology_of_cover` reads the sequence at the **ambient**
term: it concludes `H^{m+1}(X) = 0` from vanishing on the intersection and on the pieces.
What is needed here is the opposite end,

```text
   H^m(U) ⊕ H^m(V) ⟶ H^m(U ∩ V) ⟶^δ H^{m+1}(U ∪ V),
```

read at `H^m(U ∩ V)`: if the two pieces have no `H^m` then `δ` is injective, and if the
ambient space has no `H^{m+1}` then `δ` is zero, so `H^m(U ∩ V) = 0`.  That is
`isZero_inter_of_cover` below, and it is `mvExactW` plus two `Subsingleton`s — the same
three-line shape as the vanishing form, at the other end of the sequence.

## The induction

With `A = N ∖ ({z₀} ∪ T)` and `B = N ∖ {z₀'}` for a new point `z₀'`, the two are open (the
punctures are finite, hence closed, since the space is `T₁`), they cover `N` exactly when
the new point is not already punctured, and their intersection is the complement of the
enlarged set.  `H^m(A) = 0` is the induction hypothesis, `H^m(B) = 0` is
`PuncturedAcyclic.puncturedVanish` at the new point, and `H^{m+1}(N) = 0` is
`PuncturedAcyclic.vanish` because `m + 1 > d`.

Note where the hypothesis is `∀ z, PuncturedAcyclic N d z` rather than at one point: the
induction punctures at a *new* point at every step, so one-point acyclicity is needed at
every point of `N`.  For the LIX base this costs nothing —
`LemmaTwoStepC.puncturedAcyclic_lixZero`'s producer already takes the point as an argument.

## Main results

* `isZero_inter_of_cover` — Mayer–Vietoris read at the intersection.
* `isZero_punctured_finite` — **`H^m(N ∖ S; F₂) = 0`** for finite non-empty `S`, `m ≥ d`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. Mayer–Vietoris, read at the intersection -/

variable {X : TopCat.{0}}

/-- **Mayer–Vietoris, intersection form.**  If neither piece of a two-element open cover
has cohomology in degree `m`, and the ambient space has none in degree `m + 1`, then the
intersection has none in degree `m`.

This is the exactness `H^m(U) ⊕ H^m(V) → H^m(U ∩ V) →^δ H^{m+1}(X)` read at the middle:
the first arrow has zero image, so `δ` is injective, and `δ` lands in a zero group. -/
theorem isZero_inter_of_cover (U V : Opens X) (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hU : IsZero (Hmod2 (mvU U) m)) (hV : IsZero (Hmod2 (mvU V) m))
    (hX : IsZero (Hmod2 X (m + 1))) :
    IsZero (Hmod2 (mvInter U V) m) := by
  haveI := ModuleCat.subsingleton_of_isZero hU
  haveI := ModuleCat.subsingleton_of_isZero hV
  haveI := ModuleCat.subsingleton_of_isZero hX
  have hsub : ∀ w : Hmod2 (mvInter U V) m, w = 0 := by
    intro w
    obtain ⟨a, b, hab⟩ := (mvExactW U V hUV m w).mp (Subsingleton.elim _ _)
    rw [← hab, Subsingleton.elim a 0, Subsingleton.elim b 0, map_zero, map_zero, add_zero]
  haveI : Subsingleton (Hmod2 (mvInter U V) m) := ⟨fun a b => by rw [hsub a, hsub b]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The same over a plain topological space, which is the shape the induction below uses. -/
theorem isZero_inter_of_cover' (N : Type) [TopologicalSpace N] (U V : Opens N)
    (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hU : IsZero (cohomologyZMod2 (TopCat.of ↥(U : Set N)) m))
    (hV : IsZero (cohomologyZMod2 (TopCat.of ↥(V : Set N)) m))
    (hX : IsZero (cohomologyZMod2 (TopCat.of N) (m + 1))) :
    IsZero (cohomologyZMod2 (TopCat.of ↥((U : Set N) ∩ (V : Set N))) m) :=
  isZero_inter_of_cover (X := TopCat.of N) U V hUV m hU hV hX

/-! ## 2. Transport along an equality of subsets -/

/-- Vanishing transports along an equality of subsets, through the toolkit's
homeomorphism invariance and `Homeomorph.setCongr`. -/
theorem isZero_cohomology_setCongr {N : Type} [TopologicalSpace N] {s t : Set N}
    (h : s = t) (m : ℕ) (ht : IsZero (cohomologyZMod2 (TopCat.of ↥t) m)) :
    IsZero (cohomologyZMod2 (TopCat.of ↥s) m) :=
  cohomologyToolkit.homeo _ _ (Homeomorph.setCongr h) m ht

/-! ## 3. The induction -/

variable {N : Type} [TopologicalSpace N] [T1Space N] {d : ℕ}

/-- **The induction.**  `H^m` of the complement of a non-empty finite set vanishes.

The step punctures at a point `a` that is **not** already punctured — which is exactly the
hypothesis `Finset.induction_on` hands over — so the two opens `N ∖ T` and `N ∖ {a}` really
do cover `N`, and their intersection is `N ∖ (T ∪ {a})`.  The `T = ∅` branch of the step is
the one-point statement itself. -/
theorem isZero_punctured_finset (hac : ∀ z : N, PuncturedAcyclic N d z) {m : ℕ}
    (hm : d ≤ m) : ∀ T : Finset N, T.Nonempty →
    IsZero (cohomologyZMod2 (TopCat.of ↥((T : Set N)ᶜ)) m) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun h => absurd h (by simp)
  | insert a T ha ih =>
    intro _
    rcases T.eq_empty_or_nonempty with rfl | hT
    · refine isZero_cohomology_setCongr (t := ({a}ᶜ : Set N)) ?_ m
        ((hac a).puncturedVanish m hm)
      ext x
      simp
    · have hUopen : IsOpen (((T : Set N))ᶜ) := T.finite_toSet.isClosed.isOpen_compl
      have hVopen : IsOpen (({a}ᶜ : Set N)) := isClosed_singleton.isOpen_compl
      have hanot : a ∉ (T : Set N) := by simpa using ha
      have hUV : (⟨((T : Set N))ᶜ, hUopen⟩ : Opens N) ⊔ ⟨({a}ᶜ : Set N), hVopen⟩ = ⊤ := by
        refine TopologicalSpace.Opens.ext ?_
        rw [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top]
        ext x
        simp only [TopologicalSpace.Opens.coe_mk, Set.mem_union, Set.mem_compl_iff,
          Set.mem_singleton_iff, Set.mem_univ, iff_true]
        by_cases hx : x = a
        · subst hx
          exact Or.inl hanot
        · exact Or.inr hx
      have hinter := isZero_inter_of_cover' N ⟨((T : Set N))ᶜ, hUopen⟩
        ⟨({a}ᶜ : Set N), hVopen⟩ hUV m (ih hT) ((hac a).puncturedVanish m hm)
        ((hac a).vanish (m + 1) (by omega))
      refine isZero_cohomology_setCongr
        (t := (((T : Set N))ᶜ ∩ ({a}ᶜ : Set N))) ?_ m hinter
      ext x
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_inter_iff,
        Set.mem_singleton_iff, TopologicalSpace.Opens.coe_mk]
      tauto

/-- **Punctured acyclicity at finitely many points.**  If `N` is top-punctured acyclic of
dimension `d` at every one of its points, then the complement of any finite non-empty set
has no mod-2 cohomology in any degree `≥ d`.

This is item 2 of the `k`-zero Step C's first deliverable: at `S` the set of the `k+1`
zeros and `m = 2r`, it is the hypothesis that makes `j : H^{2r}(N, N ∖ S) → H^{2r}(N)`
surjective. -/
theorem isZero_punctured_finite (hac : ∀ z : N, PuncturedAcyclic N d z) {m : ℕ} (hm : d ≤ m)
    {S : Set N} (hfin : S.Finite) (hne : S.Nonempty) :
    IsZero (cohomologyZMod2 (TopCat.of ↥(Sᶜ : Set N)) m) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  refine isZero_cohomology_setCongr (t := ((hfin.toFinset : Set N)ᶜ)) ?_ m
    (isZero_punctured_finset hac hm hfin.toFinset ⟨z₀, hfin.mem_toFinset.mpr hz₀⟩)
  rw [Set.Finite.coe_toFinset]

/-! Audited on every build. -/

#audit_axioms isZero_inter_of_cover
#audit_axioms isZero_punctured_finite

end GroupApproximation.CharClass
