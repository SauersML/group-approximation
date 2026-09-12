import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Higman.RecursivePresentationBridge
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceCurrentLeavittCompressionClosure

/-!
# `mf_recognition_complexity.tex`, `lem:seed`: a recursive presentation of `H`

This file is the Lean form of the first lemma of the section "The complexity of
recognizing MF groups", at the manuscript's own group, together with the entry
of `tab:objects` that names it:

> `H`: the non-MF group `EL₁₂(L_{F₂}(1,2))` of `[NonMF]`.

> **Lemma (`lem:seed`).**  The group `H = EL₁₂(L_{F₂}(1,2))` is finitely
> generated and has decidable word problem.  In particular, it has a recursive
> presentation on finitely many generators.

`Manuscript.MFRecognition.SeedPresentation` fixes a different, finitely
presented seed and proves a different statement about it; this module is the
printed lemma at the printed group, so the two live side by side and this one
uses its own namespace, `LeavittSwitch`.

## The one cited input

The generation half of `lem:seed` is proved here.  The decidability half rests
on the Diamond Lemma normal form for `L_{F₂}(1,2)`, which this development does
not carry out, so it is stated as `DiamondLemmaWordProblem` and taken as a
leading hypothesis by every declaration that uses it, in the style of
`Manuscript.NonMF.TorsionFree.HullInputs`.  Nothing here is postulated and no
declaration has an open leaf: a consumer that wants the conclusions of
`lem:seed` supplies the citation, and it is then visible in the statement.

The reference is G. M. Bergman, *The diamond lemma for ring theory*, together
with the standard reduced `F₂`-basis of the Leavitt algebra recorded in
`[Leavitt]`.

## What is proved

*Generation.*  "Let `Y` be the set of elements `e_ij(a)` with `i ≠ j` and
`a ∈ {1, s₀, s₁, t₀, t₁}`.  Since `e_ij(a+b) = e_ij(a)e_ij(b)` and
`[e_ik(a), e_kj(b)] = e_ij(ab)` for distinct `i, j, k`, induction on monomial
length shows that `H = ⟨Y⟩`."  `printedY` is the displayed set,
`rootCoefficientSubalgebra` is the induction on monomial length in its standard
packaged form --- the coefficients whose root elements all lie in a fixed
subgroup form a unital `F₂`-subalgebra, by exactly the two displayed identities
--- and `closure_printedY_eq_top` concludes from the fact, already in the
repository, that `s₀, s₁, t₀, t₁` generate `L_{F₂}(1,2)` as an `F₂`-algebra.

*Everything after the citation.*  A decidable word problem is recursively
enumerable (`rePred_wordProblem_seedGen`), so `H` carries a
`Higman.RecursivePresentation` (`recursivePresentationH`); the relator set `T`
is the kernel of the evaluation map and comes with a primitive-recursive search
(`seedSearch`, `seedSearch_spec`).  The identification `⟨Y | T⟩ ≅ H`
(`seedEquiv`) needs only generation, so it carries no hypothesis at all.
`printedRecursivePresentationOfH` bundles the data that `lem:switch` consumes.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace LeavittSwitch

open Higman

-- The commutator bracket `⁅x, y⁆` used in `rootCoefficientSubalgebra.mul_mem'`
-- takes its `Bracket` instance from this scope.  `open scoped` does not travel
-- through imports, so every file in the repository that writes `⁅_, _⁆` opens
-- it (`Leavitt.ElementaryRoots`, `Leavitt.ElementaryGroup`, and others).
open scoped commutatorElement

/-! ## The group `H` and the printed generating set `Y` -/

/-- **`tab:objects`.**  `H` is the non-MF group `EL₁₂(L_{F₂}(1,2))` of the
companion paper. -/
noncomputable abbrev H : Type := OneSidedMFRadical.RankTwelveEndpoint.H

/-- The coefficient ring `R = L_{F₂}(1,2)`. -/
abbrev R : Type := OneSidedMFRadical.RankTwelveEndpoint.R

/-- The canonical binary Leavitt family `s₀, s₁, t₀, t₁` of `R`. -/
noncomputable abbrev leavittFamily : LeavittFamily R :=
  OneSidedMFRadical.RankTwelveEndpoint.leavittFamily

/-- **`lem:seed`, first clause.**  "The group `H = EL₁₂(L_{F₂}(1,2))` is
finitely generated."  This is the companion paper's `lem:elfg` at rank twelve,
already in the repository. -/
theorem printed_finitelyGenerated : Group.FG H :=
  OneSidedMFRadical.RankTwelveEndpoint.finitelyGenerated

/-- The printed coefficient set `{1, s₀, s₁, t₀, t₁}`. -/
def printedCoefficients : Set R :=
  {1, leavittFamily.s0, leavittFamily.s1, leavittFamily.t0, leavittFamily.t1}

theorem one_mem_printedCoefficients : (1 : R) ∈ printedCoefficients :=
  Set.mem_insert _ _

theorem printedCoefficients_finite : printedCoefficients.Finite :=
  ((((Set.finite_singleton leavittFamily.t1).insert leavittFamily.t0).insert
    leavittFamily.s1).insert leavittFamily.s0).insert 1

/-- **`lem:seed`.**  "Let `Y` be the set of elements `e_ij(a)` with `i ≠ j` and
`a ∈ {1, s₀, s₁, t₀, t₁}`." -/
def printedY : Set H :=
  {z | ∃ (i j : Fin 12) (hij : i ≠ j) (a : R),
    a ∈ printedCoefficients ∧ elementaryRoot i j hij a = z}

/-- The totalized elementary root: `e_ij(a)` off the diagonal and `1` on it.
It exists only to exhibit `Y` as the image of a finite index set and to index
the generators computably. -/
noncomputable def rootTotal (i j : Fin 12) (a : R) : H :=
  if h : i ≠ j then elementaryRoot i j h a else 1

theorem rootTotal_of_ne {i j : Fin 12} (hij : i ≠ j) (a : R) :
    rootTotal i j a = elementaryRoot i j hij a :=
  dif_pos hij

theorem rootTotal_of_not_ne {i j : Fin 12} (hij : ¬ i ≠ j) (a : R) :
    rootTotal i j a = 1 :=
  dif_neg hij

theorem rootTotal_mem_insert (i j : Fin 12) {a : R}
    (ha : a ∈ printedCoefficients) :
    rootTotal i j a ∈ insert (1 : H) printedY := by
  by_cases hij : i ≠ j
  · exact Set.mem_insert_of_mem _ ⟨i, j, hij, a, ha, (rootTotal_of_ne hij a).symm⟩
  · exact Set.mem_insert_iff.mpr (Or.inl (rootTotal_of_not_ne hij a))

/-- The printed generating set is finite: it is the image of `12 × 12 × 5`
pieces of data. -/
theorem printedY_finite : printedY.Finite := by
  haveI : Finite (printedCoefficients : Set R) := printedCoefficients_finite.to_subtype
  refine Set.Finite.subset (Set.finite_range
    (fun p : (Fin 12 × Fin 12) × (printedCoefficients : Set R) =>
      rootTotal p.1.1 p.1.2 (p.2 : R))) ?_
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  exact ⟨((i, j), ⟨a, ha⟩), rootTotal_of_ne hij a⟩

/-! ## `H = ⟨Y⟩`

The printed induction on monomial length, in its packaged form: the two
displayed identities say exactly that the coefficients whose elementary roots
all lie in a fixed subgroup are closed under addition and under multiplication,
so they form a unital `F₂`-subalgebra. -/

/-- **The engine of `lem:seed`'s first half.**  "Since `e_ij(a+b) =
e_ij(a)e_ij(b)` and `[e_ik(a), e_kj(b)] = e_ij(ab)` for distinct `i, j, k`":
the coefficients whose elementary roots in every off-diagonal position lie in
`K` form a unital `F₂`-subalgebra of `R`. -/
def rootCoefficientSubalgebra (K : Subgroup H)
    (hunit : ∀ (i j : Fin 12) (hij : i ≠ j), elementaryRoot i j hij (1 : R) ∈ K) :
    Subalgebra (ZMod 2) R where
  carrier := {a | ∀ (i j : Fin 12) (hij : i ≠ j), elementaryRoot i j hij a ∈ K}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryRoot_mul]
    exact K.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ :=
      Fin.exists_ne_and_ne_of_two_lt i j (by omega : (2 : ℕ) < 12)
    have hik : i ≠ k := hki.symm
    have hc : ⁅elementaryRoot i k hik a, elementaryRoot k j hkj b⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem
        (K.mul_mem (K.mul_mem (ha i k hik) (hb k j hkj))
          (K.inv_mem (ha i k hik)))
        (K.inv_mem (hb k j hkj))
    rw [elementaryRoot_commutator i k j hik hkj hij a b] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, elementaryRoot_zero] using K.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij

/-- **`lem:seed`.**  "Induction on monomial length shows that `H = ⟨Y⟩`." -/
theorem closure_printedY_eq_top : Subgroup.closure printedY = ⊤ := by
  have hsub : ∀ (i j : Fin 12) (hij : i ≠ j) (a : R), a ∈ printedCoefficients →
      elementaryRoot i j hij a ∈ Subgroup.closure printedY := by
    intro i j hij a ha
    exact Subgroup.subset_closure ⟨i, j, hij, a, ha, rfl⟩
  have hunit : ∀ (i j : Fin 12) (hij : i ≠ j),
      elementaryRoot i j hij (1 : R) ∈ Subgroup.closure printedY := by
    intro i j hij
    exact hsub i j hij 1 one_mem_printedCoefficients
  have hCtop :
      rootCoefficientSubalgebra (Subgroup.closure printedY) hunit = ⊤ := by
    apply top_unique
    rw [←
      OneSidedMFRadical.RankTwelveEndpoint.manuscriptLeavittNamedGenerators_adjoin_eq_top]
    refine Algebra.adjoin_le ?_
    intro a ha i j hij
    exact hsub i j hij a (Set.mem_insert_of_mem _ ha)
  have hall : ∀ (i j : Fin 12) (hij : i ≠ j) (a : R),
      elementaryRoot i j hij a ∈ Subgroup.closure printedY := by
    intro i j hij a
    have ha : a ∈ rootCoefficientSubalgebra (Subgroup.closure printedY) hunit := by
      simp [hCtop]
    exact ha i j hij
  apply top_unique
  rw [← elementaryRootSet_generate (I := Fin 12) (R := R), Subgroup.closure_le]
  rintro g ⟨i, j, hij, a, rfl⟩
  exact hall i j hij a

/-! ## A computably indexed generating family

`lem:switch` asks for a recursive presentation "on a computable set of
generators", so the printed finite set `Y` is presented as the range of a family
indexed by the naturals. -/

/-- The printed coefficients, listed in the printed order `1, s₀, s₁, t₀, t₁`. -/
noncomputable def coeffOf : ℕ → R
  | 0 => 1
  | 1 => leavittFamily.s0
  | 2 => leavittFamily.s1
  | 3 => leavittFamily.t0
  | 4 => leavittFamily.t1
  | _ + 5 => 1

theorem coeffOf_mem (n : ℕ) : coeffOf n ∈ printedCoefficients := by
  match n with
  | 0 => simp [coeffOf, printedCoefficients]
  | 1 => simp [coeffOf, printedCoefficients]
  | 2 => simp [coeffOf, printedCoefficients]
  | 3 => simp [coeffOf, printedCoefficients]
  | 4 => simp [coeffOf, printedCoefficients]
  | _ + 5 => simp [coeffOf, printedCoefficients]

theorem exists_coeffOf {a : R} (ha : a ∈ printedCoefficients) :
    ∃ k : ℕ, k < 5 ∧ coeffOf k = a := by
  simp only [printedCoefficients, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h | h | h
  · exact ⟨0, by omega, by simp [coeffOf, h]⟩
  · exact ⟨1, by omega, by simp [coeffOf, h]⟩
  · exact ⟨2, by omega, by simp [coeffOf, h]⟩
  · exact ⟨3, by omega, by simp [coeffOf, h]⟩
  · exact ⟨4, by omega, by simp [coeffOf, h]⟩

/-- The finite index set of the printed generating family: an ordered pair of
matrix positions together with one of the five printed coefficients. -/
abbrev SeedIndex : Type := (Fin 12 × Fin 12) × Fin 5

/-- The printed generating family on its finite index set. -/
noncomputable def seedGenOf (p : SeedIndex) : H :=
  rootTotal p.1.1 p.1.2 (coeffOf (p.2 : ℕ))

/-- A total decoding of the naturals onto the finite index set. -/
def decodeSeedIndex (n : ℕ) : SeedIndex :=
  (Encodable.decode (α := SeedIndex) n).getD default

theorem decodeSeedIndex_surjective (p : SeedIndex) :
    ∃ n : ℕ, decodeSeedIndex n = p :=
  ⟨Encodable.encode p, by simp [decodeSeedIndex, Encodable.encodek]⟩

/-- **The generating family of `lem:seed`**, enumerated by a computable index:
the printed set `Y`, with the diagonal positions read as the identity. -/
noncomputable def seedGen (n : ℕ) : H :=
  seedGenOf (decodeSeedIndex n)

theorem range_seedGen_subset : Set.range seedGen ⊆ insert (1 : H) printedY := by
  rintro _ ⟨n, rfl⟩
  show rootTotal (decodeSeedIndex n).1.1 (decodeSeedIndex n).1.2
      (coeffOf ((decodeSeedIndex n).2 : ℕ)) ∈ insert (1 : H) printedY
  exact rootTotal_mem_insert _ _ (coeffOf_mem _)

theorem printedY_subset_range_seedGen : printedY ⊆ Set.range seedGen := by
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  obtain ⟨k, hk5, hk⟩ := exists_coeffOf ha
  obtain ⟨n, hn⟩ := decodeSeedIndex_surjective ((i, j), ⟨k, hk5⟩)
  refine ⟨n, ?_⟩
  have hval : seedGen n = rootTotal i j (coeffOf k) := by
    simp only [seedGen, hn, seedGenOf]
  rw [hval, hk, rootTotal_of_ne hij]

/-- **`lem:seed`, generation on the computable index.**  `H = ⟨Y⟩`. -/
theorem closure_range_seedGen_eq_top : Subgroup.closure (Set.range seedGen) = ⊤ := by
  apply top_unique
  rw [← closure_printedY_eq_top]
  exact Subgroup.closure_mono printedY_subset_range_seedGen

/-! ## The relator set `T` and the presentation `⟨Y | T⟩`

These two do not depend on the cited input: the presentation `⟨Y | T⟩` is `H`
by generation alone. -/

/-- Every element of the free group on the standard alphabet is the value of a
raw word. -/
theorem freeEval_surjective (x : FreeGroup ℕ) : ∃ w : RawWord, freeEval w = x := by
  have hx : x ∈ Subgroup.closure (Set.range (FreeGroup.of : ℕ → FreeGroup ℕ)) := by
    rw [FreeGroup.closure_range_of]
    exact Subgroup.mem_top x
  exact (Higman.mem_closure_iff_exists_evalRaw FreeGroup.of x).1 hx

/-- **`lem:seed`, the relator set `T`.**  The words in `Y^{±1}` that represent
`1` in `H`, read in the free group on the generating indices. -/
abbrev seedRelators : Set (FreeGroup ℕ) := Higman.relatorSetOf seedGen

theorem mem_seedRelators (w : RawWord) :
    freeEval w ∈ seedRelators ↔ evalRaw seedGen w = 1 :=
  Higman.mem_relatorSetOf seedGen w

/-- **`lem:seed`, the presentation.**  `⟨Y | T⟩` is `H`.  Generation is all
this needs, so it carries no hypothesis. -/
noncomputable def seedEquiv : PresentedGroup seedRelators ≃* H :=
  Higman.presentedGroupEquiv closure_range_seedGen_eq_top

/-! ## The cited input, and what follows from it -/

-- CITED INPUT: Bergman, the diamond lemma for ring theory, together with the
-- standard reduced basis of the Leavitt algebra.  Stated, never established
-- here; consumers take it as a leading hypothesis.
/-- **`lem:seed`, second clause, as a hypothesis.**

> The monomials in `s₀,s₁,t₀,t₁` that contain no subword `t_i s_j` and no
> subword `s₁t₁` form the standard reduced `F₂`-basis of `L_{F₂}(1,2)`.
> Indeed, with the orientation `t_i s_j → δ_ij` and `s₁t₁ → 1 + s₀t₀`, the two
> critical words `t_i s₁ t₁` and `s₁ t₁ s_j` resolve to a common value, and the
> Diamond Lemma gives these monomials as a basis.  Products of reduced monomials
> are computed by the defining reductions, so equality in `L_{F₂}(1,2)` is
> decidable.  So a word in `Y^{±1}` evaluates to an explicit `12 × 12` matrix
> over `L_{F₂}(1,2)`, and it represents `1` in `H` if and only if that matrix is
> the identity.  The set of words representing `1` is decidable.

That conclusion, at the printed generating family, is exactly the statement
below. -/
def DiamondLemmaWordProblem : Prop :=
  ∃ decider : RawWord → Bool,
    Computable decider ∧
      ∀ w : RawWord, decider w = true ↔ evalRaw seedGen w = 1

/-- **`lem:seed`.**  "The set of words representing `1` is decidable, so
recursively enumerable." -/
theorem rePred_wordProblem_seedGen (hDiamond : DiamondLemmaWordProblem) :
    REPred fun w : RawWord => evalRaw seedGen w = 1 := by
  obtain ⟨decider, hcomp, hspec⟩ := hDiamond
  have hrewrite : (fun w : RawWord => evalRaw seedGen w = 1) =
      fun w : RawWord => ∃ _ : Unit, decider w = true := by
    funext w
    refine propext ⟨fun h => ⟨(), (hspec w).2 h⟩, ?_⟩
    rintro ⟨-, h⟩
    exact (hspec w).1 h
  rw [hrewrite]
  exact WordProblemRE.rePred_exists_eq_true ((hcomp.comp Computable.fst).to₂)

/-- **`lem:seed`, conclusion.**  "In particular, `H` has a recursive
presentation on finitely many generators." -/
noncomputable def recursivePresentationH (hDiamond : DiamondLemmaWordProblem) :
    Higman.RecursivePresentation H where
  gen := seedGen
  spans := closure_range_seedGen_eq_top
  re := rePred_wordProblem_seedGen hDiamond

/-- The primitive-recursive search enumerating `T`. -/
noncomputable def seedSearch (hDiamond : DiamondLemmaWordProblem) :
    RawWord → ℕ → Bool :=
  (Higman.exists_enumerable_relators (recursivePresentationH hDiamond)).choose

theorem primrec₂_seedSearch (hDiamond : DiamondLemmaWordProblem) :
    Primrec₂ (seedSearch hDiamond) :=
  (Higman.exists_enumerable_relators (recursivePresentationH hDiamond)).choose_spec.1

/-- The search recognizes exactly `T`. -/
theorem seedSearch_spec (hDiamond : DiamondLemmaWordProblem) (v : RawWord) :
    freeEval v ∈ seedRelators ↔ ∃ n, seedSearch hDiamond v n = true :=
  (Higman.exists_enumerable_relators (recursivePresentationH hDiamond)).choose_spec.2 v

/-! ## The bundled input of `lem:switch` -/

/-- **The data `⟨Y | T⟩` that `lem:switch` consumes.**  Finitely many
generators presented as a computable family, a primitive-recursive enumeration
of the relator set `T`, and the identification of the presented group with
`H`. -/
structure RecursivePresentationOfH where
  /-- The generating family, indexed computably. -/
  gen : ℕ → H
  /-- Only the finitely many printed generators of `Y` occur in its range. -/
  genRange : Set.range gen ⊆ insert 1 printedY
  /-- The printed generating set is finite. -/
  finiteY : printedY.Finite
  /-- `H = ⟨Y⟩`. -/
  spans : Subgroup.closure (Set.range gen) = ⊤
  /-- The search enumerating the relator set. -/
  search : RawWord → ℕ → Bool
  /-- The search is primitive recursive. -/
  search_primrec : Primrec₂ search
  /-- It enumerates exactly `T`, the words representing `1`. -/
  search_spec : ∀ v : RawWord,
    freeEval v ∈ Higman.relatorSetOf gen ↔ ∃ n, search v n = true
  /-- `⟨Y | T⟩ ≅ H`. -/
  equiv : PresentedGroup (Higman.relatorSetOf gen) ≃* H

/-- **`lem:seed`, in the form `lem:switch` uses it.** -/
noncomputable def printedRecursivePresentationOfH
    (hDiamond : DiamondLemmaWordProblem) : RecursivePresentationOfH where
  gen := seedGen
  genRange := range_seedGen_subset
  finiteY := printedY_finite
  spans := closure_range_seedGen_eq_top
  search := seedSearch hDiamond
  search_primrec := primrec₂_seedSearch hDiamond
  search_spec := seedSearch_spec hDiamond
  equiv := seedEquiv

end LeavittSwitch
end MFRecognition
end Manuscript
end GroupApproximation
