import GroupApproximation.GGT.RelHypOsin24CombinedFamily

/-!
# Dahmani--Guirardel--Osin, Proposition 4.35, and the direction the filling
lane needs

## What Proposition 4.35 says

Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), Proposition 4.35 (`\label{transitive}` in `HE.tex` of the arXiv source
`1111.7048`), transcribed:

> Let `G` be a group, `{H_λ}_{λ∈Λ}` a **finite** collection of subgroups of
> `G`, `X ⊆ G`, `Y_λ ⊆ H_λ`.  Suppose that `{H_λ}_{λ∈Λ} ↪_h (G, X)` and, for
> each `λ ∈ Λ`, there is a collection of subgroups `{K_{λμ}}_{μ∈M_λ}` of
> `H_λ` such that `{K_{λμ}}_{μ∈M_λ} ↪_h (H_λ, Y_λ)`.  Then
> `⋃_{λ∈Λ} {K_{λμ}}_{μ∈M_λ} ↪_h (G, Z)`, where `Z = X ∪ (⋃_{λ∈Λ} Y_λ)`.

Its proof is the relative-presentation argument: strongly bounded relative
presentations with linear relative isoperimetric functions are chosen for `G`
over `(X, ℋ)` and for each `H_λ` over `(Y_λ, 𝒦_λ)`, the `𝒮_λ`-cells of a
minimal-type diagram over the first are replaced by diagrams over the second,
and the resulting count of `𝒫`- and `ℛ`-cells is again linear.  Finiteness of
`Λ` enters once, to choose a single constant `C` working for every `λ`.  Both
ends of that argument are Theorem 4.24, the isoperimetric characterisation of
hyperbolic embeddedness, which this repository does not formalise: `↪_h` is
`RelGenSet.IsHyperbolicallyEmbedded`, Definition 4.25 in its geometric form.

## The direction that is needed here is not Proposition 4.35

Proposition 4.35 **removes** the family `{H_λ}` from the conclusion and
replaces it by subgroups of its members.  Hull's Lemma 4.4 needs the opposite
bookkeeping: the original peripheral family `{H_λ}` has to survive **beside**
the auxiliary elementary closures `{E_i}` that the filling cones off, over the
original relative generating set.  In the notation of this file, with `D` the
original relative generating set and `E` the auxiliary one:

* `D.IsHyperbolicallyEmbedded` is `{H_λ} ↪_h (G, X)`;
* `E.IsHyperbolicallyEmbedded` together with a condition relating `E.base` to
  `D.alphabet.carrier` is `{E_i} ↪_h (G, X ∪ ⋃_λ H_λ)`, the second coning-off
  performed over the first relative alphabet;
* the conclusion wanted is `{H_λ} ∪ {E_i} ↪_h (G, X)`.

This is **not** printed in Dahmani--Guirardel--Osin.  The two printed facts
nearest to it are

* Remark 4.26, which gives only the forward implication
  `{H_λ}_{λ∈Λ} ↪_h (G, X)` ⟹ `H_λ ↪_h (G, X ∪ ⋃_{μ≠λ} H_μ)`, and states
  explicitly that its converse fails (`H₁ = G = F(x,y)`, `H₂ = ⟨x⟩`); and
* Corollary 4.27, which moves `↪_h` between two relative generating sets whose
  symmetric difference is finite (`GGT.DGOCorollary427`).

Remark 4.26's counterexample does not refute the statement below: in it,
`{H₂} ↪_h (G, X ∪ H₁)` fails, because `X ∪ H₁ = G` makes the relative metric
of `H₂` bounded.

## Two forms, and the residues of each

The filling lane holds the two families over *nested*, not equal, alphabets:
the auxiliary family is coned off over Hull's alphabet, which contains the
original relative alphabet.  Both forms are therefore stated.

`DGOProposition435Statement` is the **equal-alphabet** form, over
`RelHyp.combinedRelGenSet` (base `D.base`).  Under `E.base =
D.alphabet.carrier` the joint alphabet is *equal* to the auxiliary alphabet,
so clause (a) of `↪_h` is reused rather than transported
(`combinedRelGenSet_hyperbolic`), and clause (b) at an auxiliary index follows
by reading each original peripheral letter as an auxiliary *base* letter
(`combined_relBall_inr_subset`).  Its single residue is clause (b) at an
original index, `DGOProposition435LocalFinitenessStatement`, and
`dgoProposition435Statement_iff_localFiniteness` shows the residue is exactly
the gap.

`DGOProposition435InclusionStatement` is the **nested-alphabet** form, over
`jointRelGenSet`, whose base is the proper part of `D.base`, the base letters
that are not already peripheral letters.  Dropping those leaves the alphabet
unchanged and makes the joint base inversion-closed for free.  Under
`D.alphabet.carrier ⊆ E.base` clause (b) at an auxiliary index still follows
(`jointRelGenSet_relBall_inr_subset`), but clause (a) no longer does: the
joint alphabet is now a *subset* of the auxiliary one, and hyperbolicity does
not pass to a smaller generating set.  So this form has two residues,
`DGOProposition435JointHyperbolicStatement` and
`DGOProposition435JointLocalFinitenessStatement`, and
`dgoProposition435InclusionStatement_of_residues` splits it into exactly them.
`dgoProposition435JointHyperbolic_of_base_eq` discharges the first whenever
the two alphabets do agree, which is what the first filling step supplies.

## Model tests

`isHyperbolicallyEmbedded_combinedRelGenSet_of_isEmpty_left` and
`isHyperbolicallyEmbedded_combinedRelGenSet_of_isEmpty_right` are the two
degenerate tests: with no auxiliary subgroups the statement reduces to its
first hypothesis, and with no original subgroups to its second.

`not_isHyperbolicallyEmbedded_of_base_splits` records what goes wrong if the
enlarged auxiliary base is taken as the joint base instead of the original
one: as soon as every original peripheral element is a product of two joint
base letters, the original relative metric collapses to radius `2` and local
finiteness fails.  That is why `jointRelGenSet` keeps the original base.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace RelLetter

variable {G : Type u} {Λ : Type v} {I : Type w}

/-- **A joint letter read as an auxiliary letter.**  An original peripheral
letter becomes a base letter, which is admissible exactly when the auxiliary
base contains the original relative alphabet. -/
def auxOfJoint : RelLetter G (Sum Λ I) → RelLetter G I
  | base x => base x
  | comp (Sum.inl _) h => base h
  | comp (Sum.inr i) h => comp i h

/-- **A joint letter read as an original letter.**  An auxiliary peripheral
letter becomes a base letter; that reading is admissible only in the degenerate
case where there are no auxiliary letters at all. -/
def origOfJoint : RelLetter G (Sum Λ I) → RelLetter G Λ
  | base x => base x
  | comp (Sum.inl lam) h => comp lam h
  | comp (Sum.inr _) h => base h

@[simp] theorem auxOfJoint_val (a : RelLetter G (Sum Λ I)) :
    (auxOfJoint a).val = a.val := by
  cases a with
  | base _ => rfl
  | comp s _ => cases s <;> rfl

@[simp] theorem origOfJoint_val (a : RelLetter G (Sum Λ I)) :
    (origOfJoint a).val = a.val := by
  cases a with
  | base _ => rfl
  | comp s _ => cases s <;> rfl

theorem listVal_map_auxOfJoint [Group G] (w : List (RelLetter G (Sum Λ I))) :
    listVal (w.map auxOfJoint) = listVal w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
      show (auxOfJoint a).val * listVal (t.map auxOfJoint) = a.val * listVal t
      rw [auxOfJoint_val, ih]

theorem listVal_map_origOfJoint [Group G] (w : List (RelLetter G (Sum Λ I))) :
    listVal (w.map origOfJoint) = listVal w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
      show (origOfJoint a).val * listVal (t.map origOfJoint) = a.val * listVal t
      rw [origOfJoint_val, ih]

/-- Only an auxiliary peripheral letter can be an `i`-component after reading
a joint letter as an auxiliary letter. -/
theorem isCompOf_of_auxOfJoint {a : RelLetter G (Sum Λ I)} {i : I}
    (h : (auxOfJoint a).IsCompOf i) : a.IsCompOf (Sum.inr i) := by
  cases a with
  | base _ => exact h.elim
  | comp s _ =>
      cases s with
      | inl _ => exact h.elim
      | inr _ => exact congrArg Sum.inr h

/-- Only an original peripheral letter can be a `lam`-component after reading
a joint letter as an original letter. -/
theorem isCompOf_of_origOfJoint {a : RelLetter G (Sum Λ I)} {lam : Λ}
    (h : (origOfJoint a).IsCompOf lam) : a.IsCompOf (Sum.inl lam) := by
  cases a with
  | base _ => exact h.elim
  | comp s _ =>
      cases s with
      | inl _ => exact congrArg Sum.inl h
      | inr _ => exact h.elim

end RelLetter

namespace RelHyp

variable {G : Type u} [Group G] {Λ : Type v} {I : Type w}

/-! ## Reading joint words as auxiliary words -/

/-- Avoidance of `Γ_{E_i}` survives reading a joint word as an auxiliary word:
the two words have the same vertices, and the only joint letters that become
`i`-components are the auxiliary `i`-letters themselves. -/
theorem avoidsFrom_map_auxOfJoint {F : Sum Λ I → Subgroup G}
    {Ef : I → Subgroup G} (hF : ∀ j : I, F (Sum.inr j) = Ef j) (i : I) :
    ∀ (u : List (RelLetter G (Sum Λ I))) (p : G),
      AvoidsFrom F (Sum.inr i) u p →
        AvoidsFrom Ef i (u.map RelLetter.auxOfJoint) p := by
  intro u
  induction u with
  | nil => intro _ _; exact trivial
  | cons a t ih =>
      intro p hp
      obtain ⟨hhead, htail⟩ := hp
      refine ⟨?_, ?_⟩
      · rintro ⟨hc, hmem⟩
        refine hhead ⟨RelLetter.isCompOf_of_auxOfJoint hc, ?_⟩
        rw [hF i]
        exact hmem
      · rw [RelLetter.auxOfJoint_val]
        exact ih (p * a.val) htail

/-- **Clause (b) of `↪_h` at an auxiliary index, for any joint relative
generating set** whose base and whose original peripherals are auxiliary base
letters.  Every joint word avoiding `Γ_{E_i}` becomes an auxiliary word of the
same length and the same value. -/
theorem relBall_inr_subset_of_letters (J : RelGenSet G (Sum Λ I))
    (E : RelGenSet G I) (hbase : J.base ⊆ E.base)
    (hinl : ∀ lam : Λ, ((J.fam (Sum.inl lam) : Subgroup G) : Set G) ⊆ E.base)
    (hinr : ∀ i : I, J.fam (Sum.inr i) = E.fam i) (i : I) (n : ℕ) :
    J.relBall (Sum.inr i) n ⊆ E.relBall i n := by
  rintro h ⟨hmem, u, hlet, hval, hav, hlen⟩
  refine ⟨?_, u.map RelLetter.auxOfJoint, ?_, ?_, ?_, ?_⟩
  · rw [← hinr i]
    exact hmem
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' := hlet b hb
    cases b with
    | base _ => exact hbase hb'
    | comp s _ =>
        cases s with
        | inl lam => exact hinl lam hb'
        | inr j =>
            show _ ∈ E.fam j
            rw [← hinr j]
            exact hb'
  · rw [RelLetter.listVal_map_auxOfJoint]
    exact hval
  · exact avoidsFrom_map_auxOfJoint hinr i u 1 hav
  · rw [List.length_map]
    exact hlen

/-! ## The equal-alphabet form -/

/-- **Clause (b) at an auxiliary index**, for the labelled sum over the
original base. -/
theorem combined_relBall_inr_subset (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier) (i : I) (n : ℕ) :
    (combinedRelGenSet D E).relBall (Sum.inr i) n ⊆ E.relBall i n :=
  relBall_inr_subset_of_letters _ E
    (by
      rw [hbase]
      exact fun x hx => Set.mem_union_left _ hx)
    (fun lam => by
      rw [hbase]
      exact fun x hx => Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hx⟩))
    (fun _ => rfl) i n

/-- Clause (a) of `↪_h` depends on the alphabet only. -/
theorem exists_isHyperbolicSpace_of_alphabet_eq {P Q : Alphabet G} (h : P = Q)
    (hQ : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley Q)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley P) := by
  subst h
  exact hQ

/-- **Clause (a) for the labelled sum.**  The base equation makes the joint
alphabet equal to the auxiliary alphabet, so its Cayley graph is the auxiliary
one. -/
theorem combinedRelGenSet_hyperbolic (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (combinedRelGenSet D E).alphabet) :=
  exists_isHyperbolicSpace_of_alphabet_eq (combined_alphabet_eq D E hbase)
    hE.hyperbolic

/-- **The joint-family direction of hyperbolic-embeddedness transitivity, at
equal alphabets.**

`{H_λ} ↪_h (G, X)` and `{E_i} ↪_h (G, X ∪ ⋃_λ H_λ)` give
`{H_λ} ∪ {E_i} ↪_h (G, X)`. -/
def DGOProposition435Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      E.base = D.alphabet.carrier →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        (combinedRelGenSet D E).IsHyperbolicallyEmbedded

/-- **The exact residue of `DGOProposition435Statement`.**

The original peripheral metrics must stay locally finite once the auxiliary
subgroups are coned off.  Clause (a) and clause (b) at the auxiliary indices
are proved above from the base equation alone, so this is everything that is
missing. -/
def DGOProposition435LocalFinitenessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      E.base = D.alphabet.carrier →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ),
          ((combinedRelGenSet D E).relBall (Sum.inl lam) n).Finite

theorem dgoProposition435Statement_of_localFiniteness
    (h : DGOProposition435LocalFinitenessStatement.{u, v, w}) :
    DGOProposition435Statement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE
  refine ⟨combinedRelGenSet_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact h D E hbase hD hE lam n
  · exact (hE.locallyFinite i n).subset
      (combined_relBall_inr_subset D E hbase i n)

theorem dgoProposition435LocalFiniteness_of_statement
    (h : DGOProposition435Statement.{u, v, w}) :
    DGOProposition435LocalFinitenessStatement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE lam n
  exact (h D E hbase hD hE).locallyFinite (Sum.inl lam) n

/-- **The residue is exactly the gap.** -/
theorem dgoProposition435Statement_iff_localFiniteness :
    DGOProposition435Statement.{u, v, w} ↔
      DGOProposition435LocalFinitenessStatement.{u, v, w} :=
  ⟨dgoProposition435LocalFiniteness_of_statement,
    dgoProposition435Statement_of_localFiniteness⟩

/-! ## The nested-alphabet form -/

/-- **The proper part of a relative base**: the base letters that are not
already peripheral letters.

It is inversion-closed with no hypothesis, because the whole relative alphabet
is symmetric and the peripherals are subgroups; it is contained in the base;
and putting the peripherals back recovers the whole alphabet.  It meets no
`H_lam`, so `RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base` can
never bite on a joint family built over it. -/
def properBase (D : RelGenSet G Λ) : Set G :=
  D.base \ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))

theorem properBase_subset_base (D : RelGenSet G Λ) : properBase D ⊆ D.base :=
  fun _ hx => hx.1

theorem properBase_disjoint_fam (D : RelGenSet G Λ) (lam : Λ) {x : G}
    (hx : x ∈ properBase D) : x ∉ D.fam lam :=
  fun hmem => hx.2 (Set.mem_iUnion.mpr ⟨lam, hmem⟩)

theorem properBase_inv (D : RelGenSet G Λ) {x : G} (hx : x ∈ properBase D) :
    x⁻¹ ∈ properBase D := by
  refine ⟨?_, ?_⟩
  · have hxA : x ∈ D.alphabet.carrier := Set.mem_union_left _ hx.1
    rcases D.symmetricGenerating.inv_mem x hxA with hb | hf
    · exact hb
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
      have hlam' : x⁻¹ ∈ D.fam lam := hlam
      exact absurd (by simpa using inv_mem hlam') (properBase_disjoint_fam D lam hx)
  · intro hf
    obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
    have hlam' : x⁻¹ ∈ D.fam lam := hlam
    exact properBase_disjoint_fam D lam hx (by simpa using inv_mem hlam')

theorem base_subset_properBase_union (D : RelGenSet G Λ) :
    D.base ⊆ properBase D ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
  intro x hx
  by_cases hf : x ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
  · exact Or.inr hf
  · exact Or.inl ⟨hx, hf⟩

/-- **The joint relative generating set over the proper part of the original
base.**

Its base is inversion-closed, which both joint interfaces ask for and a bare
`RelGenSet` does not supply; it is contained in the original base, so the
original relative balls only shrink; and dropping the peripheral letters from
the base leaves the alphabet unchanged, because they come back as peripheral
letters of the sum. -/
def jointRelGenSet (D : RelGenSet G Λ) (E : RelGenSet G I) :
    RelGenSet G (Sum Λ I) where
  base := properBase D
  fam
    | Sum.inl lam => D.fam lam
    | Sum.inr i => E.fam i
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · rintro y (hy | hy)
      · exact Or.inl (properBase_inv D hy)
      · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
        cases s with
        | inl lam =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inl lam, (D.fam lam).inv_mem hs⟩)
        | inr i =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inr i, (E.fam i).inv_mem hs⟩)
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      apply Subgroup.closure_mono
      rintro y (hy | hy)
      · rcases base_subset_properBase_union D hy with hp | hf
        · exact Or.inl hp
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)

@[simp] theorem jointRelGenSet_base (D : RelGenSet G Λ) (E : RelGenSet G I) :
    (jointRelGenSet D E).base = properBase D := rfl

@[simp] theorem jointRelGenSet_fam_inl (D : RelGenSet G Λ) (E : RelGenSet G I)
    (lam : Λ) : (jointRelGenSet D E).fam (Sum.inl lam) = D.fam lam := rfl

@[simp] theorem jointRelGenSet_fam_inr (D : RelGenSet G Λ) (E : RelGenSet G I)
    (i : I) : (jointRelGenSet D E).fam (Sum.inr i) = E.fam i := rfl

/-- The joint base is closed under inversion. -/
theorem jointRelGenSet_base_inv (D : RelGenSet G Λ) (E : RelGenSet G I) :
    ∀ x ∈ (jointRelGenSet D E).base, x⁻¹ ∈ (jointRelGenSet D E).base :=
  fun _ hx => properBase_inv D hx

/-- The joint alphabet is the original relative alphabet together with the
auxiliary peripherals. -/
theorem jointRelGenSet_alphabet_carrier (D : RelGenSet G Λ)
    (E : RelGenSet G I) :
    (jointRelGenSet D E).alphabet.carrier =
      D.alphabet.carrier ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · exact Or.inl (Set.mem_union_left _ (properBase_subset_base D hy))
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
      cases s with
      | inl lam =>
          exact Or.inl (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hs⟩))
      | inr i => exact Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩)
  · rintro y (hy | hy)
    · rcases hy with hy | hy
      · rcases base_subset_properBase_union D hy with hp | hf
        · exact Or.inl hp
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩)

/-- **Clause (b) at an auxiliary index**, for the nested-alphabet form. -/
theorem jointRelGenSet_relBall_inr_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base) (i : I)
    (n : ℕ) : (jointRelGenSet D E).relBall (Sum.inr i) n ⊆ E.relBall i n :=
  relBall_inr_subset_of_letters _ E
    (fun _ hx => hbase (Set.mem_union_left _ (properBase_subset_base D hx)))
    (fun lam _ hx =>
      hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hx⟩)))
    (fun _ => rfl) i n

/-- **The joint-family direction at nested alphabets.**

This is the form the filling lane can use: the auxiliary family is coned off
over an alphabet that *contains* the original relative alphabet, which is all
`AuxiliaryPeripheralFamily.base_le` and `RelativeHullContinuationData` give. -/
def DGOProposition435InclusionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        (jointRelGenSet D E).IsHyperbolicallyEmbedded

/-- **First residue of the nested form: the joint Cayley graph is
hyperbolic.**

Under an inclusion the joint alphabet is a *subset* of the auxiliary one, and
hyperbolicity does not descend to a smaller generating set, so this no longer
follows from the hypotheses.  It is free when the two alphabets agree, by
`dgoProposition435JointHyperbolic_of_base_eq`. -/
def DGOProposition435JointHyperbolicStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∃ delta : ℝ,
          IsHyperbolicSpace delta (Cayley (jointRelGenSet D E).alphabet)

/-- **Second residue of the nested form: the original peripheral metrics stay
locally finite** once the auxiliary subgroups are coned off. -/
def DGOProposition435JointLocalFinitenessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ),
          ((jointRelGenSet D E).relBall (Sum.inl lam) n).Finite

/-- **The nested form splits into exactly its two residues.** -/
theorem dgoProposition435InclusionStatement_of_residues
    (hhyp : DGOProposition435JointHyperbolicStatement.{u, v, w})
    (hloc : DGOProposition435JointLocalFinitenessStatement.{u, v, w}) :
    DGOProposition435InclusionStatement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE
  refine ⟨hhyp D E hbase hD hE, ?_⟩
  rintro (lam | i) n
  · exact hloc D E hbase hD hE lam n
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSet_relBall_inr_subset D E hbase i n)

theorem dgoProposition435JointHyperbolic_of_inclusionStatement
    (h : DGOProposition435InclusionStatement.{u, v, w}) :
    DGOProposition435JointHyperbolicStatement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE
  exact (h D E hbase hD hE).hyperbolic

theorem dgoProposition435JointLocalFiniteness_of_inclusionStatement
    (h : DGOProposition435InclusionStatement.{u, v, w}) :
    DGOProposition435JointLocalFinitenessStatement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE lam n
  exact (h D E hbase hD hE).locallyFinite (Sum.inl lam) n

/-- **At equal alphabets the hyperbolicity residue is discharged**: the joint
alphabet is then the auxiliary alphabet. -/
theorem dgoProposition435JointHyperbolic_of_base_eq (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (jointRelGenSet D E).alphabet) := by
  have hcarrier : (jointRelGenSet D E).alphabet.carrier = E.alphabet.carrier := by
    rw [jointRelGenSet_alphabet_carrier D E, ← hbase]
    rfl
  exact exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq hcarrier) hE.hyperbolic

/-! ## Model tests -/

/-- **No original subgroups.**  The labelled sum is the auxiliary family, and
the statement reduces to its second hypothesis. -/
theorem isHyperbolicallyEmbedded_combinedRelGenSet_of_isEmpty_left
    [IsEmpty Λ] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    (combinedRelGenSet D E).IsHyperbolicallyEmbedded := by
  refine ⟨combinedRelGenSet_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact isEmptyElim lam
  · exact (hE.locallyFinite i n).subset
      (combined_relBall_inr_subset D E hbase i n)

/-- Avoidance of `Γ_{H_lam}` survives reading a joint word as an original
word. -/
theorem avoidsFrom_map_origOfJoint {F : Sum Λ I → Subgroup G}
    {Df : Λ → Subgroup G} (hF : ∀ mu : Λ, F (Sum.inl mu) = Df mu) (lam : Λ) :
    ∀ (u : List (RelLetter G (Sum Λ I))) (p : G),
      AvoidsFrom F (Sum.inl lam) u p →
        AvoidsFrom Df lam (u.map RelLetter.origOfJoint) p := by
  intro u
  induction u with
  | nil => intro _ _; exact trivial
  | cons a t ih =>
      intro p hp
      obtain ⟨hhead, htail⟩ := hp
      refine ⟨?_, ?_⟩
      · rintro ⟨hc, hmem⟩
        refine hhead ⟨RelLetter.isCompOf_of_origOfJoint hc, ?_⟩
        rw [hF lam]
        exact hmem
      · rw [RelLetter.origOfJoint_val]
        exact ih (p * a.val) htail

/-- **Clause (b) at an original index when there are no auxiliary
subgroups**, for any joint relative generating set whose base letters are
original base letters. -/
theorem relBall_inl_subset_of_letters_of_isEmpty [IsEmpty I]
    (J : RelGenSet G (Sum Λ I)) (D : RelGenSet G Λ) (hbase : J.base ⊆ D.base)
    (hinl : ∀ lam : Λ, J.fam (Sum.inl lam) = D.fam lam) (lam : Λ) (n : ℕ) :
    J.relBall (Sum.inl lam) n ⊆ D.relBall lam n := by
  rintro h ⟨hmem, u, hlet, hval, hav, hlen⟩
  refine ⟨?_, u.map RelLetter.origOfJoint, ?_, ?_, ?_, ?_⟩
  · rw [← hinl lam]
    exact hmem
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' := hlet b hb
    cases b with
    | base _ => exact hbase hb'
    | comp s _ =>
        cases s with
        | inl mu =>
            show _ ∈ D.fam mu
            rw [← hinl mu]
            exact hb'
        | inr i => exact isEmptyElim i
  · rw [RelLetter.listVal_map_origOfJoint]
    exact hval
  · exact avoidsFrom_map_origOfJoint hinl lam u 1 hav
  · rw [List.length_map]
    exact hlen

/-- **No auxiliary subgroups.**  The joint relative balls at an original index
are contained in the original ones. -/
theorem combined_relBall_inl_subset_of_isEmpty [IsEmpty I]
    (D : RelGenSet G Λ) (E : RelGenSet G I) (lam : Λ) (n : ℕ) :
    (combinedRelGenSet D E).relBall (Sum.inl lam) n ⊆ D.relBall lam n :=
  relBall_inl_subset_of_letters_of_isEmpty _ D (fun _ hx => hx)
    (fun _ => rfl) lam n

/-- **No auxiliary subgroups.**  The statement reduces to its first
hypothesis. -/
theorem isHyperbolicallyEmbedded_combinedRelGenSet_of_isEmpty_right
    [IsEmpty I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded) :
    (combinedRelGenSet D E).IsHyperbolicallyEmbedded := by
  refine ⟨combinedRelGenSet_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact (hD.locallyFinite lam n).subset
      (combined_relBall_inl_subset_of_isEmpty D E lam n)
  · exact isEmptyElim i

/-! ### The same two tests for the nested form -/

/-- **No original subgroups, nested form.**  The joint family is the auxiliary
family, and the statement reduces to its second hypothesis. -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_of_isEmpty_left
    [IsEmpty Λ] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSet D E).IsHyperbolicallyEmbedded := by
  refine ⟨dgoProposition435JointHyperbolic_of_base_eq D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact isEmptyElim lam
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSet_relBall_inr_subset D E hbase.symm.subset i n)

/-- **No auxiliary subgroups, nested form.**  The joint alphabet is then the
original one, so both clauses come from the first hypothesis alone.  No
hypothesis on the original base is needed, because the proper part of a base
is always contained in it. -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_of_isEmpty_right
    [IsEmpty I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hD : D.IsHyperbolicallyEmbedded) :
    (jointRelGenSet D E).IsHyperbolicallyEmbedded := by
  have hcarrier :
      (jointRelGenSet D E).alphabet.carrier = D.alphabet.carrier := by
    rw [jointRelGenSet_alphabet_carrier D E]
    refine Set.union_eq_self_of_subset_right ?_
    intro y hy
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp hy
    exact isEmptyElim i
  refine ⟨exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq hcarrier) hD.hyperbolic, ?_⟩
  rintro (lam | i) n
  · have hb : (jointRelGenSet D E).base ⊆ D.base := properBase_subset_base D
    exact (hD.locallyFinite lam n).subset
      (relBall_inl_subset_of_letters_of_isEmpty _ D hb (fun _ => rfl) lam n)
  · exact isEmptyElim i

/-! ## Why the joint base has to be the original one -/

/-- **The enlarged auxiliary base cannot be used as the joint base.**

The hypothesis `hsplit` says that every element of `H_lam` is a product of two
joint base letters, so all of `H_lam` lies in the joint relative ball of radius
`2` and local finiteness fails.  Over Hull's alphabet, which contains the
original relative alphabet, that is exactly what happens, which is why
`jointRelGenSet` keeps the original base and pays for it with the hyperbolicity
residue instead. -/
theorem not_isHyperbolicallyEmbedded_of_base_splits
    (J : RelGenSet G (Sum Λ I)) (lam : Λ)
    (hsplit : ∀ h ∈ J.fam (Sum.inl lam), ∃ x y : G,
      x ∈ J.base ∧ y ∈ J.base ∧ x * y = h)
    (hinf : (J.fam (Sum.inl lam) : Set G).Infinite) :
    ¬ J.IsHyperbolicallyEmbedded := by
  intro hJ
  refine hinf (Set.Finite.subset (hJ.locallyFinite (Sum.inl lam) 2) ?_)
  intro h hh
  obtain ⟨x, y, hx, hy, hxy⟩ := hsplit h hh
  refine ⟨hh, [RelLetter.base x, RelLetter.base y], ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hx
    · rw [List.eq_of_mem_singleton ha']
      exact hy
  · show x * (y * 1) = h
    rw [mul_one]
    exact hxy
  · exact ⟨fun hc => hc.1, fun hc => hc.1, trivial⟩
  · simp

end RelHyp
end GGT
end GroupApproximation
