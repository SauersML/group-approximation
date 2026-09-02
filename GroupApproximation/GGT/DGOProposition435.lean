import GroupApproximation.GGT.RelHypOsin24CombinedFamily
import GroupApproximation.GGT.DGOCorollary427PairLocal
import GroupApproximation.GGT.DGOCorollary427Full

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

## A third form, on the auxiliary alphabet

`DGOProposition435FullStatement` uses `jointRelGenSetFull`, whose base is the
whole auxiliary base minus the original peripherals.  Its joint alphabet is the
auxiliary alphabet *exactly* (`jointRelGenSetFull_alphabet_carrier`), so the two
peripheral structures live on one relative alphabet, which is what the relator
re-spelling of Hull's Lemma 4.4 needs, and clause (a) of `↪_h` is again free.
That form therefore has a single residue,
`DGOProposition435FullLocalFinitenessStatement`, which
`GGT/DGOProposition435FiniteLetters.lean` reduces further.  Its base is much
larger, so that residue is a strictly stronger demand than the one of the
nested form;
`jointBaseFull_subset_properBase_union` names the exact excess and
`not_isHyperbolicallyEmbedded_jointRelGenSetFull_of_base_splits` says when the
demand fails.

## The local-finiteness residue, reduced

`DGOProposition435FiniteAuxiliaryLettersStatement` says that for each original
index and radius, finitely many auxiliary letters suffice to spell the whole
joint relative ball.
`dgoProposition435JointLocalFiniteness_of_finiteAuxiliaryLetters` proves the
second residue from it, by turning those letters into finitely many extra base
letters and quoting the local-finiteness half of Corollary 4.27, which is
proved in `GGT/DGOCorollary427PairLocal.lean`.  So the residue is now a
statement about auxiliary letters alone, which is the shape Proposition 4.14
delivers.

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

/-! ## Reducing the local-finiteness residue to finitely many auxiliary
letters -/

/-- Adjoin a symmetric set of letters to a relative base. -/
def adjoinBase (D : RelGenSet G Λ) (F : Set G) (hFinv : ∀ x ∈ F, x⁻¹ ∈ F) :
    RelGenSet G Λ where
  base := D.base ∪ F
  fam := D.fam
  symmetricGenerating := by
    have hup : D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) ⊆
        (D.base ∪ F) ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
      rintro y (hy | hy)
      · exact Or.inl (Or.inl hy)
      · exact Or.inr hy
    refine ⟨?_, ?_⟩
    · rintro y ((hy | hy) | hy)
      · exact hup (D.symmetricGenerating.inv_mem y (Set.mem_union_left _ hy))
      · exact Or.inl (Or.inr (hFinv y hy))
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (D.fam lam).inv_mem hlam⟩)
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono hup

@[simp] theorem adjoinBase_base (D : RelGenSet G Λ) (F : Set G)
    (hFinv : ∀ x ∈ F, x⁻¹ ∈ F) :
    (adjoinBase D F hFinv).base = D.base ∪ F := rfl

@[simp] theorem adjoinBase_fam (D : RelGenSet G Λ) (F : Set G)
    (hFinv : ∀ x ∈ F, x⁻¹ ∈ F) : (adjoinBase D F hFinv).fam = D.fam := rfl

/-- **A finite enlargement of the base keeps the relative balls finite.**

This is the local-finiteness half of Dahmani--Guirardel--Osin's Corollary 4.27,
in the one-way direction, and it is proved in the repository. -/
theorem relBall_finite_adjoinBase (D : RelGenSet G Λ) (F : Set G)
    (hFinv : ∀ x ∈ F, x⁻¹ ∈ F) (hFfin : F.Finite)
    (hD : D.IsHyperbolicallyEmbedded) (lam : Λ) (n : ℕ) :
    ((adjoinBase D F hFinv).relBall lam n).Finite :=
  RelGenSet.localFiniteness_of_finite_base_diff D (adjoinBase D F hFinv) rfl
    (hFfin.subset (by
      rintro x ⟨hx, hxn⟩
      exact hx.resolve_left hxn))
    (fun mu m => hD.locallyFinite mu m) lam n

/-- **Joint balls at an original index, once the auxiliary letters are
confined.**

If every element of the joint ball is spelled by a joint word of the same
length whose auxiliary letters all lie in `F`, and `F` already sits in the
enlarged base `D'`, then reading each auxiliary letter as a base letter of `D'`
sends the joint ball into a relative ball of `D'`.  A base letter is never an
edge of `Γ_{H_lam}`, so the avoidance condition survives the reading.

The joint relative generating set is left arbitrary, so the lemma serves all
three joint forms of this file. -/
theorem relBall_inl_subset_of_auxLetters (J : RelGenSet G (Sum Λ I))
    (D' : RelGenSet G Λ) (hbase : J.base ⊆ D'.base)
    (hfam : ∀ mu : Λ, J.fam (Sum.inl mu) = D'.fam mu) (F : Set G)
    (hFbase : F ⊆ D'.base) (lam : Λ) (n : ℕ)
    (hwit : ∀ h ∈ J.relBall (Sum.inl lam) n,
      ∃ w : List (RelLetter G (Sum Λ I)),
        (∀ a ∈ w, J.IsLetter a) ∧
          RelLetter.listVal w = h ∧
            AvoidsFrom J.fam (Sum.inl lam) w 1 ∧
              w.length ≤ n ∧
                ∀ (i : I) (e : G), RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F) :
    J.relBall (Sum.inl lam) n ⊆ D'.relBall lam n := by
  intro h hh
  obtain ⟨w, hlet, hval, hav, hlen, haux⟩ := hwit h hh
  refine ⟨?_, w.map RelLetter.origOfJoint, ?_, ?_, ?_, ?_⟩
  · rw [← hfam lam]
    exact hh.1
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' := hlet b hb
    cases b with
    | base _ => exact hbase hb'
    | comp s e =>
        cases s with
        | inl mu =>
            show e ∈ D'.fam mu
            rw [← hfam mu]
            exact hb'
        | inr i => exact hFbase (haux i e hb)
  · rw [RelLetter.listVal_map_origOfJoint]
    exact hval
  · exact avoidsFrom_map_origOfJoint hfam lam w 1 hav
  · rw [List.length_map]
    exact hlen

/-- **The finite-auxiliary-letter statement.**

For each original index and each radius, finitely many auxiliary letters
suffice to spell the whole joint relative ball.  This is what
Dahmani--Guirardel--Osin's Proposition 4.14 delivers in their setting: in a
shortest joint word avoiding `Γ_{H_lam}` the auxiliary components are isolated
in the cycle closed by the `H_lam`-edge, so their relative lengths are bounded
linearly in the radius, and local finiteness of the auxiliary family turns that
bound into a finite set of letters. -/
def DGOProposition435FiniteAuxiliaryLettersStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ), ∃ F : Set G, F.Finite ∧
          ∀ h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) n,
            ∃ w : List (RelLetter G (Sum Lambda I)),
              (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
                RelLetter.listVal w = h ∧
                  AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
                    w.length ≤ n ∧
                      ∀ (i : I) (e : G),
                        RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F

/-- **The local-finiteness residue follows from the finite-auxiliary-letter
statement.**

Confining the auxiliary letters to a finite set turns them into finitely many
extra base letters, and a finite enlargement of the base keeps the relative
balls finite by the local-finiteness half of Corollary 4.27.  So the second
residue of the nested form is exactly a statement about auxiliary letters, with
no further use of the original family. -/
theorem dgoProposition435JointLocalFiniteness_of_finiteAuxiliaryLetters
    (h : DGOProposition435FiniteAuxiliaryLettersStatement.{u, v, w}) :
    DGOProposition435JointLocalFinitenessStatement.{u, v, w} := by
  intro G _ Lambda I D E hbase hD hE lam n
  obtain ⟨F, hFfin, hwit⟩ := h D E hbase hD hE lam n
  have hF'fin : (F ∪ F⁻¹).Finite := hFfin.union hFfin.inv
  have hF'inv : ∀ x ∈ F ∪ F⁻¹, x⁻¹ ∈ F ∪ F⁻¹ := by
    rintro x (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)
  refine (relBall_finite_adjoinBase D (F ∪ F⁻¹) hF'inv hF'fin hD lam n).subset ?_
  refine relBall_inl_subset_of_auxLetters _ (adjoinBase D (F ∪ F⁻¹) hF'inv)
    (fun _ hx => Or.inl (properBase_subset_base D hx)) (fun _ => rfl) F
    (fun _ hx => Or.inr (Or.inl hx)) lam n hwit

/-- **The joint Cayley graph is hyperbolic when some hyperbolically embedded
auxiliary family sits over an alphabet exceeding the original relative alphabet
by only finitely much.**

The joint alphabet is the original relative alphabet together with the
auxiliary peripherals, so it does not depend on the auxiliary *base* at all.
Any auxiliary relative generating set with the same family therefore serves,
and if its base exceeds the original relative alphabet finitely, its alphabet
differs from the joint one by a finite set.  Finite changes of a symmetric
generating set are bi-Lipschitz, and hyperbolicity crosses them.

This is what discharges the residue whenever the auxiliary family is available
before its relative generating set has been enlarged, and it tolerates the
finitely many filling targets adjoined on the way.  Its Hull-side consumer is
`HullSC.jointHyperbolic_of_matched_peripherals`. -/
theorem jointHyperbolic_of_finite_base_excess (D : RelGenSet G Λ)
    (E E' : RelGenSet G I) (hfam : E'.fam = E.fam)
    (hbase : D.alphabet.carrier ⊆ E'.base)
    (hfin : (E'.base \ D.alphabet.carrier).Finite)
    (hE' : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley E'.alphabet)) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (jointRelGenSet D E).alphabet) := by
  have hcarrier : (jointRelGenSet D E).alphabet.carrier =
      D.alphabet.carrier ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G)) :=
    jointRelGenSet_alphabet_carrier D E
  have hEcarrier : E'.alphabet.carrier =
      E'.base ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G)) := by
    show E'.base ∪ (⋃ i : I, ((E'.fam i : Subgroup G) : Set G)) = _
    rw [hfam]
  have hjointSub :
      ((jointRelGenSet D E).alphabet.carrier \ E'.alphabet.carrier).Finite := by
    refine Set.finite_empty.subset ?_
    rw [hcarrier, hEcarrier]
    rintro x ⟨hx | hx, hxn⟩
    · exact absurd (Or.inl (hbase hx)) hxn
    · exact absurd (Or.inr hx) hxn
  have hauxSub :
      (E'.alphabet.carrier \ (jointRelGenSet D E).alphabet.carrier).Finite := by
    refine hfin.subset ?_
    rw [hcarrier, hEcarrier]
    rintro x ⟨hx | hx, hxn⟩
    · exact ⟨hx, fun hxD => hxn (Or.inl hxD)⟩
    · exact absurd (Or.inr hx) hxn
  obtain ⟨K, hK, hcomp⟩ := FiniteChange.exists_bilipschitz_of_finite_diff
    E'.alphabet.symmetricGenerating
    (jointRelGenSet D E).alphabet.symmetricGenerating hauxSub hjointSub
  obtain ⟨d, hd⟩ := hE'
  exact FiniteChange.exists_hyperbolic_of_bilipschitz E'.alphabet
    (jointRelGenSet D E).alphabet hK (fun x y => (hcomp x y).1)
    (fun x y => (hcomp x y).2) hd

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

/-- **Radius zero.**  The only element of the ball is the identity, spelled by
the empty word, so no auxiliary letter is needed. -/
theorem finiteAuxiliaryLetters_zero (D : RelGenSet G Λ) (E : RelGenSet G I)
    (lam : Λ) : ∃ F : Set G, F.Finite ∧
      ∀ h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) 0,
        ∃ w : List (RelLetter G (Sum Λ I)),
          (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
            RelLetter.listVal w = h ∧
              AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
                w.length ≤ 0 ∧
                  ∀ (i : I) (e : G),
                    RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F := by
  refine ⟨∅, Set.finite_empty, ?_⟩
  intro h hh
  rw [RelGenSet.relBall_zero] at hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact ⟨[], by simp, RelLetter.listVal_nil, trivial, by simp, by simp⟩

/-- **No auxiliary subgroups.**  The empty set of auxiliary letters works at
every radius. -/
theorem finiteAuxiliaryLetters_of_isEmpty [IsEmpty I] (D : RelGenSet G Λ)
    (E : RelGenSet G I) (lam : Λ) (n : ℕ) : ∃ F : Set G, F.Finite ∧
      ∀ h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) n,
        ∃ w : List (RelLetter G (Sum Λ I)),
          (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
            RelLetter.listVal w = h ∧
              AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
                w.length ≤ n ∧
                  ∀ (i : I) (e : G),
                    RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F := by
  refine ⟨∅, Set.finite_empty, ?_⟩
  rintro h ⟨-, w, hlet, hval, hav, hlen⟩
  exact ⟨w, hlet, hval, hav, hlen, fun i _ _ => isEmptyElim i⟩

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

/-! ## The joint family with adjoined base letters -/

/-- The symmetric closure of a set of letters. -/
def symmClosure (T : Set G) : Set G := T ∪ T⁻¹

theorem subset_symmClosure (T : Set G) : T ⊆ symmClosure T :=
  fun _ hx => Or.inl hx

theorem symmClosure_inv {T : Set G} {x : G} (hx : x ∈ symmClosure T) :
    x⁻¹ ∈ symmClosure T := by
  rcases hx with hx | hx
  · exact Or.inr (by simpa using hx)
  · exact Or.inl (by simpa using hx)

theorem symmClosure_finite {T : Set G} (hT : T.Finite) :
    (symmClosure T).Finite := hT.union hT.inv

theorem inv_mem_symmClosure {T : Set G} {x : G} (hx : x ∈ T) :
    x⁻¹ ∈ symmClosure T := symmClosure_inv (subset_symmClosure T hx)

/-- **The joint base with extra letters adjoined.**

The proper part of the original base together with the symmetric closure of
`T`, minus the original peripherals.  Removing the peripherals keeps the
hygiene invariant, and taking the symmetric closure makes the base
inversion-closed with no hypothesis on `T`. -/
def jointBaseAdjoin (D : RelGenSet G Λ) (T : Set G) : Set G :=
  properBase D ∪
    (symmClosure T \ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)))

theorem jointBaseAdjoin_inv (D : RelGenSet G Λ) (T : Set G) {x : G}
    (hx : x ∈ jointBaseAdjoin D T) : x⁻¹ ∈ jointBaseAdjoin D T := by
  rcases hx with hx | ⟨hxT, hxn⟩
  · exact Or.inl (properBase_inv D hx)
  · refine Or.inr ⟨symmClosure_inv hxT, ?_⟩
    intro hf
    obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
    have hlam' : x⁻¹ ∈ D.fam lam := hlam
    exact hxn (Set.mem_iUnion.mpr ⟨lam, by simpa using inv_mem hlam'⟩)

theorem jointBaseAdjoin_subset (D : RelGenSet G Λ) (T : Set G) :
    jointBaseAdjoin D T ⊆ D.base ∪ symmClosure T := by
  rintro x (hx | ⟨hxT, -⟩)
  · exact Or.inl (properBase_subset_base D hx)
  · exact Or.inr hxT

theorem base_subset_jointBaseAdjoin_union (D : RelGenSet G Λ) (T : Set G) :
    D.base ⊆
      jointBaseAdjoin D T ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
  intro x hx
  rcases base_subset_properBase_union D hx with hp | hf
  · exact Or.inl (Or.inl hp)
  · exact Or.inr hf

/-- **The joint relative generating set with extra base letters.**

`jointRelGenSet` is the case `T = ∅`, up to the union with the empty set. -/
def jointRelGenSetAdjoin (D : RelGenSet G Λ) (E : RelGenSet G I) (T : Set G) :
    RelGenSet G (Sum Λ I) where
  base := jointBaseAdjoin D T
  fam
    | Sum.inl lam => D.fam lam
    | Sum.inr i => E.fam i
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · rintro y (hy | hy)
      · exact Or.inl (jointBaseAdjoin_inv D T hy)
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
      · rcases base_subset_jointBaseAdjoin_union D T hy with hp | hf
        · exact Or.inl hp
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)

@[simp] theorem jointRelGenSetAdjoin_base (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) :
    (jointRelGenSetAdjoin D E T).base = jointBaseAdjoin D T := rfl

@[simp] theorem jointRelGenSetAdjoin_fam_inl (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (lam : Λ) :
    (jointRelGenSetAdjoin D E T).fam (Sum.inl lam) = D.fam lam := rfl

@[simp] theorem jointRelGenSetAdjoin_fam_inr (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (i : I) :
    (jointRelGenSetAdjoin D E T).fam (Sum.inr i) = E.fam i := rfl

/-- **(i)** The joint base is an auxiliary base. -/
theorem jointRelGenSetAdjoin_base_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (hbase : D.alphabet.carrier ⊆ E.base)
    (hT : symmClosure T ⊆ E.base) :
    (jointRelGenSetAdjoin D E T).base ⊆ E.base := by
  intro x hx
  rcases jointBaseAdjoin_subset D T hx with hb | hs
  · exact hbase (Set.mem_union_left _ hb)
  · exact hT hs

/-- The joint base is closed under inversion, with no hypothesis. -/
theorem jointRelGenSetAdjoin_base_inv (D : RelGenSet G Λ) (E : RelGenSet G I)
    (T : Set G) : ∀ x ∈ (jointRelGenSetAdjoin D E T).base,
      x⁻¹ ∈ (jointRelGenSetAdjoin D E T).base :=
  fun _ hx => jointBaseAdjoin_inv D T hx

/-- **(iii)** An adjoined letter outside every original peripheral is a joint
base letter, and so is its inverse. -/
theorem jointRelGenSetAdjoin_inv_mem_base (D : RelGenSet G Λ)
    (E : RelGenSet G I) {T : Set G} {t : G} (ht : t ∈ T)
    (htn : ∀ lam : Λ, t⁻¹ ∉ D.fam lam) :
    t⁻¹ ∈ (jointRelGenSetAdjoin D E T).base := by
  refine Or.inr ⟨inv_mem_symmClosure ht, ?_⟩
  intro hf
  obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
  exact htn lam hlam

/-- The joint alphabet is the original relative alphabet, the adjoined
letters, and the auxiliary peripherals. -/
theorem jointRelGenSetAdjoin_alphabet_carrier (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) :
    (jointRelGenSetAdjoin D E T).alphabet.carrier =
      D.alphabet.carrier ∪ symmClosure T ∪
        (⋃ i : I, ((E.fam i : Subgroup G) : Set G)) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · rcases jointBaseAdjoin_subset D T hy with hb | hs
      · exact Or.inl (Or.inl (Set.mem_union_left _ hb))
      · exact Or.inl (Or.inr hs)
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
      cases s with
      | inl lam =>
          exact Or.inl (Or.inl (Set.mem_union_right _
            (Set.mem_iUnion.mpr ⟨lam, hs⟩)))
      | inr i => exact Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩)
  · rintro y ((hy | hy) | hy)
    · rcases hy with hy | hy
      · rcases base_subset_jointBaseAdjoin_union D T hy with hp | hf
        · exact Or.inl hp
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
    · by_cases hH : y ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hH
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · exact Or.inl (Or.inr ⟨hy, hH⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩)

/-- **(ii)** The joint alphabet is the auxiliary alphabet exactly when the
auxiliary base is covered by the original relative alphabet, the adjoined
letters, and the auxiliary peripherals. -/
theorem jointRelGenSetAdjoin_alphabet_carrier_eq (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (hbase : D.alphabet.carrier ⊆ E.base)
    (hT : symmClosure T ⊆ E.base)
    (hcover : E.base ⊆ D.alphabet.carrier ∪ symmClosure T ∪
      (⋃ i : I, ((E.fam i : Subgroup G) : Set G))) :
    (jointRelGenSetAdjoin D E T).alphabet.carrier = E.alphabet.carrier := by
  rw [jointRelGenSetAdjoin_alphabet_carrier D E T]
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ((hy | hy) | hy)
    · exact Or.inl (hbase hy)
    · exact Or.inl (hT hy)
    · exact Or.inr hy
  · rintro y (hy | hy)
    · exact hcover hy
    · exact Or.inr hy

/-- Clause (a) for the adjoined form, under the covering condition. -/
theorem jointRelGenSetAdjoin_hyperbolic (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (hbase : D.alphabet.carrier ⊆ E.base)
    (hT : symmClosure T ⊆ E.base)
    (hcover : E.base ⊆ D.alphabet.carrier ∪ symmClosure T ∪
      (⋃ i : I, ((E.fam i : Subgroup G) : Set G)))
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (jointRelGenSetAdjoin D E T).alphabet) :=
  exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq
      (jointRelGenSetAdjoin_alphabet_carrier_eq D E T hbase hT hcover))
    hE.hyperbolic

/-- Clause (b) at an auxiliary index, for the adjoined form. -/
theorem jointRelGenSetAdjoin_relBall_inr_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (hbase : D.alphabet.carrier ⊆ E.base)
    (hT : symmClosure T ⊆ E.base) (i : I) (n : ℕ) :
    (jointRelGenSetAdjoin D E T).relBall (Sum.inr i) n ⊆ E.relBall i n :=
  relBall_inr_subset_of_letters _ E
    (jointRelGenSetAdjoin_base_subset D E T hbase hT)
    (fun lam _ hx =>
      hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hx⟩)))
    (fun _ => rfl) i n

/-- **The joint alphabet is contained in the auxiliary alphabet.**

Enough for an index relabelling of joint words into auxiliary words; the
reverse inclusion is what fails after the relative generating set is
enlarged. -/
theorem jointRelGenSetAdjoin_alphabet_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) (T : Set G) (hbase : D.alphabet.carrier ⊆ E.base)
    (hT : symmClosure T ⊆ E.base) :
    (jointRelGenSetAdjoin D E T).alphabet.carrier ⊆ E.alphabet.carrier := by
  rw [jointRelGenSetAdjoin_alphabet_carrier D E T]
  rintro y ((hy | hy) | hy)
  · exact Or.inl (hbase hy)
  · exact Or.inl (hT hy)
  · exact Or.inr hy

/-- **The joint base is finite** when the original relative base is and only
finitely many letters are adjoined.  This is what makes the quotient of the
joint family a relatively hyperbolic structure, whose base must be finite. -/
theorem jointRelGenSetAdjoin_base_finite (D : RelGenSet G Λ)
    (E : RelGenSet G I) {T : Set G} (hDfin : D.base.Finite) (hTfin : T.Finite) :
    ((jointRelGenSetAdjoin D E T).base).Finite :=
  (hDfin.union (symmClosure_finite hTfin)).subset (jointBaseAdjoin_subset D T)

/-- **The adjoined form keeps the reducible residue.**

Its base exceeds the proper part of the original base by a finite set, so the
local-finiteness residue is still absorbed by
`relBall_finite_adjoinBase` once the auxiliary letters are confined.  This is
what distinguishes it from the auxiliary-alphabet form, whose base excess is
the whole enlargement of the relative generating set. -/
theorem jointRelGenSetAdjoin_relBall_inl_finite (D : RelGenSet G Λ)
    (E : RelGenSet G I) {T : Set G} (hTfin : T.Finite)
    (hD : D.IsHyperbolicallyEmbedded) {F : Set G} (hFfin : F.Finite)
    (lam : Λ) (n : ℕ)
    (hwit : ∀ h ∈ (jointRelGenSetAdjoin D E T).relBall (Sum.inl lam) n,
      ∃ w : List (RelLetter G (Sum Λ I)),
        (∀ a ∈ w, (jointRelGenSetAdjoin D E T).IsLetter a) ∧
          RelLetter.listVal w = h ∧
            AvoidsFrom (jointRelGenSetAdjoin D E T).fam (Sum.inl lam) w 1 ∧
              w.length ≤ n ∧
                ∀ (i : I) (e : G), RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F) :
    ((jointRelGenSetAdjoin D E T).relBall (Sum.inl lam) n).Finite := by
  have hUfin : (symmClosure T ∪ symmClosure F).Finite :=
    (symmClosure_finite hTfin).union (symmClosure_finite hFfin)
  have hUinv : ∀ x ∈ symmClosure T ∪ symmClosure F,
      x⁻¹ ∈ symmClosure T ∪ symmClosure F := by
    rintro x (hx | hx)
    · exact Or.inl (symmClosure_inv hx)
    · exact Or.inr (symmClosure_inv hx)
  refine (relBall_finite_adjoinBase D (symmClosure T ∪ symmClosure F) hUinv
    hUfin hD lam n).subset ?_
  refine relBall_inl_subset_of_auxLetters _
    (adjoinBase D (symmClosure T ∪ symmClosure F) hUinv) ?_ (fun _ => rfl) F ?_
    lam n hwit
  · intro x hx
    rcases jointBaseAdjoin_subset D T hx with hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inl hs)
  · exact fun x hx => Or.inr (Or.inr (subset_symmClosure F hx))

/-! ## The joint family on the auxiliary alphabet -/

/-- **The joint base on the auxiliary alphabet**: every auxiliary base letter
that is not an original peripheral letter.

Taking the whole auxiliary base rather than the original one is forced by the
relator re-spelling, which needs the two peripheral structures to live on *one*
relative alphabet.  It is the largest base compatible with the hygiene
invariant, since a peripheral letter in the base would refute embeddedness
outright. -/
def jointBaseFull (D : RelGenSet G Λ) (E : RelGenSet G I) : Set G :=
  E.base \ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))

/-- **The joint relative generating set on the auxiliary alphabet.**

Unlike `jointRelGenSet`, this one has the auxiliary alphabet exactly
(`jointRelGenSetFull_alphabet_carrier`), so clause (a) of `↪_h` is free and the
form below has a single residue.  The price is that its base is as large as the
auxiliary base, which makes clause (b) at an original index a strictly stronger
demand; `not_isHyperbolicallyEmbedded_jointRelGenSetFull_of_base_splits` says
exactly when that demand fails. -/
def jointRelGenSetFull (D : RelGenSet G Λ) (E : RelGenSet G I) :
    RelGenSet G (Sum Λ I) where
  base := jointBaseFull D E
  fam
    | Sum.inl lam => D.fam lam
    | Sum.inr i => E.fam i
  symmetricGenerating := by
    classical
    refine ⟨?_, ?_⟩
    · rintro y (hy | hy)
      · have hyA : y ∈ E.alphabet.carrier := Set.mem_union_left _ hy.1
        rcases E.symmetricGenerating.inv_mem y hyA with hb | hf
        · by_cases hH :
              y⁻¹ ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
          · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hH
            exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
          · exact Or.inl ⟨hb, hH⟩
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩)
      · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
        cases s with
        | inl lam =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inl lam, (D.fam lam).inv_mem hs⟩)
        | inr i =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inr i, (E.fam i).inv_mem hs⟩)
    · refine eq_top_iff.mpr ?_
      rw [← E.symmetricGenerating.closure_eq]
      apply Subgroup.closure_mono
      rintro y (hy | hy)
      · by_cases hH : y ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hH
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
        · exact Or.inl ⟨hy, hH⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩)

@[simp] theorem jointRelGenSetFull_base (D : RelGenSet G Λ)
    (E : RelGenSet G I) :
    (jointRelGenSetFull D E).base = jointBaseFull D E := rfl

@[simp] theorem jointRelGenSetFull_fam_inl (D : RelGenSet G Λ)
    (E : RelGenSet G I) (lam : Λ) :
    (jointRelGenSetFull D E).fam (Sum.inl lam) = D.fam lam := rfl

@[simp] theorem jointRelGenSetFull_fam_inr (D : RelGenSet G Λ)
    (E : RelGenSet G I) (i : I) :
    (jointRelGenSetFull D E).fam (Sum.inr i) = E.fam i := rfl

/-- **The joint base is an auxiliary base.**  This is the first thing the
relator re-spelling asks for. -/
theorem jointRelGenSetFull_base_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) : (jointRelGenSetFull D E).base ⊆ E.base := by
  rintro x ⟨hx, -⟩
  exact hx

/-- **The joint base is closed under inversion** as soon as the auxiliary base
is, which the filling lane records. -/
theorem jointRelGenSetFull_base_inv (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) :
    ∀ x ∈ (jointRelGenSetFull D E).base,
      x⁻¹ ∈ (jointRelGenSetFull D E).base := by
  rintro x ⟨hx, hxn⟩
  refine ⟨hEinv x hx, ?_⟩
  intro hf
  obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
  have hlam' : x⁻¹ ∈ D.fam lam := hlam
  exact hxn (Set.mem_iUnion.mpr ⟨lam, by simpa using inv_mem hlam'⟩)

/-- **An auxiliary base letter outside every original peripheral is a joint
base letter.**  This is what puts the adjoined filling target into the joint
base, the third thing the relator re-spelling asks for. -/
theorem jointRelGenSetFull_mem_base (D : RelGenSet G Λ) (E : RelGenSet G I)
    {t : G} (ht : t ∈ E.base) (htn : ∀ lam : Λ, t ∉ D.fam lam) :
    t ∈ (jointRelGenSetFull D E).base := by
  refine ⟨ht, ?_⟩
  intro hf
  obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
  exact htn lam hlam

/-- **The joint alphabet is the auxiliary alphabet.**

Two peripheral structures on one relative alphabet, which is the second thing
the relator re-spelling asks for, and the reason clause (a) of `↪_h` costs
nothing in this form. -/
theorem jointRelGenSetFull_alphabet_carrier (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base) :
    (jointRelGenSetFull D E).alphabet.carrier = E.alphabet.carrier := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · exact Or.inl hy.1
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
      cases s with
      | inl lam =>
          exact Or.inl (hbase (Set.mem_union_right _
            (Set.mem_iUnion.mpr ⟨lam, hs⟩)))
      | inr i => exact Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩)
  · rintro y (hy | hy)
    · by_cases hH : y ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hH
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
      · exact Or.inl ⟨hy, hH⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩)

/-- **Clause (a) is free in this form.** -/
theorem jointRelGenSetFull_hyperbolic (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (jointRelGenSetFull D E).alphabet) :=
  exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq
      (jointRelGenSetFull_alphabet_carrier D E hbase)) hE.hyperbolic

/-- **Clause (b) at an auxiliary index**, in this form. -/
theorem jointRelGenSetFull_relBall_inr_subset (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base) (i : I)
    (n : ℕ) : (jointRelGenSetFull D E).relBall (Sum.inr i) n ⊆ E.relBall i n :=
  relBall_inr_subset_of_letters _ E (jointRelGenSetFull_base_subset D E)
    (fun lam _ hx =>
      hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hx⟩)))
    (fun _ => rfl) i n

/-- **The joint direction on the auxiliary alphabet.**

The form the relator re-spelling consumes.  Its joint family lives on the
auxiliary relative alphabet, so it is a second peripheral structure on the same
alphabet.  Of the three forms in this file it is the strongest, and it is the
only one whose clause (a) is free without a matched alphabet.

The auxiliary index type is finite and the auxiliary base is inversion-closed;
both hold in the filling lane, where the index type is
`HullSC.AuxiliaryPeripheralIndex k` and the symmetry is
`HullSC.AuxiliaryPeripheralFamily.base_inv`, and both are needed to reduce the
residue. -/
def DGOProposition435FullStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w} [Finite I]
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      (∀ x ∈ E.base, x⁻¹ ∈ E.base) →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        (jointRelGenSetFull D E).IsHyperbolicallyEmbedded

/-- **The single residue of the auxiliary-alphabet form.** -/
def DGOProposition435FullLocalFinitenessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w} [Finite I]
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      (∀ x ∈ E.base, x⁻¹ ∈ E.base) →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ),
          ((jointRelGenSetFull D E).relBall (Sum.inl lam) n).Finite

theorem dgoProposition435FullStatement_of_localFiniteness
    (h : DGOProposition435FullLocalFinitenessStatement.{u, v, w}) :
    DGOProposition435FullStatement.{u, v, w} := by
  intro G _ Lambda I _ D E hbase hEinv hD hE
  refine ⟨jointRelGenSetFull_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact h D E hbase hEinv hD hE lam n
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSetFull_relBall_inr_subset D E hbase i n)

theorem dgoProposition435FullLocalFiniteness_of_statement
    (h : DGOProposition435FullStatement.{u, v, w}) :
    DGOProposition435FullLocalFinitenessStatement.{u, v, w} := by
  intro G _ Lambda I _ D E hbase hEinv hD hE lam n
  exact (h D E hbase hEinv hD hE).locallyFinite (Sum.inl lam) n

/-- **The residue is exactly the gap**, in the auxiliary-alphabet form. -/
theorem dgoProposition435FullStatement_iff_localFiniteness :
    DGOProposition435FullStatement.{u, v, w} ↔
      DGOProposition435FullLocalFinitenessStatement.{u, v, w} :=
  ⟨dgoProposition435FullLocalFiniteness_of_statement,
    dgoProposition435FullStatement_of_localFiniteness⟩

/-- **The exact excess of the auxiliary-alphabet joint base over the original
one.**

The two joint bases differ by `E.base \ D.alphabet.carrier`, the letters the
auxiliary relative generating set adds to the original relative alphabet.  If
that difference is finite, the auxiliary-alphabet residue is no stronger than
the original-base one, by `relBall_finite_adjoinBase`; if it is infinite, as it
is after an enlargement of the relative generating set, the two residues really
do differ. -/
theorem jointBaseFull_subset_properBase_union (D : RelGenSet G Λ)
    (E : RelGenSet G I) :
    jointBaseFull D E ⊆ properBase D ∪ (E.base \ D.alphabet.carrier) := by
  classical
  rintro x ⟨hx, hxn⟩
  by_cases hD : x ∈ D.alphabet.carrier
  · refine Or.inl ⟨?_, hxn⟩
    rcases hD with hb | hf
    · exact hb
    · exact absurd hf hxn
  · exact Or.inr ⟨hx, hD⟩

/-- **When the auxiliary-alphabet form fails.**

If every element of an infinite original peripheral is a product of two joint
base letters, the original relative metric collapses to radius `2`.  Since the
joint base is the whole auxiliary base minus the original peripherals, this is
a real risk once the auxiliary base is much larger than the original relative
alphabet, and it is the price of putting the two structures on one alphabet. -/
theorem not_isHyperbolicallyEmbedded_jointRelGenSetFull_of_base_splits
    (D : RelGenSet G Λ) (E : RelGenSet G I) (lam : Λ)
    (hsplit : ∀ h ∈ D.fam lam, ∃ x y : G,
      x ∈ (jointRelGenSetFull D E).base ∧
        y ∈ (jointRelGenSetFull D E).base ∧ x * y = h)
    (hinf : (D.fam lam : Set G).Infinite) :
    ¬ (jointRelGenSetFull D E).IsHyperbolicallyEmbedded :=
  not_isHyperbolicallyEmbedded_of_base_splits _ lam hsplit hinf

/-- At a matched alphabet the two joint bases agree. -/
theorem jointBaseFull_eq_properBase (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier) :
    jointBaseFull D E = properBase D := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hx, hxn⟩
    rw [hbase] at hx
    rcases hx with hx | hx
    · exact ⟨hx, hxn⟩
    · exact absurd hx hxn
  · rintro x ⟨hx, hxn⟩
    refine ⟨?_, hxn⟩
    rw [hbase]
    exact Set.mem_union_left _ hx

/-- **No original subgroups, auxiliary-alphabet form.** -/
theorem isHyperbolicallyEmbedded_jointRelGenSetFull_of_isEmpty_left
    [IsEmpty Λ] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSetFull D E).IsHyperbolicallyEmbedded := by
  refine ⟨jointRelGenSetFull_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact isEmptyElim lam
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSetFull_relBall_inr_subset D E hbase i n)

/-- **No auxiliary subgroups, auxiliary-alphabet form, at a matched
alphabet.**  The joint base is then the proper part of the original base and
the statement reduces to its first hypothesis. -/
theorem isHyperbolicallyEmbedded_jointRelGenSetFull_of_isEmpty_right
    [IsEmpty I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hD : D.IsHyperbolicallyEmbedded) :
    (jointRelGenSetFull D E).IsHyperbolicallyEmbedded := by
  have hb : (jointRelGenSetFull D E).base ⊆ D.base := by
    rw [jointRelGenSetFull_base, jointBaseFull_eq_properBase D E hbase]
    exact properBase_subset_base D
  have hcarrier :
      (jointRelGenSetFull D E).alphabet.carrier = D.alphabet.carrier := by
    rw [jointRelGenSetFull_alphabet_carrier D E hbase.symm.subset, ← hbase]
    show E.base ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G)) = E.base
    refine Set.union_eq_self_of_subset_right ?_
    intro y hy
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp hy
    exact isEmptyElim i
  refine ⟨exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq hcarrier) hD.hyperbolic, ?_⟩
  rintro (lam | i) n
  · exact (hD.locallyFinite lam n).subset
      (relBall_inl_subset_of_letters_of_isEmpty _ D hb (fun _ => rfl) lam n)
  · exact isEmptyElim i

end RelHyp
end GGT
end GroupApproximation
