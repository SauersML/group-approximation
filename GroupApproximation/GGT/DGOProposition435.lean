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
presentations with linear relative isoperimetric functions are chosen for
`G` over `(X, ℋ)` and for each `H_λ` over `(Y_λ, 𝒦_λ)`, the `S_λ`-cells of a
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
original relative generating set.  In the notation of this file, with
`D` the original relative generating set and `E` the auxiliary one:

* `D.IsHyperbolicallyEmbedded` is `{H_λ} ↪_h (G, X)`;
* `E.base = D.alphabet.carrier` together with `E.IsHyperbolicallyEmbedded` is
  `{E_i} ↪_h (G, X ∪ ⋃_λ H_λ)`, the second coning-off performed over the
  first relative alphabet;
* the conclusion wanted is `{H_λ} ∪ {E_i} ↪_h (G, X)`, that is,
  `(combinedRelGenSet D E).IsHyperbolicallyEmbedded`.

This is `DGOProposition435Statement` below.  It is **not** printed in
Dahmani--Guirardel--Osin.  The two printed facts nearest to it are

* Remark 4.26, which gives only the forward implication
  `{H_λ}_{λ∈Λ} ↪_h (G, X)` ⟹ `H_λ ↪_h (G, X ∪ ⋃_{μ≠λ} H_μ)`, and states
  explicitly that its converse fails (`H₁ = G = F(x,y)`, `H₂ = ⟨x⟩`); and
* Corollary 4.27, which moves `↪_h` between two relative generating sets whose
  symmetric difference is finite (`GGT.DGOCorollary427`).

Remark 4.26's counterexample does not refute `DGOProposition435Statement`: in
it, `{H₂} ↪_h (G, X ∪ H₁)` fails, because `X ∪ H₁ = G` makes the relative
metric of `H₂` bounded.  The base equation `E.base = D.alphabet.carrier` is
exactly the hypothesis that rules this out.

## What is proved here and what is left

Two of the three clauses of `↪_h` for the labelled sum are proved outright:

* `combinedRelGenSet_hyperbolic` — clause (a).  The base equation makes the
  joint alphabet *equal* to the auxiliary alphabet
  (`RelHyp.combined_alphabet_eq`), so hyperbolicity is reused, not
  transported.
* `combined_relBall_inr_subset` — clause (b) at an auxiliary index.  Every
  joint word avoiding `Γ_{E_i}` becomes an auxiliary word of the same length
  and the same value by reading each original peripheral letter as a *base*
  letter, which the base equation licenses.  So the joint relative balls at
  `Sum.inr i` are contained in the auxiliary ones.

What is left is clause (b) at an *original* index: the original peripheral
metrics must stay locally finite after the auxiliary subgroups are coned off.
That single residue is `DGOProposition435LocalFinitenessStatement`, and
`dgoProposition435Statement_iff_localFiniteness` shows it is exactly the gap.
It is where Proposition 4.35's diagram surgery would go: an auxiliary letter
is a single edge of unbounded relative length, and nothing geometric bounds it
without Theorem 4.24.

## The base equation is not decoration

`combined_relBall_inl_subset_of_isEmpty` and
`isHyperbolicallyEmbedded_combinedRelGenSet_of_isEmpty_left` are the two
degenerate model tests: with no auxiliary subgroups the statement reduces to
its first hypothesis, and with no original subgroups to its second.

`not_isHyperbolicallyEmbedded_of_base_splits` records the failure mode when
the base equation is weakened to `D.alphabet.carrier ⊆ E.base`, which is the
inclusion the filling lane actually carries: as soon as every original
peripheral element is a product of two auxiliary base letters that are not
peripheral, the original relative metric collapses to radius `2` and local
finiteness fails.  Enlarging the base is therefore not free, and Corollary
4.27 repairs only finite enlargements.
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
base is the whole original relative alphabet. -/
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
      | inr j => exact congrArg Sum.inr h

/-- Only an original peripheral letter can be a `lam`-component after reading
a joint letter as an original letter. -/
theorem isCompOf_of_origOfJoint {a : RelLetter G (Sum Λ I)} {lam : Λ}
    (h : (origOfJoint a).IsCompOf lam) : a.IsCompOf (Sum.inl lam) := by
  cases a with
  | base _ => exact h.elim
  | comp s _ =>
      cases s with
      | inl mu => exact congrArg Sum.inl h
      | inr _ => exact h.elim

end RelLetter

namespace RelHyp

variable {G : Type u} [Group G] {Λ : Type v} {I : Type w}

/-! ## Reading joint words as auxiliary words -/

/-- A joint letter is an auxiliary letter once the auxiliary base is the whole
original relative alphabet: base letters are already auxiliary base letters,
original peripheral letters are auxiliary base letters because the original
family lies in the original relative alphabet, and auxiliary peripheral letters
are unchanged. -/
theorem isLetter_auxOfJoint (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier) {a : RelLetter G (Sum Λ I)}
    (ha : (combinedRelGenSet D E).IsLetter a) :
    E.IsLetter (RelLetter.auxOfJoint a) := by
  cases a with
  | base x =>
      show x ∈ E.base
      rw [hbase]
      exact Set.mem_union_left _ ha
  | comp s h =>
      cases s with
      | inl lam =>
          show h ∈ E.base
          rw [hbase]
          exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, ha⟩)
      | inr _ => exact ha

/-- Avoidance of `Γ_{E_i}` survives reading a joint word as an auxiliary
word: the two words have the same vertices, and the only joint letters that
become `i`-components are the auxiliary `i`-letters themselves. -/
theorem avoidsFrom_map_auxOfJoint (D : RelGenSet G Λ) (E : RelGenSet G I)
    (i : I) : ∀ (u : List (RelLetter G (Sum Λ I))) (p : G),
      AvoidsFrom (combinedRelGenSet D E).fam (Sum.inr i) u p →
        AvoidsFrom E.fam i (u.map RelLetter.auxOfJoint) p := by
  intro u
  induction u with
  | nil => intro _ _; exact trivial
  | cons a t ih =>
      intro p hp
      obtain ⟨hhead, htail⟩ := hp
      refine ⟨?_, ?_⟩
      · rintro ⟨hc, hmem⟩
        exact hhead ⟨RelLetter.isCompOf_of_auxOfJoint hc, hmem⟩
      · rw [RelLetter.auxOfJoint_val]
        exact ih (p * a.val) htail

/-- **Clause (b) of `↪_h` at an auxiliary index.**  The joint relative ball is
contained in the auxiliary relative ball of the same radius. -/
theorem combined_relBall_inr_subset (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier) (i : I) (n : ℕ) :
    (combinedRelGenSet D E).relBall (Sum.inr i) n ⊆ E.relBall i n := by
  rintro h ⟨hmem, u, hlet, hval, hav, hlen⟩
  refine ⟨hmem, u.map RelLetter.auxOfJoint, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isLetter_auxOfJoint D E hbase (hlet b hb)
  · rw [RelLetter.listVal_map_auxOfJoint]
    exact hval
  · exact avoidsFrom_map_auxOfJoint D E i u 1 hav
  · rw [List.length_map]
    exact hlen

/-- **Clause (a) of `↪_h` for the labelled sum.**  The base equation makes the
joint alphabet equal to the auxiliary alphabet, so its Cayley graph is the
auxiliary one. -/
theorem combinedRelGenSet_hyperbolic (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (combinedRelGenSet D E).alphabet) := by
  have htransport : ∀ P Q : Alphabet G, P = Q →
      (∃ delta : ℝ, IsHyperbolicSpace delta (Cayley Q)) →
        ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley P) := by
    intro P Q hPQ hQ
    subst hPQ
    exact hQ
  exact htransport _ _ (combined_alphabet_eq D E hbase) hE.hyperbolic

/-! ## The statement and its exact residue -/

/-- **The joint-family direction of hyperbolic-embeddedness transitivity.**

`{H_λ} ↪_h (G, X)` and `{E_i} ↪_h (G, X ∪ ⋃_λ H_λ)` give
`{H_λ} ∪ {E_i} ↪_h (G, X)`.

This is the statement Hull's Lemma 4.4 consumes and the one recorded as
unavailable in `RelHypOsin24CombinedFamily`.  It is not
Dahmani--Guirardel--Osin's Proposition 4.35, which replaces `{H_λ}` by
hyperbolically embedded subfamilies of its members instead of keeping it; see
the module docstring. -/
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

/-- With no auxiliary subgroups a joint letter is an original letter. -/
theorem isLetter_origOfJoint_of_isEmpty [IsEmpty I] (D : RelGenSet G Λ)
    (E : RelGenSet G I) {a : RelLetter G (Sum Λ I)}
    (ha : (combinedRelGenSet D E).IsLetter a) :
    D.IsLetter (RelLetter.origOfJoint a) := by
  cases a with
  | base _ => exact ha
  | comp s _ =>
      cases s with
      | inl _ => exact ha
      | inr i => exact isEmptyElim i

/-- Avoidance of `Γ_{H_lam}` survives reading a joint word as an original
word. -/
theorem avoidsFrom_map_origOfJoint (D : RelGenSet G Λ) (E : RelGenSet G I)
    (lam : Λ) : ∀ (u : List (RelLetter G (Sum Λ I))) (p : G),
      AvoidsFrom (combinedRelGenSet D E).fam (Sum.inl lam) u p →
        AvoidsFrom D.fam lam (u.map RelLetter.origOfJoint) p := by
  intro u
  induction u with
  | nil => intro _ _; exact trivial
  | cons a t ih =>
      intro p hp
      obtain ⟨hhead, htail⟩ := hp
      refine ⟨?_, ?_⟩
      · rintro ⟨hc, hmem⟩
        exact hhead ⟨RelLetter.isCompOf_of_origOfJoint hc, hmem⟩
      · rw [RelLetter.origOfJoint_val]
        exact ih (p * a.val) htail

/-- **No auxiliary subgroups.**  The joint relative balls at an original index
are contained in the original ones. -/
theorem combined_relBall_inl_subset_of_isEmpty [IsEmpty I]
    (D : RelGenSet G Λ) (E : RelGenSet G I) (lam : Λ) (n : ℕ) :
    (combinedRelGenSet D E).relBall (Sum.inl lam) n ⊆ D.relBall lam n := by
  rintro h ⟨hmem, u, hlet, hval, hav, hlen⟩
  refine ⟨hmem, u.map RelLetter.origOfJoint, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isLetter_origOfJoint_of_isEmpty D E (hlet b hb)
  · rw [RelLetter.listVal_map_origOfJoint]
    exact hval
  · exact avoidsFrom_map_origOfJoint D E lam u 1 hav
  · rw [List.length_map]
    exact hlen

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

/-! ## Why the base equation cannot be weakened to an inclusion -/

/-- **The inclusion form is false.**

If the auxiliary base is allowed to be strictly larger than the original
relative alphabet, an original peripheral subgroup can be reached in two base
steps and its relative metric collapses.  The hypothesis `hsplit` says exactly
that: every element of `H_lam` is a product of two auxiliary base letters that
are not peripheral letters of the joint family, so all of `H_lam` lies in the
joint relative ball of radius `2`.

This is the obstruction the filling lane meets, where the auxiliary family is
embedded over Hull's alphabet and only an inclusion
`D.alphabet.carrier ⊆ E.base` is available.  Corollary 4.27 repairs only
finite enlargements of a relative generating set. -/
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
