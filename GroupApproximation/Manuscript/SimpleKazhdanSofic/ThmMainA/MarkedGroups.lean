import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import Mathlib.Algebra.Group.Pointwise.Set.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Marked groups, convergence, expander limits, LEF (Theorem `thm:main`, tex l.86–105)

`simple_kazhdan_sofic_group.tex`, the paragraph after Theorem `thm:main`:

> (l.86–87) A \emph{marked group} is a group with a finite generating tuple.
>
> (l.87–92) Marked groups $(Q_k,\bar q_k)$ converge to a marked group $(G,\bar g)$ in the space of
> marked groups~\cite{Grigorchuk,Champetier} if the tuples have the same length $m$ and, for each
> word $w$ in $m$ letters and their inverses and all large $k$ depending on $w$, we have
> $w(\bar q_k)=1$ if and only if $w(\bar g)=1$.
>
> (l.92–98) We call $(G,\bar g)$ an \emph{expander limit} of the $(Q_k,\bar q_k)$ if moreover the
> $Q_k$ are finite, $|Q_k|\to\infty$, and their Cayley graphs with respect to the $\bar q_k$ form a
> family of expanders: there is $\varepsilon>0$ such that for every $k$, every set of at most
> $|Q_k|/2$ elements of $Q_k$ has at least $\varepsilon$ times as many neighbors outside it as it
> has elements, the neighbors of an element being its products with the entries of $\bar q_k$ and
> their inverses.
>
> (l.98–100) A group is an expander limit of groups from a class if some marking of it is an
> expander limit of marked groups from that class.
>
> (l.102–104) A group is LEF~\cite{VershikGordon} if each finite subset $\Phi$ maps injectively
> into a finite group by a map that preserves every product $gh$ with $g,h,gh\in\Phi$.
>
> (l.104–105) Limits of finite groups in the space of marked groups are LEF.

## Definitions

* `IsMarking`, `MarkedGroup`: a group with a finite generating tuple `Fin m → G`.
* `MarkedConverges q g`: both sides are markings of the same length `m`, and every word
  `w : FreeGroup (Fin m)` is eventually trivial at `q k` exactly when it is trivial at `g`.
* `cayleyNeighbors q S`: the products `x * q i` and `x * (q i)⁻¹` for `x ∈ S`.
* `IsExpanderLimit q g`: convergence, finite `Q k`, `|Q k| → ∞`, and vertex expansion
  `ε |S| ≤ |N(S) \ S|` for every `S` with `2|S| ≤ |Q k|`.
* `IsExpanderLimitOfClass C G`: some marking of `G` is an expander limit of marked groups in `C`.
* LEF is `GroupApproximation.IsTextbookLEF` (`Sofic.LEF`), verbatim the printed definition.

## Proof routes

* `manuscriptSentence_limitsOfFiniteGroupsAreLEF`: a convergent sequence of finite marked groups is
  a marked limit in the sense of `SimpleKazhdanSofic.IsMarkedLimit`, and
  `isTextbookLEF_of_isMarkedLimit` evaluates the finitely many words describing `Φ` in one late `Q k`.
* `isExpanderLimit_of_isMarkedLimit` converts the corpus form of `thm:main` (a finite index type
  `ι`, edge expansion `x ↦ σ_i x`) into the printed form (a tuple `Fin m`, vertex expansion through
  right products with generators and inverses).  The generators are reindexed by `ι ≃ Fin m`.  For
  expansion, every left edge `x ↦ σ_i x` leaving `S⁻¹` gives the right neighbour
  `(σ_i x)⁻¹ = x⁻¹ σ_i⁻¹` of `x⁻¹ ∈ S` outside `S`.  The map `(x, i) ↦ ((σ_i x)⁻¹, i)` is injective,
  so `ε |S| ≤ #edges ≤ m |N(S) \ S|`, and `ε / (m + 1)` is a vertex-expansion constant.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainA

open Filter Set
open scoped Pointwise

/-! ## Marked groups (tex l.86–87) -/

/-- A tuple `g : Fin m → G` is a **marking** of `G` if its entries generate `G`. -/
def IsMarking {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) : Prop :=
  Subgroup.closure (Set.range g) = ⊤

/-- **A marked group** (tex l.86–87): a group with a finite generating tuple. -/
structure MarkedGroup where
  /-- The underlying type. -/
  carrier : Type
  /-- The group structure. -/
  group : Group carrier
  /-- The length `m` of the generating tuple. -/
  length : ℕ
  /-- The generating tuple. -/
  marking : Fin length → carrier
  /-- The tuple generates the group. -/
  generates : @IsMarking carrier group length marking

/-! ## Convergence in the space of marked groups (tex l.87–92) -/

/-- **Convergence of marked groups** (tex l.87–92): marked groups `(Q k, q k)` converge to the marked
group `(G, g)` if the tuples have the same length `m` and each word `w` in `m` letters and their
inverses is, for all large `k`, trivial at `q k` if and only if it is trivial at `g`. -/
def MarkedConverges {m : ℕ} {Q : ℕ → Type*} [∀ k, Group (Q k)] (q : ∀ k, Fin m → Q k)
    {G : Type*} [Group G] (g : Fin m → G) : Prop :=
  (∀ k, IsMarking (q k)) ∧ IsMarking g ∧
    ∀ w : FreeGroup (Fin m), ∀ᶠ k in atTop, (FreeGroup.lift (q k) w = 1 ↔ FreeGroup.lift g w = 1)

/-! ## Expander limits (tex l.92–100) -/

/-- The **neighbours** of a set `S` in the Cayley graph of `Q` with respect to `q`: the products of
its elements with the entries of `q` and their inverses (tex l.97–98). -/
def cayleyNeighbors {Q : Type*} [Group Q] {m : ℕ} (q : Fin m → Q) (S : Set Q) : Set Q :=
  {y | ∃ x ∈ S, ∃ i : Fin m, y = x * q i ∨ y = x * (q i)⁻¹}

/-- **Expander limit** (tex l.92–98): `(G, g)` is the limit of `(Q k, q k)`, the `Q k` are finite
with `|Q k| → ∞`, and there is `ε > 0` such that every `S ⊆ Q k` with at most `|Q k|/2` elements has
at least `ε |S|` neighbours outside `S`. -/
def IsExpanderLimit {m : ℕ} {Q : ℕ → Type*} [∀ k, Group (Q k)] (q : ∀ k, Fin m → Q k)
    {G : Type*} [Group G] (g : Fin m → G) : Prop :=
  MarkedConverges q g ∧ (∀ k, Finite (Q k)) ∧ Tendsto (fun k => Nat.card (Q k)) atTop atTop ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (S : Set (Q k)), 2 * S.ncard ≤ Nat.card (Q k) →
      ε * S.ncard ≤ (cayleyNeighbors (q k) S \ S).ncard

/-- **Expander limit of groups from a class** (tex l.98–100): some marking of `G` is an expander
limit of marked groups whose underlying groups lie in the class `C`. -/
def IsExpanderLimitOfClass (C : ∀ (Q : Type) [Group Q], Prop) (G : Type*) [Group G] : Prop :=
  ∃ (m : ℕ) (g : Fin m → G) (Q : ℕ → Type) (_ : ∀ k, Group (Q k)) (q : ∀ k, Fin m → Q k),
    (∀ k, C (Q k)) ∧ IsExpanderLimit q g

/-! ## From the corpus form of `thm:main` to the printed form -/

/-- Reindexing the generators by an equivalence reindexes the words. -/
theorem lift_comp_equiv_apply {ι κ K : Type*} [Group K] (f : ι → K) (e : ι ≃ κ)
    (w : FreeGroup κ) :
    FreeGroup.lift (fun j => f (e.symm j)) w = FreeGroup.lift f (FreeGroup.map e.symm w) := by
  have h := FreeGroup.lift_unique (f := fun j => f (e.symm j))
    ((FreeGroup.lift f).comp (FreeGroup.map e.symm))
    (fun x => by rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]) (x := w)
  rw [MonoidHom.comp_apply] at h
  exact h.symm

/-- Left edges `x ↦ σ_i x` leaving `S⁻¹` inject into pairs (right neighbour of `S` outside `S`,
letter). -/
theorem ncard_leavingEdges_inv_le {ι H : Type*} [Group H] [Finite H] (σ : ι → H) {m : ℕ}
    (e : ι ≃ Fin m) (S : Set H) :
    ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard ≤
      (cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard * m := by
  have hmaps : ∀ p ∈ ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)),
      (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2)) p ∈
        (cayleyNeighbors (fun j => σ (e.symm j)) S \ S) ×ˢ (Set.univ : Set (Fin m)) := by
    intro p hp
    obtain ⟨hy, hyi⟩ := hp
    have hnbr : (σ p.2 * p.1)⁻¹ ∈ cayleyNeighbors (fun j => σ (e.symm j)) S := by
      refine ⟨p.1⁻¹, Set.mem_inv.mp hy, e p.2, Or.inr ?_⟩
      show (σ p.2 * p.1)⁻¹ = p.1⁻¹ * (σ (e.symm (e p.2)))⁻¹
      rw [Equiv.symm_apply_apply, mul_inv_rev]
    have hout : (σ p.2 * p.1)⁻¹ ∉ S := fun hmem => hyi (Set.mem_inv.mpr hmem)
    exact Set.mk_mem_prod ⟨hnbr, hout⟩ (Set.mem_univ _)
  have hinj : Set.InjOn (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2))
      ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)) := by
    intro p _ p' _ h
    have h1 : (σ p.2 * p.1)⁻¹ = (σ p'.2 * p'.1)⁻¹ := congrArg Prod.fst h
    have h2 : e p.2 = e p'.2 := congrArg Prod.snd h
    have hi : p.2 = p'.2 := e.injective h2
    rw [inv_inj, hi, mul_right_inj] at h1
    exact Prod.ext h1 hi
  have h := Set.ncard_le_ncard_of_injOn (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2)) hmaps hinj
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin] at h
  exact h

/-- Edge expansion of `S⁻¹` with constant `ε` gives vertex expansion of `S` with constant
`ε / (m + 1)`. -/
theorem expansion_transfer {ι H : Type*} [Group H] [Finite H] (σ : ι → H) {m : ℕ}
    (e : ι ≃ Fin m) {ε : ℝ} (S : Set H)
    (hbound : ε * ((S⁻¹).ncard : ℝ) ≤
      (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ)) :
    ε / ((m : ℝ) + 1) * (S.ncard : ℝ) ≤
      ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) := by
  have hcount := ncard_leavingEdges_inv_le σ e S
  have hcount' : (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ) ≤
      ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * (m : ℝ) := by
    exact_mod_cast hcount
  rw [Set.ncard_inv] at hbound
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) :=
    Nat.cast_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  calc ε * (S.ncard : ℝ)
      ≤ (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ) := hbound
    _ ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * (m : ℝ) := hcount'
    _ ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hN

/-- A marked limit with a family of expanders, in the corpus form of `thm:main`
(`SimpleKazhdanSofic.IsMarkedLimit`, `SimpleKazhdanSofic.IsExpanderFamily`), is an expander limit in
the printed sense, after reindexing the finite generating family by `Fin m`. -/
theorem isExpanderLimit_of_isMarkedLimit {ι G : Type*} [Group G] {s : ι → G} {H : ℕ → Type*}
    [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} (hlim : IsMarkedLimit s σ)
    (hexp : IsExpanderFamily σ) :
    ∃ (m : ℕ) (g : Fin m → G) (q : ∀ ℓ, Fin m → H ℓ), IsExpanderLimit q g := by
  obtain ⟨hs, hσ, hw⟩ := hlim
  obtain ⟨hι, hfin, hcard, ε, hε, hbound⟩ := hexp
  haveI := hι
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Nat.card ι)) := ⟨Finite.equivFin ι⟩
  have hmarkG : IsMarking (fun j => s (e.symm j)) := by
    show Subgroup.closure (Set.range (s ∘ e.symm)) = ⊤
    rw [e.symm.surjective.range_comp]
    exact hs
  have hmark : ∀ ℓ, IsMarking (fun j => σ ℓ (e.symm j)) := fun ℓ => by
    show Subgroup.closure (Set.range (σ ℓ ∘ e.symm)) = ⊤
    rw [e.symm.surjective.range_comp]
    exact hσ ℓ
  have hwords : ∀ w : FreeGroup (Fin (Nat.card ι)), ∀ᶠ ℓ in atTop,
      (FreeGroup.lift (fun j => σ ℓ (e.symm j)) w = 1 ↔
        FreeGroup.lift (fun j => s (e.symm j)) w = 1) := by
    intro w
    filter_upwards [hw (FreeGroup.map e.symm w)] with ℓ hℓ
    show (FreeGroup.lift (fun j => σ ℓ (e.symm j)) w = 1 ↔
      FreeGroup.lift (fun j => s (e.symm j)) w = 1)
    rw [lift_comp_equiv_apply (σ ℓ) e w, lift_comp_equiv_apply s e w]
    exact hℓ
  have hexp' : ∀ (ℓ : ℕ) (S : Set (H ℓ)), 2 * S.ncard ≤ Nat.card (H ℓ) →
      ε / ((Nat.card ι : ℝ) + 1) * (S.ncard : ℝ) ≤
        ((cayleyNeighbors (fun j => σ ℓ (e.symm j)) S \ S).ncard : ℝ) := by
    intro ℓ S hS
    haveI := hfin ℓ
    exact expansion_transfer (σ ℓ) e S (hbound ℓ S⁻¹ (by rw [Set.ncard_inv]; exact hS))
  exact ⟨Nat.card ι, fun j => s (e.symm j), fun ℓ j => σ ℓ (e.symm j),
    ⟨hmark, hmarkG, hwords⟩, hfin, hcard, ε / ((Nat.card ι : ℝ) + 1),
    div_pos hε (by positivity), hexp'⟩

/-! ## Limits of finite groups are LEF (tex l.102–105) -/

/-- **tex l.104–105.** *Limits of finite groups in the space of marked groups are LEF.*  LEF is the
printed definition `IsTextbookLEF` (tex l.102–104). -/
theorem manuscriptSentence_limitsOfFiniteGroupsAreLEF {m : ℕ} {Q : ℕ → Type} [∀ k, Group (Q k)]
    (q : ∀ k, Fin m → Q k) {G : Type*} [Group G] (g : Fin m → G) (hfin : ∀ k, Finite (Q k))
    (hconv : MarkedConverges q g) : IsTextbookLEF G := by
  obtain ⟨hq, hg, hw⟩ := hconv
  have hlim : IsMarkedLimit g q := ⟨hg, hq, hw⟩
  exact isTextbookLEF_of_isMarkedLimit hfin hlim

end ThmMainA
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.lift_comp_equiv_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.ncard_leavingEdges_inv_le
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.expansion_transfer
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.isExpanderLimit_of_isMarkedLimit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF
