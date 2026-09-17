import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Defs

/-!
# Marked groups, convergence, expander limits, LEF, as printed (`thm:main`, tex l.86–105)

`simple_kazhdan_sofic_group.tex`, the paragraphs after Theorem `thm:main` (gap report, Lane 1, item
D1 and D2):

> A \emph{marked group} is a group with a finite generating tuple. Marked groups
> $(Q_k,\bar q_k)$ converge to a marked group $(G,\bar g)$ in the space of marked groups if the
> tuples have the same length $m$ and, for each word $w$ in $m$ letters and their inverses and all
> large $k$ depending on $w$, we have $w(\bar q_k)=1$ if and only if $w(\bar g)=1$. We call
> $(G,\bar g)$ an \emph{expander limit} of the $(Q_k,\bar q_k)$ if moreover the $Q_k$ are finite,
> $|Q_k|\to\infty$, and their Cayley graphs with respect to the $\bar q_k$ form a family of
> expanders: there is $\varepsilon>0$ such that for every $k$, every set of at most $|Q_k|/2$
> elements of $Q_k$ has at least $\varepsilon$ times as many neighbors outside it as it has
> elements, the neighbors of an element being its products with the entries of $\bar q_k$ and
> their inverses. A group is an expander limit of groups from a class if some marking of it is an
> expander limit of marked groups from that class.
>
> A group is LEF if each finite subset $\Phi$ maps injectively into a finite group by a map that
> preserves every product $gh$ with $g,h,gh\in\Phi$. Limits of finite groups in the space of marked
> groups are LEF.

## Definitions

* `IsMarking`, `MarkedGroup`: a finite generating tuple `Fin m → G`.
* `MarkedConverges q g`: convergence of `(Q k, q k)` to `(G, g)` word by word.
* `cayleyNeighbors q S`: the products `x * q i` and `x * (q i)⁻¹` with `x ∈ S`.
* `IsExpanderLimit q g`: convergence, finite `Q k`, `|Q k| → ∞`, vertex expansion
  `ε |S| ≤ |N(S) \ S|` whenever `2 |S| ≤ |Q k|`.
* `IsExpanderLimitOfClass C G`: some marking of `G` is an expander limit of marked groups from `C`.
* `IsFiniteSimpleSL3NF2`: the class of `thm:main`, finite simple groups isomorphic to some
  `SL_{3N}(F_2)`.
* `IsLEFPrinted G`: the printed LEF definition, equivalent to `IsTextbookLEF` and `IsLEF`.

## Results

* `limitsOfFiniteGroupsAreLEF` (tex l.104–105), with the printed variant
  `limitsOfFiniteGroupsAreLEFPrinted`.
* `isLEFPrinted_of_isExpanderLimitOfClass`: an expander limit of finite groups is LEF.
-/

namespace GroupApproximation.Full.SK01

open Filter

/-! ## Marked groups (tex l.86–87) -/

/-- A tuple `g : Fin m → G` is a **marking** of `G` if its entries generate `G` (tex l.86–87). -/
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

/-- **Convergence of marked groups** (tex l.87–92): the marked groups `(Q k, q k)` converge to the
marked group `(G, g)` if the tuples have the same length `m` and each word `w` in `m` letters and
their inverses is, for all large `k`, trivial at `q k` if and only if it is trivial at `g`. -/
def MarkedConverges {m : ℕ} {Q : ℕ → Type*} [∀ k, Group (Q k)] (q : ∀ k, Fin m → Q k)
    {G : Type*} [Group G] (g : Fin m → G) : Prop :=
  (∀ k, IsMarking (q k)) ∧ IsMarking g ∧
    ∀ w : FreeGroup (Fin m), ∀ᶠ k in atTop, (FreeGroup.lift (q k) w = 1 ↔ FreeGroup.lift g w = 1)

/-- Printed convergence is the corpus notion `SimpleKazhdanSofic.IsMarkedLimit` with the
generating tuples indexed by `Fin m`. -/
theorem markedConverges_iff_isMarkedLimit {m : ℕ} {Q : ℕ → Type*} [∀ k, Group (Q k)]
    (q : ∀ k, Fin m → Q k) {G : Type*} [Group G] (g : Fin m → G) :
    MarkedConverges q g ↔ SimpleKazhdanSofic.IsMarkedLimit g q :=
  ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

/-! ## Expander limits (tex l.92–100) -/

/-- The **neighbours** of a set `S` in the Cayley graph of `Q` with respect to `q`: the products of
its elements with the entries of `q` and their inverses (tex l.97–98). -/
def cayleyNeighbors {Q : Type*} [Group Q] {m : ℕ} (q : Fin m → Q) (S : Set Q) : Set Q :=
  {y | ∃ x ∈ S, ∃ i : Fin m, y = x * q i ∨ y = x * (q i)⁻¹}

/-- **Expander limit** (tex l.92–98): `(G, g)` is the limit of `(Q k, q k)`, the `Q k` are finite
with `|Q k| → ∞`, and there is `ε > 0` such that for every `k` every `S ⊆ Q k` with at most
`|Q k| / 2` elements has at least `ε |S|` neighbours outside `S`. -/
def IsExpanderLimit {m : ℕ} {Q : ℕ → Type*} [∀ k, Group (Q k)] (q : ∀ k, Fin m → Q k)
    {G : Type*} [Group G] (g : Fin m → G) : Prop :=
  MarkedConverges q g ∧ (∀ k, Finite (Q k)) ∧ Tendsto (fun k => Nat.card (Q k)) atTop atTop ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (S : Set (Q k)), 2 * S.ncard ≤ Nat.card (Q k) →
      ε * (S.ncard : ℝ) ≤ ((cayleyNeighbors (q k) S \ S).ncard : ℝ)

/-- **Expander limit of groups from a class** (tex l.98–100): some marking of `G` is an expander
limit of marked groups whose underlying groups lie in the class `C`. -/
def IsExpanderLimitOfClass (C : ∀ (Q : Type) [Group Q], Prop) (G : Type*) [Group G] : Prop :=
  ∃ (m : ℕ) (g : Fin m → G) (Q : ℕ → Type) (inst : ∀ k, Group (Q k)) (q : ∀ k, Fin m → Q k),
    (∀ k, @C (Q k) (inst k)) ∧ @IsExpanderLimit m Q inst q G _ g

/-- The class of `thm:main` (tex l.77–78): *finite simple groups `SL_{3N}(F_2)`*.  A group is in the
class when it is finite, simple, and isomorphic to `SL_{3N}(F_2)` for some `N`. -/
def IsFiniteSimpleSL3NF2 (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsSimpleGroup Q ∧
    ∃ N : ℕ, Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin (3 * N)) (ZMod 2))

/-! ## LEF (tex l.102–105) -/

/-- **LEF as printed** (tex l.102–104): each finite subset `Φ` maps injectively into a finite group
by a map that preserves every product `gh` with `g, h, gh ∈ Φ`. -/
def IsLEFPrinted (G : Type*) [Group G] : Prop :=
  ∀ Φ : Finset G, ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : G → Q),
    Set.InjOn f (Φ : Set G) ∧ ∀ g ∈ Φ, ∀ h ∈ Φ, g * h ∈ Φ → f (g * h) = f g * f h

/-- The printed LEF definition is the corpus textbook notion. -/
theorem isLEFPrinted_iff_isTextbookLEF (G : Type*) [Group G] :
    IsLEFPrinted G ↔ IsTextbookLEF G := by
  constructor
  · intro h Φ
    obtain ⟨Q, instQ, hQ, f, hinj, hmul⟩ := h Φ
    exact ⟨{ groupCarrier := Q, group := instQ, fintype := @Fintype.ofFinite Q hQ,
      decidableEq := Classical.decEq Q }, f, hinj, hmul⟩
  · intro h Φ
    obtain ⟨M, f, hinj, hmul⟩ := h Φ
    exact ⟨M.groupCarrier, M.group, @Finite.of_fintype M.groupCarrier M.fintype, f, hinj, hmul⟩

/-- The printed LEF definition is the corpus notion `IsLEF` (permutation targets). -/
theorem isLEFPrinted_iff_isLEF (G : Type*) [Group G] : IsLEFPrinted G ↔ IsLEF G :=
  (isLEFPrinted_iff_isTextbookLEF G).trans (isLEF_iff_textbook G).symm

/-- **tex l.104–105.** *Limits of finite groups in the space of marked groups are LEF.* -/
theorem limitsOfFiniteGroupsAreLEF {m : ℕ} {Q : ℕ → Type} [∀ k, Group (Q k)]
    [∀ k, Finite (Q k)] (q : ∀ k, Fin m → Q k) {G : Type*} [Group G] (g : Fin m → G)
    (h : MarkedConverges q g) : IsLEF G :=
  SimpleKazhdanSofic.isLEF_of_isMarkedLimit (fun k => (inferInstance : Finite (Q k)))
    ((markedConverges_iff_isMarkedLimit q g).mp h)

/-- **tex l.104–105**, with LEF in the printed form `IsLEFPrinted` (tex l.102–104). -/
theorem limitsOfFiniteGroupsAreLEFPrinted {m : ℕ} {Q : ℕ → Type} [∀ k, Group (Q k)]
    [∀ k, Finite (Q k)] (q : ∀ k, Fin m → Q k) {G : Type*} [Group G] (g : Fin m → G)
    (h : MarkedConverges q g) : IsLEFPrinted G :=
  (isLEFPrinted_iff_isLEF G).mpr (limitsOfFiniteGroupsAreLEF q g h)

/-- An expander limit of groups from any class is LEF (`thm:main`, "So `G_X` is LEF"): the groups of
an expander limit are finite. -/
theorem isLEF_of_isExpanderLimitOfClass {C : ∀ (Q : Type) [Group Q], Prop} {G : Type*} [Group G]
    (h : IsExpanderLimitOfClass C G) : IsLEF G := by
  obtain ⟨m, g, Q, inst, q, _, hconv, hfin, _⟩ := h
  exact SimpleKazhdanSofic.isLEF_of_isMarkedLimit hfin ((markedConverges_iff_isMarkedLimit q g).mp hconv)

/-- An expander limit of groups from any class is LEF in the printed sense. -/
theorem isLEFPrinted_of_isExpanderLimitOfClass {C : ∀ (Q : Type) [Group Q], Prop} {G : Type*}
    [Group G] (h : IsExpanderLimitOfClass C G) : IsLEFPrinted G :=
  (isLEFPrinted_iff_isLEF G).mpr (isLEF_of_isExpanderLimitOfClass h)

end GroupApproximation.Full.SK01

#audit_axioms GroupApproximation.Full.SK01.limitsOfFiniteGroupsAreLEF
#audit_axioms GroupApproximation.Full.SK01.limitsOfFiniteGroupsAreLEFPrinted
#audit_axioms GroupApproximation.Full.SK01.isLEFPrinted_of_isExpanderLimitOfClass
