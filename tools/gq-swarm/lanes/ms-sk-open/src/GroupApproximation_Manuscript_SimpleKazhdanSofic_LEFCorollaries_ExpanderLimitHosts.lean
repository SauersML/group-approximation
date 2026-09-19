import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Set.Card

/-!
# Expander limits, and the first statements of `cor:lef` and `cor:host`

`simple_kazhdan_sofic_group.tex` (current text, commit 1eefb3bbb), introduction, l.92–100:

> We call $(G,\bar g)$ an \emph{expander limit} of the $(Q_k,\bar q_k)$ if moreover the $Q_k$ are
> finite, $|Q_k|\to\infty$, and their Cayley graphs with respect to the $\bar q_k$ form a family of
> expanders: there is $\varepsilon>0$ such that for every $k$, every set of at most $|Q_k|/2$
> elements of $Q_k$ has at least $\varepsilon$ times as many neighbors outside it as it has
> elements, the neighbors of an element being its products with the entries of $\bar q_k$ and their
> inverses. A group is an expander limit of groups from a class if some marking of it is an expander
> limit of marked groups from that class.

Section "LEF groups", l.444–447 and l.454–456, l.464–466:

> Corollary~\ref{cor:lef} answers the analogous question for simple Kazhdan groups that are limits
> of finite simple groups.

> A finitely generated group is LEF if and only if it is a subgroup of an infinite, finitely
> generated, simple Kazhdan group that is an expander limit of finite simple groups
> $\SL_N(\F_2)$.

> The members of a set of finitely generated groups embed in a single such group if and only if
> they are LEF and represent countably many isomorphism classes.

## Spelling

* `outerNeighbors q S` is the set of neighbours outside `S`: the elements `q_i x` and `q_i⁻¹ x`,
  `x ∈ S`, that are not in `S`. The note does not say on which side the products are taken. We take
  left products, as `IsExpanderFamily` in `MainAssembly` does.
* `IsNeighborExpanderFamily σ` is the printed definition of a family of expanders. The marking is
  finite, the groups are finite, `|Q_k| → ∞`, and there is `ε > 0` with
  `ε |S| ≤ |outerNeighbors (σ k) S|` whenever `2 |S| ≤ |Q_k|`.
* `IsExpanderLimitHost E` is "an infinite, finitely generated, simple Kazhdan group that is an
  expander limit of finite simple groups `SL_N(F₂)`". `SL_N(F₂)` is read up to reindexing by a
  finite type `κ k`, as in `IsLEFHost`, and the marked limit is `MainAssembly.IsMarkedLimit`.

## Proof route

* `isNeighborExpanderFamily_of_isExpanderFamily`: edge expansion gives neighbour expansion, with
  `ε / (|ι| + 1)`. The map `(x, i) ↦ (σ_i x, i)` injects the leaving edges into
  `outerNeighbors × ι`. So `IsLEFHost E → IsExpanderLimitHost E`.
* The "only if" halves come from the closed `printedLEFSubgroupCharacterization` and
  `printedLEFFamilyHost` (lamplighter host, `thm:general`, `lem:nn`, the restricted sum). Both are
  for `IsLEFHost`, and the neighbour form follows.
* The "if" halves: an expander limit is a marked limit of finite groups, so it is LEF
  (`printedMarkedLimitLEFStatement`), and LEF passes to subgroups. A finitely generated group is
  countable, so it has countably many finitely generated subgroups (`countable_fg_subgroups`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LEFCorollaries

open Filter

universe u

/-! ## The printed definition of an expander limit -/

/-- **The neighbours outside a set** (tex l.96–98): the products `q_i x` and `q_i⁻¹ x` with
`x ∈ S` that do not lie in `S`. -/
def outerNeighbors {ι Q : Type*} [Group Q] (q : ι → Q) (S : Set Q) : Set Q :=
  {y : Q | y ∉ S ∧ ∃ x ∈ S, ∃ i : ι, y = q i * x ∨ y = (q i)⁻¹ * x}

/-- **A family of expanders, as printed** (tex l.93–98): the marking is finite, the groups are
finite, their orders tend to infinity, and there is `ε > 0` such that for every `k`, every set of at
most `|Q_k|/2` elements has at least `ε` times as many neighbours outside it as it has elements. -/
def IsNeighborExpanderFamily {ι : Type*} {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)]
    (σ : ∀ ℓ, ι → H ℓ) : Prop :=
  Finite ι ∧ (∀ ℓ, Finite (H ℓ)) ∧ Tendsto (fun ℓ => Nat.card (H ℓ)) atTop atTop ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ℓ : ℕ) (S : Set (H ℓ)), 2 * S.ncard ≤ Nat.card (H ℓ) →
      ε * S.ncard ≤ (outerNeighbors (σ ℓ) S).ncard

/-- **Edge expansion gives neighbour expansion.** Each leaving edge `x → σ_i x` gives the neighbour
`σ_i x` outside `S` together with the label `i`, and this is injective. So
`ε |S| ≤ #edges ≤ |ι| · #neighbours`, and `ε / (|ι| + 1)` works. -/
theorem isNeighborExpanderFamily_of_isExpanderFamily {ι : Type*} {H : ℕ → Type*}
    [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} (h : IsExpanderFamily σ) :
    IsNeighborExpanderFamily σ := by
  obtain ⟨hι, hH, htend, ε, hε, hexp⟩ := h
  refine ⟨hι, hH, htend, ε / ((Nat.card ι : ℝ) + 1), div_pos hε (by positivity),
    fun ℓ S hS => ?_⟩
  haveI : Finite ι := hι
  haveI : Finite (H ℓ) := hH ℓ
  have hmaps : ∀ p ∈ ({p : H ℓ × ι | p.1 ∈ S ∧ σ ℓ p.2 * p.1 ∉ S} : Set (H ℓ × ι)),
      (σ ℓ p.2 * p.1, p.2) ∈ outerNeighbors (σ ℓ) S ×ˢ (Set.univ : Set ι) := by
    rintro ⟨x, i⟩ ⟨hx, hout⟩
    exact ⟨⟨hout, x, hx, i, Or.inl rfl⟩, Set.mem_univ i⟩
  have hinj : Set.InjOn (fun p : H ℓ × ι => (σ ℓ p.2 * p.1, p.2))
      ({p : H ℓ × ι | p.1 ∈ S ∧ σ ℓ p.2 * p.1 ∉ S} : Set (H ℓ × ι)) := by
    rintro ⟨x, i⟩ - ⟨y, j⟩ - hxy
    have hij : i = j := congrArg Prod.snd hxy
    subst hij
    have hxy' : σ ℓ i * x = σ ℓ i * y := congrArg Prod.fst hxy
    rw [mul_left_cancel hxy']
  have hle := Set.ncard_le_ncard_of_injOn (fun p : H ℓ × ι => (σ ℓ p.2 * p.1, p.2)) hmaps hinj
  rw [Set.ncard_prod, Set.ncard_univ] at hle
  have hE : ε * S.ncard ≤
      (({p : H ℓ × ι | p.1 ∈ S ∧ σ ℓ p.2 * p.1 ∉ S} : Set (H ℓ × ι)).ncard : ℝ) :=
    hexp ℓ S hS
  have hle' : (({p : H ℓ × ι | p.1 ∈ S ∧ σ ℓ p.2 * p.1 ∉ S} : Set (H ℓ × ι)).ncard : ℝ) ≤
      ((outerNeighbors (σ ℓ) S).ncard : ℝ) * (Nat.card ι : ℝ) := by
    exact_mod_cast hle
  have hN : (0 : ℝ) ≤ ((outerNeighbors (σ ℓ) S).ncard : ℝ) := Nat.cast_nonneg _
  have hc : (0 : ℝ) < (Nat.card ι : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hc]
  nlinarith

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.isNeighborExpanderFamily_of_isExpanderFamily

/-- **The hosts of `cor:lef` and `cor:host`, as printed** (tex l.454–456): an infinite, finitely
generated, simple Kazhdan group that is an expander limit of finite simple groups `SL_N(F₂)`. -/
def IsExpanderLimitHost (E : Type) [Group E] : Prop :=
  Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    ∃ (ι : Type) (s : ι → E) (κ : ℕ → Type) (_ : ∀ ℓ, Fintype (κ ℓ))
      (_ : ∀ ℓ, DecidableEq (κ ℓ)) (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2)),
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2))) ∧ IsMarkedLimit s σ ∧
        IsNeighborExpanderFamily σ

/-- A host with edge expansion is a host with the printed neighbour expansion. -/
theorem isExpanderLimitHost_of_isLEFHost {E : Type} [Group E] (h : IsLEFHost E) :
    IsExpanderLimitHost E := by
  obtain ⟨hinf, hfg, hsimple, hT, ι, s, κ, hκ, hdec, σ, hSL, hlim, hexp⟩ := h
  exact ⟨hinf, hfg, hsimple, hT, ι, s, κ, hκ, hdec, σ, hSL, hlim,
    isNeighborExpanderFamily_of_isExpanderFamily hexp⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.isExpanderLimitHost_of_isLEFHost

/-- An expander limit of finite groups is LEF, being a limit of finite groups in the space of marked
groups (tex l.104–105). -/
theorem isLEF_of_isExpanderLimitHost {E : Type} [Group E] (h : IsExpanderLimitHost E) :
    IsLEF E := by
  obtain ⟨-, -, -, -, ι, s, κ, _, _, σ, -, hlim, hexp⟩ := h
  exact printedMarkedLimitLEFStatement ι E s (fun ℓ => Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2))
    σ hexp.2.1 hlim

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.isLEF_of_isExpanderLimitHost

/-! ## `cor:lef`, first statement -/

/-- **`cor:lef`, first statement** (tex l.454–456): a finitely generated group is LEF if and only if
it is a subgroup of an infinite, finitely generated, simple Kazhdan group that is an expander limit
of finite simple groups `SL_N(F₂)`. -/
theorem manuscriptSentence_lefIffSubgroupOfExpanderLimitHost (Γ : Type) [Group Γ]
    (hfg : Group.FG Γ) :
    IsLEF Γ ↔
      ∃ (E : Type) (_ : Group E), IsExpanderLimitHost E ∧ ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · intro hΓ
    obtain ⟨E, _, hE, f, hf⟩ := (printedLEFSubgroupCharacterization Γ hfg).1 hΓ
    exact ⟨E, inferInstance, isExpanderLimitHost_of_isLEFHost hE, f, hf⟩
  · rintro ⟨E, _, hE, f, hf⟩
    exact isLEF_of_injective f hf (isLEF_of_isExpanderLimitHost hE)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_lefIffSubgroupOfExpanderLimitHost

/-! ## `cor:host`, second statement -/

/-- **`cor:host`, second statement** (tex l.464–466): the members of a set of finitely generated
groups embed in a single such group if and only if they are LEF and represent countably many
isomorphism classes. -/
theorem manuscriptSentence_familyEmbedsIffLEFCountableClasses {ι : Type u} (Γ : ι → Type)
    [∀ i, Group (Γ i)] (hfg : ∀ i, Group.FG (Γ i)) :
    (∃ (E : Type) (_ : Group E), IsExpanderLimitHost E ∧
        ∀ i, ∃ f : Γ i →* E, Function.Injective f) ↔
      (∀ i, IsLEF (Γ i)) ∧
        ∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
          ∀ i, ∃ j, Nonempty (Γ i ≃* H j) := by
  constructor
  · rintro ⟨E, _, hE, hemb⟩
    have hlefE : IsLEF E := isLEF_of_isExpanderLimitHost hE
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨f, hf⟩ := hemb i
      exact isLEF_of_injective f hf hlefE
    · haveI : Group.FG E := hE.2.1
      haveI : Countable E := ContinuumMultiplicity.countable_of_fg E
      refine ⟨↥{K : Subgroup E | K.FG}, (ContinuumMultiplicity.countable_fg_subgroups E).to_subtype,
        fun j => ↥(j : Subgroup E), fun j => inferInstance, fun i => ?_⟩
      obtain ⟨f, hf⟩ := hemb i
      haveI : Group.FG (Γ i) := hfg i
      have hrange : f.range.FG := (Group.fg_iff_subgroup_fg f.range).mp (Group.fg_range f)
      exact ⟨⟨f.range, hrange⟩, ⟨MonoidHom.ofInjective hf⟩⟩
  · intro h
    obtain ⟨E, _, hE, hemb⟩ := (printedLEFFamilyHost.{u} ι Γ hfg).2 h
    exact ⟨E, inferInstance, isExpanderLimitHost_of_isLEFHost hE, hemb⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_familyEmbedsIffLEFCountableClasses

end LEFCorollaries
end SimpleKazhdanSofic
end GroupApproximation
