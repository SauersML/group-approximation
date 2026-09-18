import GroupApproximation.Sofic.LEF
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Asymptotic residual finiteness (census key `aaf5fe1a98c3`)

`simple_kazhdan_sofic_group.tex`, introduction (census tex l.63–66, an attribution row):

> Arzhantseva listed the sofic form among open questions, and gave an infinite simple Kazhdan
> group that is asymptotically residually finite, a weaker property in which the generating set
> may change with the radius~\cite[\S3]{Arzhantseva}.

The sentence credits Arzhantseva, but it also asserts two mathematical facts:
* there is an infinite simple Kazhdan group that is asymptotically residually finite;
* asymptotic residual finiteness is weaker than local embeddability into finite groups.

Both are proved here from the corpus, with no inputs. As in `Audit2.LEFModelsAndHosts`, the route
differs from the cited one. Arzhantseva's example (Theorem 11 of the cited survey) is a torsion-free
Tarski monster quotient of a hyperbolic Kazhdan group. Here the witness is `G_X` at the Toeplitz
subshift, which is LEF by `thm:main`. The first clause, that the sofic form was listed as open, is a
statement about the literature and is not formalized.

## The definition

Arzhantseva, *Asymptotic approximations of finitely generated groups*, Extended Abstracts Fall 2012,
Trends Math. 1 (2014), Definition 9, p. 12 (read at the published source):
* a group `G` is asymptotically approximated by a family of metric groups if, for each `n ∈ ℕ`, there
  are a finite generating set `S_n` of `G` and a map `π` from the ball `B_{S_n}(n)` to a group
  `(F, dist)` of the family;
* the map must satisfy (*) `dist(π(g)π(h), π(gh)) < 1/n` whenever `g`, `h` and `gh` lie in the ball,
  and (**) `dist(π(g), π(h)) > 1 − 1/n` for distinct `g`, `h` in the ball;
* *asymptotically residually finite* means that the family consists of residually finite groups.

The same page names the basic metric, in which every nontrivial element has length `1`. With it,
(*) says that `π` is multiplicative on the ball and (**) that it is injective there.
`IsAsymptoticallyResiduallyFinite` is this discrete form. `wordBall S n` is the ball of radius `n`
of the word metric of `S`.

## Declarations

* `wordBall`, `wordBall_finite`: balls of the word metric, which are finite.
* `IsAsymptoticallyResiduallyFinite`: Definition 9 with residually finite targets.
* `isAsymptoticallyResiduallyFinite_of_isLEF`: a finitely generated LEF group is asymptotically
  residually finite, with a constant generating set.
* `isAsymptoticallyResiduallyFinite_of_residuallyFinite`: so is a finitely generated residually
  finite group (the survey's Examples 10).
* `manuscriptSentence_infiniteSimpleKazhdanAsymptoticallyResiduallyFinite`: an infinite, finitely
  generated, simple Kazhdan group that is asymptotically residually finite.
* `manuscriptSentence_arzhantsevaAsymptoticallyResiduallyFinite`: the sentence.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

open GroupApproximation GroupApproximation.SimpleKazhdanSofic

/-- The closed ball of radius `n` about `1` in the word metric of the finite set `S`: the products of
at most `n` elements of `S ∪ S⁻¹`. -/
def wordBall {Γ : Type*} [Group Γ] (S : Finset Γ) : ℕ → Set Γ
  | 0 => {1}
  | n + 1 => wordBall S n ∪ {x | ∃ y ∈ wordBall S n, ∃ s ∈ S, x = y * s ∨ x = y * s⁻¹}

/-- Balls of the word metric of a finite set are finite. -/
theorem wordBall_finite {Γ : Type*} [Group Γ] (S : Finset Γ) : ∀ n, (wordBall S n).Finite
  | 0 => Set.finite_singleton 1
  | n + 1 => by
    show (wordBall S n ∪ {x | ∃ y ∈ wordBall S n, ∃ s ∈ S, x = y * s ∨ x = y * s⁻¹}).Finite
    refine (wordBall_finite S n).union ?_
    have hsub : {x | ∃ y ∈ wordBall S n, ∃ s ∈ S, x = y * s ∨ x = y * s⁻¹} ⊆
        ⋃ y ∈ wordBall S n, ⋃ s ∈ (S : Set Γ), ({y * s, y * s⁻¹} : Set Γ) := by
      rintro x ⟨y, hy, s, hs, hx⟩
      simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
        exists_prop]
      exact ⟨y, hy, s, hs, hx⟩
    exact Set.Finite.subset ((wordBall_finite S n).biUnion fun y _ =>
      S.finite_toSet.biUnion fun s _ => (Set.finite_singleton (y * s⁻¹)).insert (y * s)) hsub

/-- **Asymptotic residual finiteness** (Arzhantseva, Definition 9, with residually finite target
groups and the discrete metric): for every radius `n` there are a finite generating set `S` and a map
`π` to a residually finite group that is multiplicative and injective on the ball of radius `n` of
`S`.  The generating set may depend on `n`. -/
def IsAsymptoticallyResiduallyFinite (Γ : Type*) [Group Γ] : Prop :=
  ∀ n : ℕ, ∃ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ ∧
    ∃ (F : Type) (_ : Group F), Group.ResiduallyFinite F ∧ ∃ π : Γ → F,
      (∀ g ∈ wordBall S n, ∀ h ∈ wordBall S n, g * h ∈ wordBall S n → π (g * h) = π g * π h) ∧
        Set.InjOn π (wordBall S n)

/-- **A finitely generated LEF group is asymptotically residually finite**, with one generating set
for every radius: the ball of radius `n` is a finite test set for LEF. -/
theorem isAsymptoticallyResiduallyFinite_of_isLEF {Γ : Type*} [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsLEF Γ) : IsAsymptoticallyResiduallyFinite Γ := by
  obtain ⟨S, hS⟩ := hfg.out
  intro n
  obtain ⟨m, f, hinj, hmul⟩ := hΓ (wordBall_finite S n).toFinset
  have hinj' : Set.InjOn f (wordBall S n) := by
    simpa only [Set.Finite.coe_toFinset] using hinj
  refine ⟨S, hS, Equiv.Perm (Fin m), inferInstance, inferInstance, f, ?_, hinj'⟩
  intro g hg h hh _
  exact hmul.map_mul g ((wordBall_finite S n).mem_toFinset.2 hg) h
    ((wordBall_finite S n).mem_toFinset.2 hh)

/-- **A finitely generated residually finite group is asymptotically residually finite**
(Arzhantseva, Examples 10): take `π = id`. -/
theorem isAsymptoticallyResiduallyFinite_of_residuallyFinite {Γ : Type} [Group Γ]
    [Group.ResiduallyFinite Γ] (hfg : Group.FG Γ) : IsAsymptoticallyResiduallyFinite Γ := by
  obtain ⟨S, hS⟩ := hfg.out
  exact fun _ => ⟨S, hS, Γ, inferInstance, inferInstance, id, fun _ _ _ _ _ => rfl,
    Set.injOn_id _⟩

/-- **tex l.64–66, the existence clause**: there is an infinite, finitely generated, simple group
with property (T) that is asymptotically residually finite, namely `G_X` at the Toeplitz subshift. -/
theorem manuscriptSentence_infiniteSimpleKazhdanAsymptoticallyResiduallyFinite :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsAsymptoticallyResiduallyFinite E := by
  obtain ⟨hinf, hfg, hsimple, hT, -, hlef, -, -⟩ :=
    printedSimpleKazhdanSoficMain Bool toeplitzSubshift toeplitzSubshift_infinite
      toeplitzSubshift_isMinimal 3 le_rfl
  exact ⟨G toeplitzSubshift, inferInstance, hinf, hfg, hsimple, hT,
    isAsymptoticallyResiduallyFinite_of_isLEF hfg hlef⟩

/-- **tex l.63–66** (census `aaf5fe1a98c3`), the mathematics of the sentence: an infinite simple
Kazhdan group that is asymptotically residually finite exists, and for finitely generated groups
asymptotic residual finiteness is implied by LEF and by residual finiteness. -/
theorem manuscriptSentence_arzhantsevaAsymptoticallyResiduallyFinite :
    (∃ (E : Type) (_ : Group E), Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsAsymptoticallyResiduallyFinite E) ∧
    (∀ (Γ : Type) [Group Γ], Group.FG Γ → IsLEF Γ → IsAsymptoticallyResiduallyFinite Γ) ∧
    (∀ (Γ : Type) [Group Γ] [Group.ResiduallyFinite Γ], Group.FG Γ →
      IsAsymptoticallyResiduallyFinite Γ) :=
  ⟨manuscriptSentence_infiniteSimpleKazhdanAsymptoticallyResiduallyFinite,
    fun _ _ hfg hΓ => isAsymptoticallyResiduallyFinite_of_isLEF hfg hΓ,
    fun _ _ _ hfg => isAsymptoticallyResiduallyFinite_of_residuallyFinite hfg⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.wordBall_finite
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.isAsymptoticallyResiduallyFinite_of_isLEF
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.isAsymptoticallyResiduallyFinite_of_residuallyFinite
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_infiniteSimpleKazhdanAsymptoticallyResiduallyFinite
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_arzhantsevaAsymptoticallyResiduallyFinite
