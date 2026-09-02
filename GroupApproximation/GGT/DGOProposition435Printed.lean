import GroupApproximation.GGT.WPDElementaryEmbedding
import GroupApproximation.GGT.HullSCLemma44JointRelabel

/-!
# Proposition 4.35 in its printed direction, and the two subfamily models

`DGOProposition435.lean` records that the direction Hull's Lemma 4.4 needs --
keeping the original family beside the auxiliary closures -- is *not* the
printed one.  The printed direction is the one the *other* half of Lemma 4.4
needs, and this file states it.

Dahmani--Guirardel--Osin, Proposition 4.35 (`\label{transitive}` at `HE.tex:976`
of arXiv `1111.7048`), transcribed:

> Let `G` be a group, `{H_λ}_{λ∈Λ}` a **finite** collection of subgroups of
> `G`, `X ⊆ G`, `Y_λ ⊆ H_λ`.  Suppose that `{H_λ} ↪_h (G, X)` and, for each
> `λ`, there is a collection of subgroups `{K_{λμ}}_{μ∈M_λ}` of `H_λ` such
> that `{K_{λμ}} ↪_h (H_λ, Y_λ)`.  Then `⋃_λ {K_{λμ}} ↪_h (G, Z)`, where
> `Z = X ∪ (⋃_λ Y_λ)`.

## Why this is the mechanism for the original family

Osin uses exactly this to pass from a filling quotient's peripheral family to
a smaller one.  In *Small cancellations over relatively hyperbolic groups*
(arXiv `math/0411039`), the proof of Theorem `glue` enlarges the family by two
elementary closures, fills over the enlarged alphabet, gets the quotient
relatively hyperbolic with respect to the images of everything, and then drops
the elementary members: "As any elementary group is hyperbolic, `G_1` is also
hyperbolic relative to `{η(H_λ)}` according to Lemma `exhyp`"
(`embed-final.tex:1956-1959`), where `exhyp` (`:1909-1914`) is the special case
of Theorem 2.40 of Osin's Memoir for finitely generated hyperbolic members.

The two subfamily choices that realise it are modelled here.

* To KEEP a member `H_λ`, take the one-member subfamily `{H_λ}` of `H_λ` over
  the empty relative generating set: `selfRelGenSet`.  Its relative Cayley
  graph is bounded, and no path avoiding the member's own letters is nonempty,
  so its relative ball is `{1}`.
* To DROP a member `E`, take the empty subfamily over a finite symmetric
  generating set of `E`: `emptySubfamilyRelGenSet`.  Local finiteness is
  vacuous, and hyperbolicity of its Cayley graph is exactly the hypothesis that
  `E` is a hyperbolic group.  The members dropped in the application are the
  images of the cyclic elementary closures.

The base of the conclusion is then `X` enlarged by finitely many generators of
the dropped members, so it stays finite, which is what relative hyperbolicity
demands and what pushing the dropped members into the base would destroy.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The printed statement -/

/-- **Dahmani--Guirardel--Osin, Proposition 4.35**, printed direction: the
family is removed and replaced by subfamilies of its members. -/
def DGOProposition435PrintedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} [Finite Lambda]
    (D : RelGenSet G Lambda) {M : Lambda → Type v}
    (E : ∀ lam : Lambda, RelGenSet (D.fam lam) (M lam)),
    D.IsHyperbolicallyEmbedded →
    (∀ lam : Lambda, (E lam).IsHyperbolicallyEmbedded) →
      ∃ Z : RelGenSet G ((lam : Lambda) × M lam),
        Z.base = D.base ∪
            (⋃ lam : Lambda, (D.fam lam).subtype '' (E lam).base) ∧
          (∀ p : (lam : Lambda) × M lam,
            Z.fam p = ((E p.1).fam p.2).map (D.fam p.1).subtype) ∧
            Z.IsHyperbolicallyEmbedded

/-! ## Keeping a member: the group in itself over the empty base -/

/-- The one-member subfamily of a group by itself, over the empty relative
generating set. -/
def selfRelGenSet (H : Type u) [Group H] : RelGenSet H Unit where
  base := ∅
  fam := fun _ => ⊤
  symmetricGenerating := by
    constructor
    · intro x _
      exact Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top x⁻¹⟩)
    · rw [eq_top_iff]
      intro x _
      exact Subgroup.subset_closure
        (Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top x⟩))

theorem selfRelGenSet_alphabet_carrier (H : Type u) [Group H] :
    (selfRelGenSet H).alphabet.carrier = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    exact Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top x⟩)

/-- No nonempty path avoids the only member, because every letter is one of its
letters and every vertex lies in it.  So the relative ball is trivial. -/
theorem selfRelGenSet_relBall (H : Type u) [Group H] (n : ℕ) :
    (selfRelGenSet H).relBall () n = ({1} : Set H) := by
  ext h
  constructor
  · rintro ⟨-, word, hletters, hval, havoid, -⟩
    cases word with
    | nil =>
        rw [Set.mem_singleton_iff, ← hval]
        rfl
    | cons a t =>
        exfalso
        cases a with
        | base x =>
            have hx : x ∈ (∅ : Set H) := hletters (RelLetter.base x) (by simp)
            exact absurd hx (Set.notMem_empty x)
        | comp u y =>
            cases u
            exact havoid.1 ⟨rfl, Subgroup.mem_top 1⟩
  · intro hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact ⟨Subgroup.mem_top 1, [], by simp, rfl, trivial, by simp⟩

/-- **Keeping a member.**  A group is hyperbolically embedded in itself over
the empty relative generating set. -/
theorem selfRelGenSet_isHyperbolicallyEmbedded (H : Type u) [Group H] :
    (selfRelGenSet H).IsHyperbolicallyEmbedded := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · refine isHyperbolicSpace_of_bounded ?_
    intro x y
    have hmem : ((Cayley.val x)⁻¹ * Cayley.val y : H) ∈
        (selfRelGenSet H).alphabet.carrier := by
      rw [selfRelGenSet_alphabet_carrier H]
      exact Set.mem_univ _
    have hnorm : WordMetric.wordNorm (selfRelGenSet H).alphabet.carrier
        ((Cayley.val x)⁻¹ * Cayley.val y) ≤ 1 :=
      WordMetric.wordNorm_le_one_of_mem hmem
    rw [Cayley.dist_eq]
    exact_mod_cast hnorm
  · intro u n
    cases u
    rw [selfRelGenSet_relBall H n]
    exact Set.finite_singleton 1

/-! ## Dropping a member: the empty subfamily of a hyperbolic group -/

/-- The empty subfamily of a group over a symmetric generating set. -/
def emptySubfamilyRelGenSet {E : Type u} [Group E] (Y : Set E)
    (hY : IsSymmetricGeneratingSet Y) : RelGenSet E Empty where
  base := Y
  fam := Empty.elim
  symmetricGenerating := by
    have hunion : Y ∪ (⋃ e : Empty, ((Empty.elim e : Subgroup E) : Set E)) =
        Y := by
      rw [Set.iUnion_of_empty, Set.union_empty]
    rw [hunion]
    exact hY

theorem emptySubfamilyRelGenSet_alphabet_carrier {E : Type u} [Group E]
    (Y : Set E) (hY : IsSymmetricGeneratingSet Y) :
    (emptySubfamilyRelGenSet Y hY).alphabet.carrier = Y := by
  show Y ∪ (⋃ e : Empty, ((Empty.elim e : Subgroup E) : Set E)) = Y
  rw [Set.iUnion_of_empty, Set.union_empty]

/-- **Dropping a member.**  The empty subfamily is hyperbolically embedded in a
group over any symmetric generating set whose Cayley graph is hyperbolic: local
finiteness is vacuous.  For a cyclic group and a generator this is the case
Osin's `exhyp` uses. -/
theorem emptySubfamilyRelGenSet_isHyperbolicallyEmbedded {E : Type u} [Group E]
    (Y : Set E) (hY : IsSymmetricGeneratingSet Y)
    (hhyp : ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (emptySubfamilyRelGenSet Y hY).alphabet)) :
    (emptySubfamilyRelGenSet Y hY).IsHyperbolicallyEmbedded :=
  ⟨hhyp, fun e => Empty.elim e⟩


/-! ## Dropping the elementary members of a filling quotient

Osin's step, in the filling setting: the quotient is relatively hyperbolic with
respect to the images of the whole joint family, and the elementary members are
then dropped because they are hyperbolic with a finite generating set.  The
base of the result is the joint base together with finitely many generators, so
it stays finite, which is what relative hyperbolicity asks for.
-/

section Drop

open GroupApproximation.HullSC

variable {G : Type u} [Group G] {Lambda : Type w} {k : ℕ}

/-- One member is kept, indexed by `Unit`; one is dropped, indexed by
`Empty`. -/
def dropIndex : Sum Lambda (AuxiliaryPeripheralIndex k) → Type :=
  Sum.elim (fun _ => Unit) (fun _ => Empty)

variable {Q : Type u} [Group Q]

/-- The subfamily choice: each original member keeps itself over the empty
base, each selected member is replaced by the empty family over a finite
generating set. -/
def dropSubfamilies (J : RelGenSet Q (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (E : ∀ i : AuxiliaryPeripheralIndex k,
      RelGenSet (J.fam (Sum.inr i)) Empty) :
    ∀ s, RelGenSet (J.fam s) (dropIndex s) := fun s =>
  Sum.rec (motive := fun s => RelGenSet (J.fam s) (dropIndex s))
    (fun l => selfRelGenSet (J.fam (Sum.inl l))) (fun i => E i) s

/-- The kept members are indexed by the original index. -/
def dropEquiv :
    Lambda ≃ ((s : Sum Lambda (AuxiliaryPeripheralIndex k)) × dropIndex s) where
  toFun l := ⟨Sum.inl l, ()⟩
  invFun p :=
    Sum.rec (motive := fun s => dropIndex s → Lambda) (fun l _ => l)
      (fun _ e => Empty.elim e) p.1 p.2
  left_inv l := rfl
  right_inv p := by
    obtain ⟨s, m⟩ := p
    cases s with
    | inl l =>
        cases m
        rfl
    | inr i => exact Empty.elim m

/-- **The images of the original peripheral family are relatively hyperbolic in
the filling quotient.**

This is the step Osin performs at `embed-final.tex:1956-1959`: the joint image
family is relatively hyperbolic, and the elementary members drop out by the
printed Proposition 4.35, since each is hyperbolic with a finite generating
set.  No record about the original family is needed, because relative
hyperbolicity only asks for SOME finite relative generating set. -/
theorem isRelativelyHyperbolic_original_of_jointPreservation
    (h435 : DGOProposition435PrintedStatement.{u, 0, w})
    {A : HullGeneratingSet G} {N : Subgroup G} {S : Fin k → Subgroup G}
    {selected : AuxiliaryPeripheralFamily A N S} [Finite Lambda]
    {original : RelGenSet G Lambda} {q : G →* Q}
    (P : QuotientJointPeripheralPreservation q selected original)
    (hfinite : original.base.Finite)
    (E : ∀ i : AuxiliaryPeripheralIndex k,
      RelGenSet (P.rel.fam (Sum.inr i)) Empty)
    (hE : ∀ i, (E i).IsHyperbolicallyEmbedded)
    (hEfinite : ∀ i, (E i).base.Finite) :
    IsRelativelyHyperbolic Q (fun l : Lambda => (original.fam l).map q) := by
  have hsub : ∀ s, (dropSubfamilies P.rel E s).IsHyperbolicallyEmbedded := by
    intro s
    cases s with
    | inl l => exact selfRelGenSet_isHyperbolicallyEmbedded _
    | inr i => exact hE i
  obtain ⟨Z, hZbase, hZfam, hZemb⟩ :=
    h435 P.rel (dropSubfamilies P.rel E) P.embedded hsub
  have hbaseFinite : Z.base.Finite := by
    rw [hZbase]
    refine Set.Finite.union (P.base_finite hfinite) ?_
    refine Set.finite_iUnion ?_
    intro s
    refine Set.Finite.image _ ?_
    cases s with
    | inl l => exact Set.finite_empty
    | inr i => exact hEfinite i
  refine ⟨relGenSetReindex Z dropEquiv, hbaseFinite, ?_,
    relGenSetReindex_isHyperbolicallyEmbedded Z dropEquiv hZemb⟩
  funext l
  show Z.fam (dropEquiv l) = (original.fam l).map q
  rw [hZfam ⟨Sum.inl l, ()⟩]
  show ((⊤ : Subgroup (P.rel.fam (Sum.inl l))).map
    (P.rel.fam (Sum.inl l)).subtype) = (original.fam l).map q
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, P.fam_original l]

end Drop

end RelHyp
end GGT
end GroupApproximation
