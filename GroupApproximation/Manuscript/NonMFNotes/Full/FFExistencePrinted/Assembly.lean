import GroupApproximation.Manuscript.NonMFNotes.Full.FFExistence.LeavittSquare
import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `rem:ff-realization`, first sentence: assembly from the small-cancellation quotient

Manuscript `non_mf_group_notes.tex`, Remark `rem:ff-realization` (l.2818):

> The construction of [FFF, §2] gives a finitely presented torsion-free
> property-(T) group `P` containing `P₁ × P₂ × S`, where `Pᵢ ≅ P` and `S` is
> finitely presented, simple, and torsion-free.

The construction of [FFF, §2] (arXiv:2608.02025; the quotient step is
Fournier-Facio arXiv:2512.09180, Proposition 2.3, with Osin's Theorem 2.4(5))
has three steps:

1. `H₀` is a torsion-free hyperbolic group with property (T)
   (Kotowski-Ollivier; closed on main as `Hyperbolic.sharpExistence_closed`).
2. `U` is a universal finitely presented torsion-free group (Chiodo
   arXiv:1107.1489, Theorem 3.10; closed on main as
   `Manuscript.NonMF.TheoremC.chiodo`).
3. Small cancellation over `(U * H₀, U)` gives a finitely presented
   torsion-free quotient `P` of `H₀` with `U ↪ P`.

This file proves everything *after* step 3, with no binders, for every
concrete quotient `p : H₀ ↠ P` with embedding `e : U ↪ P`:

* `P` has (T), because it is a quotient of `H₀`.
* `P` is universal, because `U ↪ P`.
* `S := W` is the Hyde-Lodha group, which is finitely presented, torsion-free
  and simple (`HydeLodha.finitelyPresentedInfiniteSimple_closed`).
* `P × P × W` is finitely presented and torsion-free, so it embeds in `P`.

The results are:

* `ffPrintedExistence_of_smallCancellationQuotient`: the printed sentence,
  `NN08b.FFPrintedExistenceStatement`.
* `ffMinimalExistence_of_smallCancellationQuotient`: the form consumed by
  `NN08.remFFRealization`, `NN08b.FFMinimalExistenceStatement`.
* `ffMinimalExistence_of_datum`: the minimal existence from any finitely
  presented Kazhdan nontrivial `P` carrying a datum. This is also the Leavitt
  route, applied to `NN08b.leavittProductDatum`.

The quotient of step 3 is `TheoremC.FournierFacioQuotientStatement`, proved
on main over the relative Greendlinger leaf
(`TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger`).
The closed targets `ffPrintedExistence` and `ffMinimalExistence` are one
application of this file each, once lane GL06 lands that leaf.
-/

namespace GroupApproximation.Full.NN08c

universe w

section Datum

variable {P S : Type} [Group P] [Group S]

/-- A group carrying a datum `P × P × S ↪ P` with `S` nontrivial is
nontrivial (`rem:ff-realization`, `non_mf_group_notes.tex` l.2818: the mark
`a ∈ P₂ ∖ {1}` needs `P ≠ 1`). -/
theorem nontrivial_of_productDatum [Nontrivial S] (D : NN08.ProductDatum P S) :
    Nontrivial P := by
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  refine nontrivial_of_ne (D.emb (1, 1, s)) 1 ?_
  intro h
  apply hs
  have hemb : D.emb (1, 1, s) = D.emb 1 := by
    rw [h, map_one]
  have hprod : ((1, 1, s) : P × P × S) = 1 := D.emb_injective hemb
  exact (Prod.mk_eq_one.mp (Prod.mk_eq_one.mp hprod).2).2

/-- **`rem:ff-realization`, minimal existence, from a datum**
(`non_mf_group_notes.tex` l.2818).

Let `P` be finitely presented, Kazhdan and nontrivial, and let
`D : P × P × S ↪ P` be a datum. Take `α := D.factorOne`, whose image is `P₁`,
and a mark `a ∈ P₂ ∖ {1}`. -/
theorem ffMinimalExistence_of_datum [Nontrivial P]
    (hPfp : Group.IsFinitelyPresented P) (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (D : NN08.ProductDatum P S) : NN08b.FFMinimalExistenceStatement.{w} :=
  ⟨P, S, inferInstance, inferInstance, hPfp, hT, D, D.factorOne,
    D.factorOne_injective, rfl, NN08b.ProductDatum.exists_mark D⟩

/-- **`rem:ff-realization`, printed existence, from a datum**
(`non_mf_group_notes.tex` l.2818). -/
theorem ffPrintedExistence_of_datum (hPfp : Group.IsFinitelyPresented P)
    (hPtf : IsPowerTorsionFree P) (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (hSfp : Group.IsFinitelyPresented S) (hSsimple : IsSimpleGroup S)
    (hStf : IsPowerTorsionFree S) (D : NN08.ProductDatum P S) :
    NN08b.FFPrintedExistenceStatement.{w} :=
  ⟨P, S, inferInstance, inferInstance, hPfp, hPtf, hT, hSfp, hSsimple, hStf, ⟨D⟩⟩

end Datum

section Universal

variable {U P : Type} [Group U] [Group P]

/-- **`P₁ × P₂ × S ≤ P` with `S` the Hyde-Lodha group**
(`rem:ff-realization`, `non_mf_group_notes.tex` l.2818; [FFF, §2], "by
universality").

Suppose `P` is finitely presented and torsion-free, and receives an embedding
of a universal finitely presented torsion-free group `U`. Then `P` is itself
universal. Let `W` be the finitely presented, torsion-free, simple Hyde-Lodha
group. The group `P × P × W` is finitely presented and torsion-free, so it
embeds in `P`. -/
theorem exists_productDatum_of_universalEmbedding
    (hU : ChiodoBelegradek.ContainsEveryFPTorsionFree U)
    (hPfp : Group.IsFinitelyPresented P) (hPtf : IsPowerTorsionFree P)
    (e : U →* P) (he : Function.Injective e) :
    ∃ (S : Type) (_ : Group S), Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧
      IsPowerTorsionFree S ∧ Nonempty (NN08.ProductDatum P S) := by
  haveI : Group.IsFinitelyPresented P := hPfp
  obtain ⟨W, _, hWfp, hWtf, hWsimple, -⟩ :=
    HydeLodha.finitelyPresentedInfiniteSimple_closed
  haveI : Group.IsFinitelyPresented W := hWfp
  obtain ⟨f, hf⟩ := Manuscript.NonMF.TheoremC.exists_injective_prodProdWitness hPtf hWtf
    (Manuscript.NonMF.TheoremC.containsEveryFPTorsionFree_of_fournierFacioQuotient hU e he)
  exact ⟨W, inferInstance, hWfp, hWsimple, hWtf, ⟨⟨f, hf⟩⟩⟩

end Universal

section Quotient

variable {H₀ U P : Type} [Group H₀] [Group U] [Group P]

/-- The Kazhdan clause in the complex form of `NN08b`: a quotient of a
Kazhdan group is Kazhdan ([FFF, §2], "consequently `P` has property (T)"). -/
theorem kazhdanComplex_of_surjective (hH₀ : HasKazhdanPropertyT.{0, 0} H₀)
    (p : H₀ →* P) (hp : Function.Surjective p) : HasKazhdanPropertyTComplex.{0, w} P :=
  (hasKazhdanPropertyT_iff_textbook.{0, w}).mp
    (Manuscript.NonMF.TheoremC.kazhdan_of_fournierFacioQuotient hH₀ p hp)

/-- **`rem:ff-realization`, first sentence as printed, from the
small-cancellation quotient** (`non_mf_group_notes.tex` l.2818; [FFF, §2]).

Assume `H₀` is Kazhdan, `U` is universal finitely presented torsion-free, and
`P` is a finitely presented torsion-free quotient `p : H₀ ↠ P` with
`e : U ↪ P`. Then `P` and the Hyde-Lodha group `S` realize the printed
sentence. -/
theorem ffPrintedExistence_of_smallCancellationQuotient
    (hH₀ : HasKazhdanPropertyT.{0, 0} H₀)
    (hU : ChiodoBelegradek.ContainsEveryFPTorsionFree U)
    (hPfp : Group.IsFinitelyPresented P) (hPtf : IsPowerTorsionFree P)
    (p : H₀ →* P) (hp : Function.Surjective p)
    (e : U →* P) (he : Function.Injective e) :
    NN08b.FFPrintedExistenceStatement.{w} := by
  obtain ⟨S, _, hSfp, hSsimple, hStf, ⟨D⟩⟩ :=
    exists_productDatum_of_universalEmbedding hU hPfp hPtf e he
  exact ffPrintedExistence_of_datum hPfp hPtf (kazhdanComplex_of_surjective hH₀ p hp)
    hSfp hSsimple hStf D

/-- **`rem:ff-realization`, the existence consumed by `NN08.remFFRealization`,
from the small-cancellation quotient** (`non_mf_group_notes.tex` l.2818;
[FFF, §2]). -/
theorem ffMinimalExistence_of_smallCancellationQuotient
    (hH₀ : HasKazhdanPropertyT.{0, 0} H₀)
    (hU : ChiodoBelegradek.ContainsEveryFPTorsionFree U)
    (hPfp : Group.IsFinitelyPresented P) (hPtf : IsPowerTorsionFree P)
    (p : H₀ →* P) (hp : Function.Surjective p)
    (e : U →* P) (he : Function.Injective e) :
    NN08b.FFMinimalExistenceStatement.{w} := by
  obtain ⟨S, _, -, hSsimple, -, ⟨D⟩⟩ :=
    exists_productDatum_of_universalEmbedding hU hPfp hPtf e he
  haveI : Nontrivial S := @IsSimpleGroup.toNontrivial _ _ hSsimple
  haveI : Nontrivial P := nontrivial_of_productDatum D
  exact ffMinimalExistence_of_datum hPfp (kazhdanComplex_of_surjective hH₀ p hp) D

end Quotient

#audit_axioms GroupApproximation.Full.NN08c.nontrivial_of_productDatum
#audit_axioms GroupApproximation.Full.NN08c.ffMinimalExistence_of_datum
#audit_axioms GroupApproximation.Full.NN08c.exists_productDatum_of_universalEmbedding
#audit_axioms GroupApproximation.Full.NN08c.ffPrintedExistence_of_smallCancellationQuotient
#audit_axioms GroupApproximation.Full.NN08c.ffMinimalExistence_of_smallCancellationQuotient

end GroupApproximation.Full.NN08c
