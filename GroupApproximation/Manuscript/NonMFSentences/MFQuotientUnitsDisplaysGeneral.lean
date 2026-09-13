import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsSteinberg
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsOffLastCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientCanonicalKOne
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: two sentences at the printed generality

`non_mf_groups_exist.tex`, Theorem `thm:mf-quotient-units` and its proof.

## The Steinberg displays over the decomposition of item (a)

> for distinct `i,j ≤ m-1`,
> `e_{im}(x)=[e_{ij}(1),e_{jm}(x)]`, `e_{mj}(x)=[e_{mi}(x),e_{ij}(1)]`
> are products of an element of `EL_{m-1}(T)` and a conjugate of its inverse, so they lie
> in the normal subgroup `N` as well.

The closed carrier on main, `MFQuotientUnitsSteinberg.PrintedSteinbergDisplaysInRadical`,
takes an idempotent family whose blocks off `last` are each equivalent to `1`.  Item (a) as
printed provides less: orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`, whose
blocks `e_1, …, e_{m-1}` are pairwise equivalent, and `e_m` equivalent to an idempotent
`f ≤ e_1`.  `PrintedSteinbergDisplaysAtItemA` states the sentence over exactly that
decomposition (with `m + 1` blocks, `m ≥ 3`, as in
`MFQuotientUnitsOffLastCorner.PrintedOffLastCorner`):

* the preceding clause, "they lie in `N` by `eq:corner-units`", is
  `MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner`, which also supplies the
  corner isomorphism `θ : M_{m-1}(T) ≃ (1-e_m)R(1-e_m)`;
* the displays and the product decomposition are
  `MFQuotientUnitsSteinberg.lastColumnDisplay` and `lastRowDisplay`, whose hypotheses are the
  printed ones;
* the unit `g = e_{ij}(1)` is recorded as the image `1 - P + θ(A)` of an element `A` of
  `EL_{m-1}(T)`, which is the printed "an element of `EL_{m-1}(T)`".

## The appositive of the statement

> Then every homomorphism from `GL_n(R)` to an MF group factors uniquely through the
> canonical map `GL_n(R) → K_1(R)`, and `K_1(R)`, a countable abelian group, is MF.

`MFQuotientUnitsKOne.PrintedCanonicalKOne` carries the factorization and that `K_1(R)` is MF.
The appositive "a countable abelian group" is carried there only by instances
(`AlgebraicK.algebraicKOneCommGroup`, `AlgebraicK.algebraicKOne_countable`).
`PrintedKOneCountableAbelianMF` states every clause of the sentence as a proposition.
-/

namespace GroupApproximation
namespace MFQuotientUnitsDisplaysGeneral

open MFQuotientUnits
open MFQuotientUnitsKOne
open AlgebraicK

/-- **Printed sentence (proof of `thm:mf-quotient-units`), closed, over item (a).**

> for distinct `i,j ≤ m-1`, `e_{im}(x)=[e_{ij}(1),e_{jm}(x)]` and
> `e_{mj}(x)=[e_{mi}(x),e_{ij}(1)]` are products of an element of `EL_{m-1}(T)` and a
> conjugate of its inverse, so they lie in the normal subgroup `N` as well.

For a countable purely infinite simple ring `R` and a decomposition as in item (a) (blocks off
`last` pairwise equivalent, `e_last` equivalent to `f ≤ e_{i₀}`), with `N = Rad_MF(Rˣ)` and the
corner isomorphism `θ` onto `(1 - e_last)R(1 - e_last)`: every last-column root and every
last-row root `w = 1 + x` is the printed commutator with the unit `g = e_{ij}(1)`, `g` is the
image of an element of `EL_{m-1}(T)`, `w` is the printed product of `g` and a conjugate of its
inverse, and both lie in `N`. -/
def PrintedSteinbergDisplaysAtItemA : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ), 3 ≤ m → ∀ (e : Fin (m + 1) → R) (hidem : ∀ i, IsIdempotentElem (e i)),
      (∀ i j : Fin (m + 1), i ≠ j → e i * e j = 0) → (∑ i, e i = 1) →
      ∀ i₀ last : Fin (m + 1), i₀ ≠ last →
        (∀ i j : Fin (m + 1), i ≠ last → j ≠ last → IsEquivalentIdempotent R (e i) (e j)) →
        ∀ (f : R), IsIdempotentElem f → IdempotentLE f (e i₀) →
          IsEquivalentIdempotent R (e last) f →
          ∃ (P : R) (hP : IsIdempotentElem P)
            (θ : Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀)) ≃+* Corner R P hP),
            P = 1 - e last ∧
            ∀ i j : Fin (m + 1), i ≠ j → i ≠ last → j ≠ last → ∀ (x : R) (w : Rˣ),
              (w : R) = 1 + x →
              ((e i * x = x ∧ x * e last = x) →
                ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
                  (∃ A ∈ elementaryGroup (Fin m) (Corner R (e i₀) (hidem i₀)),
                    (g : R) = 1 - P + ((θ (A : Matrix (Fin m) (Fin m)
                      (Corner R (e i₀) (hidem i₀))) : Corner R P hP) : R)) ∧
                  (∃ b : R, e j * b = b ∧ b * e last = b ∧ (h : R) = 1 + b) ∧
                  w = g * h * g⁻¹ * h⁻¹ ∧ w = g * (h * g⁻¹ * h⁻¹) ∧
                  g ∈ mfHomKernel Rˣ ∧ w ∈ mfHomKernel Rˣ) ∧
              ((e last * x = x ∧ x * e j = x) →
                ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
                  (∃ A ∈ elementaryGroup (Fin m) (Corner R (e i₀) (hidem i₀)),
                    (g : R) = 1 - P + ((θ (A : Matrix (Fin m) (Fin m)
                      (Corner R (e i₀) (hidem i₀))) : Corner R P hP) : R)) ∧
                  (∃ b : R, e last * b = b ∧ b * e i = b ∧ (h : R) = 1 + b) ∧
                  w = h * g * h⁻¹ * g⁻¹ ∧ w = (h * g * h⁻¹) * g⁻¹ ∧
                  g ∈ mfHomKernel Rˣ ∧ w ∈ mfHomKernel Rˣ)

/-- The printed route: the clause before the displays gives `EL_{m-1}(T) ≤ N` at item (a)'s
generality (`manuscriptSentence_offLastCorner`), and the displays follow from it
(`lastColumnDisplay`, `lastRowDisplay`). -/
theorem manuscriptSentence_steinbergDisplaysAtItemA : PrintedSteinbergDisplaysAtItemA := by
  intro R _ _ hR m hm e hidem horth hsum i₀ last hne hpair f hfi hfle hlast
  obtain ⟨P, hP, θ, hPe, hroots⟩ :=
    MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner R hR m hm e hidem horth
      hsum i₀ last hne hpair f hfi hfle hlast
  have hEL : MFQuotientUnitsSteinberg.OffLastRootsIn (mfHomKernel Rˣ) e last := by
    intro p q hpq hpl hql a hpa haq g hg
    obtain ⟨_, -, -, hmem⟩ := hroots p q hpq hpl hql a hpa haq g hg
    exact hmem
  refine ⟨P, hP, θ, hPe, fun i j hij hil hjl x w hw => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨g, h, ⟨a, hia, haj, hga⟩, hb, hcomm, hgN, hsplit, hwN⟩ :=
      MFQuotientUnitsSteinberg.lastColumnDisplay (mfHomKernel Rˣ) hidem horth hij hil hjl
        (hpair i j hil hjl) hEL hx.1 hx.2 w hw
    obtain ⟨A, hA, hgA, -⟩ := hroots i j hij hil hjl a hia haj g hga
    exact ⟨g, h, ⟨a, hia, haj, hga⟩, ⟨A, hA, hgA⟩, hb, hcomm, hsplit, hgN, hwN⟩
  · obtain ⟨g, h, ⟨a, hia, haj, hga⟩, hb, hcomm, hgN, hsplit, hwN⟩ :=
      MFQuotientUnitsSteinberg.lastRowDisplay (mfHomKernel Rˣ) hidem horth hij hil hjl
        (hpair i j hil hjl) hEL hx.1 hx.2 w hw
    obtain ⟨A, hA, hgA, -⟩ := hroots i j hij hil hjl a hia haj g hga
    exact ⟨g, h, ⟨a, hia, haj, hga⟩, ⟨A, hA, hgA⟩, hb, hcomm, hsplit, hgN, hwN⟩

/-- **Printed sentence (statement of `thm:mf-quotient-units`), every clause.**

> Then every homomorphism from `GL_n(R)` to an MF group factors uniquely through the
> canonical map `GL_n(R) → K_1(R)`, and `K_1(R)`, a countable abelian group, is MF. -/
def PrintedKOneCountableAbelianMF : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (n : ℕ), 1 ≤ n →
      (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : (Matrix (Fin n) (Fin n) R)ˣ →* M,
          ∃! g : AlgebraicKOne R →* M, g.comp (matrixKappa R n) = f) ∧
      Countable (AlgebraicKOne R) ∧
      (∀ x y : AlgebraicKOne R, x * y = y * x) ∧
      IsOperatorMF (AlgebraicKOne R)

theorem manuscriptSentence_kOneCountableAbelianMF : PrintedKOneCountableAbelianMF := by
  intro R _ _ hR n hn
  obtain ⟨-, -, -, -, hMF, hfac⟩ := manuscriptCanonicalKOne R hR n hn
  exact ⟨hfac, inferInstance, fun x y => mul_comm x y, hMF⟩

end MFQuotientUnitsDisplaysGeneral
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsDisplaysGeneral.manuscriptSentence_steinbergDisplaysAtItemA
#audit_closed_axioms GroupApproximation.MFQuotientUnitsDisplaysGeneral.manuscriptSentence_kOneCountableAbelianMF
