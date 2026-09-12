import GroupApproximation.Algebra.PeirceElementaryCornerUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: the reduction to `n = 1`, and the two Steinberg displays

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units`.  Two printed
sentences whose census rows were recorded as `partial`.

## The first sentence of the proof (tex 1230–1232)

> The ring `M_n(R)` is again countable, purely infinite, and simple [AGP, Corollary 1.7],
> and `K_1(M_n(R)) ≅ K_1(R)` by Morita invariance, so it suffices to treat `n = 1`.

`MFQuotientUnitsSentences.manuscriptSentence_matrixRingAgainPurelyInfinite` carries the
three clauses before "so".  The consequence "it suffices to treat `n = 1`" is the
implication from the theorem at `n = 1` to the theorem at every `n ≥ 1` with the printed
`K_1(R)`, and `manuscriptSentence_sufficesRankOne` proves exactly that implication, by
the printed route: apply the `n = 1` statement to the countable purely infinite simple
ring `M_n(R)`, then compose with the Morita isomorphism.

## The two Steinberg displays (tex 1281–1286)

> for distinct `i, j ≤ m-1`,
> `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`,  `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]`
> are products of an element of `EL_{m-1}(T)` and a conjugate of its inverse, so they lie
> in the normal subgroup `N` as well.

Elementary matrices of the twisted matrix ring of item (a) are Peirce units `1 + x` with
`x ∈ e_p R e_q`, `p ≠ q` (`Algebra/PeirceElementaryUnits.lean`), and the printed
commutator convention is `[g, h] = g h g⁻¹ h⁻¹` (tex 156).  `lastColumnDisplay` and
`lastRowDisplay` take the printed hypotheses (orthogonal idempotents, the blocks `i` and
`j` off `last` equivalent) and the conclusion of the preceding clause (`EL_{m-1}(T) ≤ N`,
`OffLastRootsIn`), for an arbitrary normal subgroup `N`, and produce the displays: the
root `x` of the last column (row) is the commutator of the unit `g = e_{ij}(1)`, whose root
is a normalized partial isometry between the blocks `i` and `j`, with a last-column (row)
root `h`; this is `g · (h g⁻¹ h⁻¹)` (respectively `(h g h⁻¹) · g⁻¹`), a product of an element
of `EL_{m-1}(T)` and a conjugate of an inverse, so it lies in `N`.
`manuscriptSentence_steinbergDisplaysInRadical` is the closed statement at `N = Rad_MF(Rˣ)`
for a decomposition whose blocks off `last` are equivalent to `1` (the family item (a)
builds, `peirceBlocks`), where `EL_{m-1}(T) ≤ N` is supplied by
`oneAddIn_cornerUnitSubgroup_of_unitPair` and Theorem `thm:full-defect-ring` in its
rank-two form.  Nothing here is assumed.
-/

namespace GroupApproximation
namespace MFQuotientUnitsSteinberg

open MFQuotientUnits
open MFQuotientUnits.Peirce
open MFQuotientUnitsKOne

/-! ## "so it suffices to treat `n = 1`" -/

/-- **Printed (tex 1231–1232), the consequence "so it suffices to treat `n = 1`".**
The theorem at `n = 1` (`PrintedMFQuotientUnitsKOne`, every clause of the printed
statement) implies the theorem at every `n ≥ 1` with the printed `K_1(R)`
(`PrintedMFQuotientUnitsKOneAtBaseRing`). -/
def PrintedSufficesRankOne : Prop :=
  PrintedMFQuotientUnitsKOne → PrintedMFQuotientUnitsKOneAtBaseRing

/-- The printed reduction: the `n = 1` statement at the countable purely infinite simple
ring `M_n(R)` [AGP, Corollary 1.7, proved as `agpMatrixReduction`], composed with Morita
invariance `K_1(M_n(R)) ≅ K_1(R)` (`moritaKOne`). -/
theorem manuscriptSentence_sufficesRankOne : PrintedSufficesRankOne := by
  intro h1 R _ _ hR n hn
  haveI : Countable (Matrix (Fin n) (Fin n) R) :=
    CountableMatrixUnits.countable_matrix (A := R) n
  obtain ⟨-, -, hcomm, ⟨e⟩⟩ :=
    h1 (Matrix (Fin n) (Fin n) R) (agpMatrixReduction R hR n hn)
  obtain ⟨m⟩ := moritaKOne R n hn
  exact ⟨hcomm, ⟨e.trans m⟩⟩

/-- **Printed sentence (tex 1230–1232), all of it.**

> The ring `M_n(R)` is again countable, purely infinite, and simple, and
> `K_1(M_n(R)) ≅ K_1(R)` by Morita invariance, so it suffices to treat `n = 1`. -/
def PrintedReductionToRankOne : Prop :=
  (∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
      ∀ n : ℕ, 1 ≤ n →
        Countable (Matrix (Fin n) (Fin n) R) ∧
          IsPurelyInfiniteSimpleRing (Matrix (Fin n) (Fin n) R) ∧
          Nonempty (AlgebraicK.AlgebraicKOne (Matrix (Fin n) (Fin n) R)
            ≃* AlgebraicK.AlgebraicKOne R)) ∧
    PrintedSufficesRankOne

theorem manuscriptSentence_reductionToRankOne : PrintedReductionToRankOne := by
  refine ⟨?_, manuscriptSentence_sufficesRankOne⟩
  intro R _ _ hR n hn
  exact MFQuotientUnitsSentences.manuscriptSentence_matrixRingAgainPurelyInfinite R hR n hn

/-! ## The two Steinberg displays -/

/-- The commutator of two square-zero transvections: `[1 + a, 1 + b] = 1 + ab` when
`a² = b² = 0` and `ba = 0`. -/
theorem commutator_squareZeroUnit {R : Type} [Ring R] {a b : R}
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0) :
    ((squareZeroUnit a haa * squareZeroUnit b hbb * (squareZeroUnit a haa)⁻¹ *
        (squareZeroUnit b hbb)⁻¹ : Rˣ) : R) = 1 + a * b := by
  change (1 + a) * (1 + b) * (1 - a) * (1 - b) = 1 + a * b
  have haba : a * b * a = 0 := by rw [mul_assoc, hba, mul_zero]
  have habb : a * b * b = 0 := by rw [mul_assoc, hbb, mul_zero]
  have haab : a * a * b = 0 := by rw [haa, zero_mul]
  have habab : a * b * a * b = 0 := by rw [haba, zero_mul]
  noncomm_ring [haa, hbb, hba, haba, habb, haab, habab]

/-- **The printed `EL_{m-1}(T) ≤ N`**, the conclusion of the clause before the displays
("they lie in `N` by `eq:corner-units`"): every unit `1 + a` whose root `a` sits between
two distinct blocks off `last` lies in `N`. -/
def OffLastRootsIn {R : Type} [Ring R] (N : Subgroup Rˣ) {m : ℕ} (e : Fin m → R)
    (last : Fin m) : Prop :=
  ∀ p q : Fin m, p ≠ q → p ≠ last → q ≠ last → ∀ a : R, e p * a = a → a * e q = a →
    ∀ g : Rˣ, (g : R) = 1 + a → g ∈ N

/-- **The printed display `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`**, for distinct `i, j` off
`last`, and its consequence: the display is `g · (h g⁻¹ h⁻¹)` with `g ∈ EL_{m-1}(T)`, so it
lies in the normal subgroup `N`. -/
theorem lastColumnDisplay {R : Type} [Ring R] (N : Subgroup Rˣ) [hN : N.Normal] {m : ℕ}
    {e : Fin m → R} {last : Fin m} (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    {i j : Fin m} (hij : i ≠ j) (hil : i ≠ last) (hjl : j ≠ last)
    (hequiv : IsEquivalentIdempotent R (e i) (e j)) (hEL : OffLastRootsIn N e last)
    {x : R} (hix : e i * x = x) (hxl : x * e last = x) (w : Rˣ) (hw : (w : R) = 1 + x) :
    ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
      (∃ b : R, e j * b = b ∧ b * e last = b ∧ (h : R) = 1 + b) ∧
      w = g * h * g⁻¹ * h⁻¹ ∧ g ∈ N ∧ w = g * (h * g⁻¹ * h⁻¹) ∧ w ∈ N := by
  obtain ⟨u, v, huv, -, hiu, huj, hjv, -⟩ :=
    exists_normalized_equivalence (hidem i) (hidem j) hequiv
  have hxv : x * v = 0 := by
    calc x * v = (x * e last) * (e j * v) := by rw [hxl, hjv]
      _ = x * (e last * e j) * v := by noncomm_ring
      _ = 0 := by rw [horth last j (Ne.symm hjl)]; simp
  have hxu : x * u = 0 := by
    calc x * u = (x * e last) * (e i * u) := by rw [hxl, hiu]
      _ = x * (e last * e i) * u := by noncomm_ring
      _ = 0 := by rw [horth last i (Ne.symm hil)]; simp
  have haa : u * u = 0 := by
    calc u * u = (u * e j) * (e i * u) := by rw [huj, hiu]
      _ = u * (e j * e i) * u := by noncomm_ring
      _ = 0 := by rw [horth j i (Ne.symm hij)]; simp
  have hbb : (v * x) * (v * x) = 0 := by
    calc (v * x) * (v * x) = v * (x * v) * x := by noncomm_ring
      _ = 0 := by rw [hxv]; simp
  have hba : (v * x) * u = 0 := by rw [mul_assoc, hxu, mul_zero]
  have hab : u * (v * x) = x := by
    calc u * (v * x) = (u * v) * x := by noncomm_ring
      _ = e i * x := by rw [huv]
      _ = x := hix
  have hg : squareZeroUnit u haa ∈ N := hEL i j hij hil hjl u hiu huj _ rfl
  have hcomm : w = squareZeroUnit u haa * squareZeroUnit (v * x) hbb *
      (squareZeroUnit u haa)⁻¹ * (squareZeroUnit (v * x) hbb)⁻¹ := by
    apply Units.ext
    rw [commutator_squareZeroUnit haa hbb hba, hab, hw]
  have hsplit : squareZeroUnit u haa * squareZeroUnit (v * x) hbb *
      (squareZeroUnit u haa)⁻¹ * (squareZeroUnit (v * x) hbb)⁻¹ =
      squareZeroUnit u haa * (squareZeroUnit (v * x) hbb * (squareZeroUnit u haa)⁻¹ *
        (squareZeroUnit (v * x) hbb)⁻¹) := by
    simp only [mul_assoc]
  refine ⟨squareZeroUnit u haa, squareZeroUnit (v * x) hbb, ⟨u, hiu, huj, rfl⟩,
    ⟨v * x, by rw [← mul_assoc, hjv], by rw [mul_assoc, hxl], rfl⟩, hcomm, hg,
    hcomm.trans hsplit, ?_⟩
  rw [hcomm, hsplit]
  exact N.mul_mem hg (hN.conj_mem _ (N.inv_mem hg) _)

/-- **The printed display `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]`**, for distinct `i, j` off
`last`, and its consequence: the display is `(h g h⁻¹) · g⁻¹` with `g ∈ EL_{m-1}(T)`, so it
lies in the normal subgroup `N`. -/
theorem lastRowDisplay {R : Type} [Ring R] (N : Subgroup Rˣ) [hN : N.Normal] {m : ℕ}
    {e : Fin m → R} {last : Fin m} (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    {i j : Fin m} (hij : i ≠ j) (hil : i ≠ last) (hjl : j ≠ last)
    (hequiv : IsEquivalentIdempotent R (e i) (e j)) (hEL : OffLastRootsIn N e last)
    {x : R} (hlx : e last * x = x) (hxj : x * e j = x) (w : Rˣ) (hw : (w : R) = 1 + x) :
    ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
      (∃ b : R, e last * b = b ∧ b * e i = b ∧ (h : R) = 1 + b) ∧
      w = h * g * h⁻¹ * g⁻¹ ∧ g ∈ N ∧ w = (h * g * h⁻¹) * g⁻¹ ∧ w ∈ N := by
  obtain ⟨u, v, -, hvu, hiu, huj, -, hvi⟩ :=
    exists_normalized_equivalence (hidem i) (hidem j) hequiv
  have hvx : v * x = 0 := by
    calc v * x = (v * e i) * (e last * x) := by rw [hvi, hlx]
      _ = v * (e i * e last) * x := by noncomm_ring
      _ = 0 := by rw [horth i last hil]; simp
  have hux : u * x = 0 := by
    calc u * x = (u * e j) * (e last * x) := by rw [huj, hlx]
      _ = u * (e j * e last) * x := by noncomm_ring
      _ = 0 := by rw [horth j last hjl]; simp
  have haa : u * u = 0 := by
    calc u * u = (u * e j) * (e i * u) := by rw [huj, hiu]
      _ = u * (e j * e i) * u := by noncomm_ring
      _ = 0 := by rw [horth j i (Ne.symm hij)]; simp
  have hbb : (x * v) * (x * v) = 0 := by
    calc (x * v) * (x * v) = x * (v * x) * v := by noncomm_ring
      _ = 0 := by rw [hvx]; simp
  have hab : u * (x * v) = 0 := by rw [← mul_assoc, hux, zero_mul]
  have hba : (x * v) * u = x := by
    calc (x * v) * u = x * (v * u) := by noncomm_ring
      _ = x * e j := by rw [hvu]
      _ = x := hxj
  have hg : squareZeroUnit u haa ∈ N := hEL i j hij hil hjl u hiu huj _ rfl
  have hcomm : w = squareZeroUnit (x * v) hbb * squareZeroUnit u haa *
      (squareZeroUnit (x * v) hbb)⁻¹ * (squareZeroUnit u haa)⁻¹ := by
    apply Units.ext
    rw [commutator_squareZeroUnit hbb haa hab, hba, hw]
  refine ⟨squareZeroUnit u haa, squareZeroUnit (x * v) hbb, ⟨u, hiu, huj, rfl⟩,
    ⟨x * v, by rw [← mul_assoc, hlx], by rw [mul_assoc, hvi], rfl⟩, hcomm, hg, hcomm, ?_⟩
  rw [hcomm]
  exact N.mul_mem (hN.conj_mem _ hg _) (N.inv_mem hg)

/-- **`EL_{m-1}(T) ≤ Rad_MF(Rˣ)`** for a decomposition whose blocks off `last` are
equivalent to `1`: a root between two such blocks is a corner unit
(`oneAddIn_cornerUnitSubgroup_of_unitPair`), and corner units die in every MF image by
Theorem `thm:full-defect-ring` in its rank-two form. -/
theorem offLastRootsIn_mfHomKernel {R : Type} [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) {m : ℕ} {e : Fin m → R} {last : Fin m}
    (hidem : ∀ i, IsIdempotentElem (e i)) (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    (hone : ∀ i, i ≠ last → IsEquivalentIdempotent R (e i) 1) :
    OffLastRootsIn (mfHomKernel Rˣ) e last := by
  intro p q hpq hpl hql a hpa haq g hg
  exact cornerUnitSubgroup_le_mfHomKernel
    Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
    R ((oneAddIn_cornerUnitSubgroup_of_unitPair hR (hidem p) (hidem q) (horth p q hpq)
      (horth q p (Ne.symm hpq)) (hone p hpl) (hone q hql) hpa haq).mem g hg)

/-- **Printed sentence (tex 1281–1286), closed, at `N = Rad_MF(Rˣ)`.**

> for distinct `i, j ≤ m-1`, `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]` and
> `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]` are products of an element of `EL_{m-1}(T)` and a
> conjugate of its inverse, so they lie in the normal subgroup `N` as well.

For a countable purely infinite simple ring and an orthogonal idempotent family whose
blocks off `last` are equivalent to `1`: every last-column root and every last-row root
`w = 1 + x` is the printed commutator, decomposes as the printed product, and lies in
`Rad_MF(Rˣ)`. -/
def PrintedSteinbergDisplaysInRadical : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ) (e : Fin m → R) (last : Fin m), (∀ i, IsIdempotentElem (e i)) →
      (∀ i j : Fin m, i ≠ j → e i * e j = 0) →
      (∀ i, i ≠ last → IsEquivalentIdempotent R (e i) 1) →
      ∀ i j : Fin m, i ≠ j → i ≠ last → j ≠ last → ∀ (x : R) (w : Rˣ), (w : R) = 1 + x →
        ((e i * x = x ∧ x * e last = x) →
          ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
            (∃ b : R, e j * b = b ∧ b * e last = b ∧ (h : R) = 1 + b) ∧
            w = g * h * g⁻¹ * h⁻¹ ∧ g ∈ mfHomKernel Rˣ ∧ w = g * (h * g⁻¹ * h⁻¹) ∧
            w ∈ mfHomKernel Rˣ) ∧
        ((e last * x = x ∧ x * e j = x) →
          ∃ g h : Rˣ, (∃ a : R, e i * a = a ∧ a * e j = a ∧ (g : R) = 1 + a) ∧
            (∃ b : R, e last * b = b ∧ b * e i = b ∧ (h : R) = 1 + b) ∧
            w = h * g * h⁻¹ * g⁻¹ ∧ g ∈ mfHomKernel Rˣ ∧ w = (h * g * h⁻¹) * g⁻¹ ∧
            w ∈ mfHomKernel Rˣ)

theorem manuscriptSentence_steinbergDisplaysInRadical :
    PrintedSteinbergDisplaysInRadical := by
  intro R _ _ hR m e last hidem horth hone i j hij hil hjl x w hw
  have hequiv : IsEquivalentIdempotent R (e i) (e j) :=
    IsEquivalentIdempotent.trans (hidem i) (hidem j) (hone i hil) (hone j hjl).symm
  have hEL := offLastRootsIn_mfHomKernel hR hidem horth hone
  exact ⟨fun hx => lastColumnDisplay (mfHomKernel Rˣ) hidem horth hij hil hjl hequiv hEL
      hx.1 hx.2 w hw,
    fun hx => lastRowDisplay (mfHomKernel Rˣ) hidem horth hij hil hjl hequiv hEL
      hx.1 hx.2 w hw⟩

end MFQuotientUnitsSteinberg
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_sufficesRankOne
#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_reductionToRankOne
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.commutator_squareZeroUnit
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.lastColumnDisplay
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.lastRowDisplay
#audit_axioms GroupApproximation.MFQuotientUnitsSteinberg.offLastRootsIn_mfHomKernel
#audit_closed_axioms GroupApproximation.MFQuotientUnitsSteinberg.manuscriptSentence_steinbergDisplaysInRadical
