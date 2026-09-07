import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCore
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingDescent
import GroupApproximation.PropertyT.EJZIntegralReduction
import Mathlib.Algebra.CharP.Subring

/-!
# `thm:full-defect-ring` for a general countable ring

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`:

> Let `R` be a countable unital associative ring.  Suppose that `s,t ∈ R`
> satisfy `ts = 1`, `R(1-st)R = R`.  For every `n ≥ 4`, every homomorphism from
> `EL_n(R)` to an MF group is trivial.

and the last paragraph of its proof, which reduces the general countable case
to the finitely generated one.

## The three statements, and what each of them costs

The printed theorem is proved for a finitely generated ring first, because
that is the hypothesis of the Ershov--Jaikin-Zapirain property-`(T)` theorem it
invokes; the general case then follows by covering `EL_n(R)` with the images of
`EL_n(S)` over finitely generated subrings `S`.  The three declarations below
follow that structure exactly.

* `FullDefectAtFixedRing` is the theorem at one ring with **the two property
  `(T)` inputs written as hypotheses**: property `(T)` for `EL₃(R)` and for
  `EL_n(R)`.  It carries no finite-generation hypothesis, because the printed
  proof uses finite generation for nothing except those two conclusions.  This
  is the interface to the ring calculation.
* `PrintedFullComplementaryIdempotentsOverSubrings` is the general countable
  statement in the sharpest honest form: property `(T)` is asked of the
  elementary groups **of the finitely generated subrings of `R` only**, which
  is all the printed proof ever uses.  Every stronger form below is an
  instance of it.
* `PrintedFullComplementaryIdempotents` and
  `PrintedFullComplementaryIdempotentsPrimeChar` are the two instances that
  discharge that property-`(T)` hypothesis from a property-`(T)` theorem: the
  coefficient-general Ershov--Jaikin-Zapirain statement
  `FinitelyGeneratedRingGeneralRankElementaryPropertyT` (still open in this
  repository in characteristic zero and at non-prime positive characteristic;
  see `PropertyT/EJZIntegralReduction`), and the prime-characteristic theorem
  `primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT`, which is
  proved here.

The Ershov--Jaikin-Zapirain input is a **leading hypothesis of the theorem**,
never a conjunct of the proposition: a proposition that carried its own
hypothesis would be a weaker statement wearing the printed theorem's name.

## The descent

`FullDefectRingDescent.exists_finset_elementaryGroup_le_map` supplies the
printed sentence "every element of `EL_n(R)` is a product of finitely many
elementary matrices, so it lies in `EL_n(S)` for some finitely generated
unital subring `S` … containing `s`, `t`, and the `a_j, b_j`".  The prescribed
finite set is `{s, t} ∪ a(Fin m) ∪ b(Fin m)`, so the pair relation `ts = 1` and
the fullness witness both descend to `S` — they are equations between elements
of `S`, checked after the injective inclusion `S → R`.  The homomorphism `f` is
then restricted along `elementaryGroupMap S.subtype`, killed by the finitely
generated case, and evaluated at the preimage of `x`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators

/-! ## The theorem at one ring, with the property `(T)` inputs explicit -/

/-- **`thm:full-defect-ring` at a fixed countable ring**, with the two
property-`(T)` conclusions the printed proof takes from
Ershov--Jaikin-Zapirain written as hypotheses.

The two hypotheses are the printed ones: "`G = EL_n(R)` and `L = EL₃(R)` … both
groups have property (T)".  Finite generation of `R` does not appear, because
the printed proof uses it only to obtain these two.

This is the interface between the ring calculation of `thm:full-defect-ring` —
the compressor `u`, the centralizer element `c`, and normal generation of
`EL_n(R)` by `d = [ucu⁻¹, ℓ]` under fullness of `1 - st` — and the general
countable statement below. -/
def FullDefectAtFixedRing : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
    ∀ (n : ℕ), 4 ≤ n →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) R) →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) R) →
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M) (x : elementaryGroup (Fin n) R),
          f x = 1

/-! ## The general countable statement -/

/-- **`thm:full-defect-ring`, general countable `R`, with property `(T)` asked
only of the finitely generated subrings.**

This is the sharpest form the printed proof supports: `R` itself is never
required to be finitely generated — "The ring `R` need not be finitely
generated" — and property `(T)` is never used at `R`, only at the subrings `S`
the descent produces. -/
def PrintedFullComplementaryIdempotentsOverSubrings : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
    (∀ (S : Subring R), IsFinitelyGeneratedRing ↥S →
        ∀ (n : ℕ), 3 ≤ n →
          HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) ↥S)) →
      ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M) (x : elementaryGroup (Fin n) R),
          f x = 1

/-- **The printed descent to finitely generated subrings, proved.**

Given the theorem at every fixed ring, the general countable statement follows
by the printed argument: the element `x`, together with `s`, `t` and the finitely
many `a_j, b_j`, is captured by the subring `S` generated by one finite set;
the pair relation and the fullness witness descend to `S`; property `(T)` for
`EL₃(S)` and `EL_n(S)` is the hypothesis at `S`; and `f` restricted along
`elementaryGroupMap S.subtype` kills the preimage of `x`. -/
theorem fullComplementaryIdempotentsOverSubrings_of_fixedRing
    (hfixed : FullDefectAtFixedRing) :
    PrintedFullComplementaryIdempotentsOverSubrings := by
  classical
  intro R _ _ s t hts hfull hT n hn M _ hM f x
  obtain ⟨m, a, b, hab⟩ := hfull
  -- the printed finite set of coefficients: `s`, `t`, and the `a_j, b_j`
  set T : Finset R :=
    insert s (insert t ((Finset.univ.image a) ∪ (Finset.univ.image b))) with hTdef
  obtain ⟨F, hTF, hmem⟩ :=
    exists_finset_elementaryGroup_le_map (ι := Fin n) T x.2
  have hcoe : ∀ y : R, y ∈ T → y ∈ Subring.closure (F : Set R) :=
    fun y hy ↦ Subring.subset_closure (hTF hy)
  have hsS : s ∈ Subring.closure (F : Set R) :=
    hcoe s (by rw [hTdef]; exact Finset.mem_insert_self _ _)
  have htS : t ∈ Subring.closure (F : Set R) :=
    hcoe t (by
      rw [hTdef]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have haS : ∀ k, a k ∈ Subring.closure (F : Set R) := fun k ↦
    hcoe _ (by
      rw [hTdef]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ k)))))
  have hbS : ∀ k, b k ∈ Subring.closure (F : Set R) := fun k ↦
    hcoe _ (by
      rw [hTdef]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ k)))))
  -- the pair and the fullness witness, descended to the subring
  have htsS : (⟨t, htS⟩ : ↥(Subring.closure (F : Set R))) * ⟨s, hsS⟩ = 1 :=
    Subtype.ext hts
  have hfullS : ∑ k, (⟨a k, haS k⟩ : ↥(Subring.closure (F : Set R))) *
      (1 - ⟨s, hsS⟩ * ⟨t, htS⟩) * ⟨b k, hbS k⟩ = 1 := by
    refine Subtype.ext ?_
    push_cast
    exact hab
  -- property (T) at the subring
  have hfg : IsFinitelyGeneratedRing ↥(Subring.closure (F : Set R)) :=
    isFinitelyGeneratedRing_subringClosure F
  have hT3 : HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin 3) ↥(Subring.closure (F : Set R))) :=
    hT _ hfg 3 le_rfl
  have hTn : HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin n) ↥(Subring.closure (F : Set R))) :=
    hT _ hfg n (le_trans (by norm_num) hn)
  -- the element comes from the subring
  obtain ⟨y, hy, hyx⟩ := hmem
  have hxeq : x = elementaryGroupMap (ι := Fin n)
      (Subring.closure (F : Set R)).subtype ⟨y, hy⟩ := Subtype.ext hyx.symm
  rw [hxeq]
  exact hfixed _ ⟨s, hsS⟩ ⟨t, htS⟩ htsS ⟨m, _, _, hfullS⟩ n hn hT3 hTn M hM
    (f.comp (elementaryGroupMap (Subring.closure (F : Set R)).subtype)) ⟨y, hy⟩

/-! ## The two property-`(T)` instances -/

/-- **`thm:full-defect-ring` exactly as printed.**  Let `R` be a countable
unital associative ring, `s, t ∈ R` with `ts = 1` and `1 - st` full — the
printed gloss `∑_j a_j(1-st)b_j = 1` for finitely many `a_j, b_j ∈ R`.  Then for
every `n ≥ 4`, every homomorphism from `EL_n(R)` to an MF group is trivial.

The property-`(T)` theorem is a hypothesis of the theorem below, not of this
proposition. -/
def PrintedFullComplementaryIdempotents : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M) (x : elementaryGroup (Fin n) R),
          f x = 1

/-- **The printed theorem, from the ring calculation and the printed
Ershov--Jaikin-Zapirain input.**

`hEJZ` is `FinitelyGeneratedRingGeneralRankElementaryPropertyT`, the
coefficient-general Ershov--Jaikin-Zapirain statement in the exact form
`PropertyT/EJZIntegralReduction` names it: property `(T)` for `EL_n(A)` in
every rank `n ≥ 3` over every finitely generated ring `A`.  It is reused, never
restated. -/
theorem manuscriptFullComplementaryIdempotents
    (hfixed : FullDefectAtFixedRing)
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedFullComplementaryIdempotents := by
  intro R _ _ s t hts hfull n hn M _ hM f x
  exact fullComplementaryIdempotentsOverSubrings_of_fixedRing hfixed R s t hts
    hfull (fun S hfg k hk ↦ hEJZ (↥S) hfg k hk) n hn M hM f x

/-- **`thm:full-defect-ring` in prime characteristic, with no property-`(T)`
hypothesis at all.**  The printed statement, restricted to coefficient rings of
prime characteristic — where the Ershov--Jaikin-Zapirain theorem is proved in
this repository, in every rank `n ≥ 3` and over every finitely generated ring
(`primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT`). -/
def PrintedFullComplementaryIdempotentsPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Countable R] [CharP R p]
    (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ (f : elementaryGroup (Fin n) R →* M)
            (x : elementaryGroup (Fin n) R), f x = 1

/-- **The prime-characteristic case, from the ring calculation alone.**

Every subring of a ring of characteristic `p` again has characteristic `p`
(`CharP.subring`), so the property-`(T)` hypothesis of
`PrintedFullComplementaryIdempotentsOverSubrings` is discharged at every
finitely generated subring by the repository's own theorem.  No literature
input remains. -/
theorem manuscriptFullComplementaryIdempotentsPrimeChar
    (hfixed : FullDefectAtFixedRing) :
    PrintedFullComplementaryIdempotentsPrimeChar := by
  intro p hp R _ _ _ s t hts hfull n hn M _ hM f x
  refine fullComplementaryIdempotentsOverSubrings_of_fixedRing hfixed R s t hts
    hfull (fun S hfg k hk ↦ ?_) n hn M hM f x
  exact primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT p hp (↥S)
    hfg k hk

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation
