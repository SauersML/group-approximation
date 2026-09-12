import GroupApproximation.CharClass.LIXKGenSphere
import GroupApproximation.CharClass.LIXShapeGeneric
import GroupApproximation.CharClass.LIXKPunctured
import GroupApproximation.Meta.AxiomGuard

/-!
# The punctured-product vanishing over `S¹ × S^{2n+1} × Y`, generic in the rank

Lane `sp-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4; report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3 file B).

`CharClass/LIXStepEPunctured.lean` runs the punctured-product recursion over
`N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` by peeling one projective factor at a time, with
`CharClass/LIXSectionNesting.lean`'s two homeomorphisms doing the re-bracketing and
`hbase` — the two sphere factors — as the base case.  Everything in that argument is
generic in the rank except the literal `unitVectors (Fin 3)` and the two numerals `6` and
`2·(∑ dⱼ) + 6`.  This file re-authors it at rank `n`, over `sp-tower`'s
`CharClass.Gen.baseM n dd`, with `CharClass/LIXKGenSphere.lean`'s `KGen.hbase n` as the
base case.

## What this is for, and what it is not for

It supplies the ONE hypothesis of `sp-oddside`'s `LIXKPunctured.isZero_punctured_finite`
that is not already rank-free.  That theorem — `H^m` of the complement of a finite
non-empty set vanishes for `m ≥ d` — is stated for an abstract `[T1Space N]` and an
abstract `d`, so the `k`-zero Step C's `k+1`-point punctured vanishing needs no new
induction at rank `n`: it needs `∀ z, PuncturedAcyclic N (lixTopDegree n dd) z`, which is
`puncturedAcyclic_lixBase_topDegree` below.

Per `sp-oddside`'s own structural finding, the `k+1`-point statement is **not** on the
critical path of the mod-2 route (the one-zero argument is run at each `z_i` and consumes
only the ONE-point statement, which is `puncturedAcyclic_lixBase_topDegree` applied at
`z_i`).  It is proved anyway because `sp-design` §4.2 item 1 asks for it and because any
arrangement identifying `γ_r` through exactness rather than through the section needs it.

## Main results

* `KGen.lixRank`, `KGen.lixTopDegree` — the rank and top degree at rank `n`, with
  `lixTopDegree_two` recording that at `n = 2` the second is `LIXSectionLocalHomeo`'s on
  the nose.
* `KGen.baseNilHomeo`, `KGen.baseSnocHomeo` — the re-bracketing, at rank `n`.
* `KGen.puncturedAcyclic_lixBase` — **the punctured-product vanishing at the LIX base, at
  every rank**, unconditional apart from positivity of the `dⱼ`.
* `KGen.puncturedVanish_finite` — its finite-puncture consequence, through `sp-oddside`'s
  induction.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59
open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. The rank and the top degree at rank `n` -/

/-- `rank V = ∑ⱼ dⱼ + (n+1)` at rank `n`.  At `n = 2` this is
`LemmaTwoTopClass.lixRank`, whose `+ 3` is `+ (2+1)`. -/
def lixRank {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ) : ℕ := (∑ j, dd j) + (n + 1)

/-- The top degree `2 · rank` at rank `n`, stated additively rather than as `2 * lixRank`
so that the recursion's arithmetic stays in the shape `omega` and `ring` read. -/
def lixTopDegree {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ) : ℕ :=
  2 * (∑ j, dd j) + (2 * n + 2)

theorem lixTopDegree_eq_two_mul_lixRank {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ) :
    lixTopDegree n dd = 2 * lixRank n dd := by
  rw [lixTopDegree, lixRank]
  ring

/-! ## 2. Re-bracketing the base, at rank `n` -/

/-- **The base case.**  With no projective factors the base is `S¹ × S^{2n+1}`; the
dependent product over `Fin 0` is a one-point space. -/
def baseNilHomeo (n : ℕ) (dd : Fin 0 → ℕ) :
    (↥sphereOne × Gen.baseM n dd) ≃ₜ ↥sphereOne × ↥(unitVectors (Fin (n + 1))) :=
  (Homeomorph.refl (↥sphereOne)).prodCongr
    (Homeomorph.prodUnique (↥(unitVectors (Fin (n + 1)))) (∀ j : Fin 0, CP (dd j)))

/-- **The binary step.**  The base with `ℓ + 1` projective factors is the base with `ℓ` of
them, times one `ℂP`, adjoined on the right. -/
def baseSnocHomeo {ℓ : ℕ} (n : ℕ) (dd : Fin (ℓ + 1) → ℕ) :
    (↥sphereOne × Gen.baseM n dd)
      ≃ₜ (↥sphereOne × Gen.baseM n (fun j => dd j.castSucc)) × CP (dd (Fin.last ℓ)) :=
  (((Homeomorph.refl (↥sphereOne)).prodCongr
        ((Homeomorph.refl (↥(unitVectors (Fin (n + 1))))).prodCongr
          (piFinSnocHomeo (fun j : Fin (ℓ + 1) => CP (dd j))))).trans
    ((Homeomorph.refl (↥sphereOne)).prodCongr
      (Homeomorph.prodAssoc (↥(unitVectors (Fin (n + 1))))
        (∀ j : Fin ℓ, CP (dd j.castSucc)) (CP (dd (Fin.last ℓ)))).symm)).trans
    (Homeomorph.prodAssoc (↥sphereOne)
      (↥(unitVectors (Fin (n + 1))) × (∀ j : Fin ℓ, CP (dd j.castSucc)))
      (CP (dd (Fin.last ℓ)))).symm

/-! ## 3. The recursion -/

/-- **The punctured-product vanishing at the LIX base, at every rank.**

Induction on the number of projective factors, peeling the last one with `baseSnocHomeo`
and transporting with `PuncturedAcyclic.congr'`.  The base case is `baseNilHomeo` against
`KGen.hbase n`.  This is `LIXStepEPunctured.puncturedAcyclic_lixBase` with the rank made a
parameter and with the three projective hypotheses already discharged from
`ThomProjectivePunctured`/`ThomKunnethProjective`, which are generic in `d` and were never
rank-bound. -/
theorem puncturedAcyclic_lixBase (n : ℕ) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
    ∀ z : ↥sphereOne × Gen.baseM n dd,
      PuncturedAcyclic (↥sphereOne × Gen.baseM n dd)
        (2 * (∑ j, dd j) + (2 * n + 2)) z := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro dd _ z
    have hdeg : 2 * (∑ j : Fin 0, dd j) + (2 * n + 2) = 2 * n + 2 := by simp
    rw [hdeg]
    exact PuncturedAcyclic.congr' cohomologyToolkit (baseNilHomeo n dd) rfl
      (hbase n (baseNilHomeo n dd z))
  | succ ℓ ih =>
    intro dd hdd z
    have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + (2 * n + 2)
        = (2 * (∑ j : Fin ℓ, dd j.castSucc) + (2 * n + 2)) + 2 * dd (Fin.last ℓ) := by
      rw [Fin.sum_univ_castSucc dd]
      ring
    rw [hdeg]
    refine PuncturedAcyclic.congr' cohomologyToolkit (baseSnocHomeo n dd) rfl ?_
    have hprod := puncturedAcyclic_prod
      (x₀ := (baseSnocHomeo n dd z).1) (y₀ := (baseSnocHomeo n dd z).2)
      (kunnethFactor_CP (dd (Fin.last ℓ)))
      (kunnethFactor_CP_punctured (dd (Fin.last ℓ)) (hdd (Fin.last ℓ))
        (baseSnocHomeo n dd z).2)
      (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc) (baseSnocHomeo n dd z).1)
      (puncturedAcyclic_CP (dd (Fin.last ℓ)) (hdd (Fin.last ℓ)) (baseSnocHomeo n dd z).2)
    simpa using hprod

/-- The same, in the degree index the `k`-zero Step C hands the counting engine. -/
theorem puncturedAcyclic_lixBase_topDegree (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hdd : ∀ j, 0 < dd j) (z : ↥sphereOne × Gen.baseM n dd) :
    PuncturedAcyclic (↥sphereOne × Gen.baseM n dd) (lixTopDegree n dd) z :=
  puncturedAcyclic_lixBase n ℓ dd hdd z

/-! ## 4. The finite-puncture consequence -/

/-- **`H^m(N ∖ S; F₂) = 0` for a finite non-empty `S` and `m ≥ 2·rank`, at every rank.**

The induction is `sp-oddside`'s `LIXKPunctured.isZero_punctured_finite`, which is stated
for an abstract `[T1Space N]` and an abstract dimension and therefore needs no rank
parameter; all this adds is its one hypothesis at rank `n`.  At `S` the set of the `k+1`
zeros and `m = 2r` it is `sp-design` §4.2 item 1. -/
theorem puncturedVanish_finite (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    {m : ℕ} (hm : lixTopDegree n dd ≤ m)
    {S : Set (↥sphereOne × Gen.baseM n dd)} (hfin : S.Finite) (hne : S.Nonempty) :
    IsZero (cohomologyZMod2
      (TopCat.of ↥(Sᶜ : Set (↥sphereOne × Gen.baseM n dd))) m) :=
  isZero_punctured_finite (puncturedAcyclic_lixBase_topDegree n dd hdd) hm hfin hne

end KGen

/-! ## 5. The rank-two bridge

`KGen.lixTopDegree 2 dd` is `2 * (∑ j, dd j) + (2 * 2 + 2)` and
`LIXSectionLocalHomeo.lixTopDegree dd` is `2 * (∑ j, dd j) + 6`; the two numerals are
literals, so the bridge is `rfl` and the rank-`n` statement really is a generalisation of
the rank-two one rather than a statement about a neighbouring degree. -/

theorem lixTopDegree_two {ℓ : ℕ} (dd : Fin ℓ → ℕ) :
    KGen.lixTopDegree 2 dd = lixTopDegree dd := rfl

/-- The rank-two cross-check of §3, in the shape `LIXStepESpheresDischarged` states it. -/
theorem puncturedAcyclic_lixBase_two {ℓ : ℕ} (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (z : ↥sphereOne × baseM dd) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (lixTopDegree dd) z :=
  KGen.puncturedAcyclic_lixBase_topDegree 2 dd hdd z

/-! Audited on every build. -/

#audit_axioms KGen.puncturedAcyclic_lixBase
#audit_axioms KGen.puncturedVanish_finite
#audit_axioms puncturedAcyclic_lixBase_two

end GroupApproximation.CharClass
