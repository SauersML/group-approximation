import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:one-sided-ring-maximal`: `EL_n(R)` is countable, nontrivial and not MF, for every `n ≥ 2`

`non_mf_groups_exist.tex`, Corollary `cor:one-sided-ring-maximal` (tex 1050–1057) and its proof
(tex 1072–1075):

> If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then for every $n\ge2$
> the algebra $C^*_{\mathrm r}(\EL_n(R))$ is separable, stably finite, and not MF, and the unit
> group $R^\times$ is not MF.
>
> If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then $G=\EL_n(R)$ is
> countable and nontrivial, and by Theorem~\ref{thm:full-defect-ring} it is not MF.

The hypothesis of `thm:full-defect-ring` (tex 930–937): `R` is a countable unital associative ring,
and `s, t ∈ R` satisfy `ts = 1` and `R(1-st)R = R`, printed in the form `1 = ∑ⱼ aⱼ(1-st)bⱼ` for
finitely many `aⱼ, bⱼ`.  The printed `R ≠ 0` is `[Nontrivial R]`.

## Where `4` was used, and why it is gone

`FullDefectRing.PrintedElementaryGroupNotMF` quantifies over `n ≥ 4`, because it is proved from the
rank-four form of `thm:full-defect-ring` (the universal group `EL_4(𝒞)` and the compression
criterion applied in rank four).  The proof's *Rank two* paragraph (tex 986–1010) — the ring map
`𝒞 → R`, the corner map `ȷ` and `Ψ(A) = diag(ȷ(A), 1)` from `GL_4(R)` to `GL_2(R)`, and
`lem:rank-two` — carries the conclusion down to `n = 2, 3`.  That descent is in the library as
`FullDefectRankTwo.rankTwo_of_rankFour`, and the rank-two theorem with nothing assumed is
`FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics`
(root-imported).  This module turns it into the printed "not MF" at every `n ≥ 2`:

* countable: `FullDefectRing.countable_elementaryGroup`;
* nontrivial: `FullDefectRing.nontrivial_elementaryGroup` at the indices `0 ≠ 1` of `Fin n`;
* not MF: every homomorphism to an MF group is trivial, and the identity of a nontrivial MF group
  is not (`FullDefectRing.not_isCDEOperatorMF_of_killsMFTargets`); both the literal
  Carrión–Dadarlat–Eckhardt predicate `IsCDEOperatorMF` and `IsOperatorMF` are recorded, and they
  agree on countable groups (`isCDEOperatorMF_iff_isOperatorMF`).

The same content also sits in two never-root-imported modules of the other swarm
(`OneSidedMFRadical/ElementaryGroupNotMFRankTwoClosed`, `NonMF/OneSidedRegular/ElementaryGroupNotMF`).
They are not imported here, so that this endpoint is compiled by CI without wiring foreign modules.
-/

namespace GroupApproximation.Full.NM10

open GroupApproximation.Manuscript.OneSidedMFRadical
open GroupApproximation.ReducedGroupCStarTrace

/-- **"then $G=\EL_n(R)$ is countable and nontrivial, and by Theorem~\ref{thm:full-defect-ring} it is
not MF"** (tex 1072–1075), for every countable nonzero unital ring `R` with `ts = 1` and full `1 - st`,
at every rank `n ≥ 2` of the corollary (tex 1054).  "Not MF" is stated in both the
Carrión–Dadarlat–Eckhardt form and the operator-norm form. -/
def PrintedElementaryGroupNotMFRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 2 ≤ n →
        Countable (elementaryGroup (Fin n) R) ∧
          Nontrivial (elementaryGroup (Fin n) R) ∧
            ¬ @IsCDEOperatorMF (elementaryGroup (Fin n) R) _
                FullDefectRing.countable_elementaryGroup ∧
              ¬ IsOperatorMF (elementaryGroup (Fin n) R)

/-- **`cor:one-sided-ring-maximal`, tex 1072–1075, at every `n ≥ 2`**, with nothing assumed. -/
theorem printedElementaryGroupNotMFRankTwo : PrintedElementaryGroupNotMFRankTwo := by
  intro R _ _ _ s t hts hfull n hn
  haveI hcount : Countable (elementaryGroup (Fin n) R) :=
    FullDefectRing.countable_elementaryGroup
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    FullDefectRing.nontrivial_elementaryGroup (R := R) hne
  have hnotCDE : ¬ IsCDEOperatorMF (elementaryGroup (Fin n) R) :=
    FullDefectRing.not_isCDEOperatorMF_of_killsMFTargets fun M _ hM f x ↦
      FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
        R s t hts hfull n hn M hM f x
  refine ⟨hcount, inferInstance, hnotCDE, ?_⟩
  intro hMF
  exact hnotCDE ((isCDEOperatorMF_iff_isOperatorMF (elementaryGroup (Fin n) R)).mpr hMF)

/-- The rank-four statement `FullDefectRing.PrintedElementaryGroupNotMF` is the `n ≥ 4` part of
`PrintedElementaryGroupNotMFRankTwo`. -/
theorem printedElementaryGroupNotMF_of_rankTwo : FullDefectRing.PrintedElementaryGroupNotMF := by
  intro R _ _ _ s t hts hfull n hn
  exact (printedElementaryGroupNotMFRankTwo R s t hts hfull n (by omega)).2.2.1

/-- **`cor:one-sided-ring-maximal`, second printed sentence (tex 1053–1056), together with the proof
sentence of tex 1072–1075**, at every `n ≥ 2`: for a countable nonzero ring with `ts = 1` and full
`1 - st`, `EL_n(R)` is countable, nontrivial and not MF; `C*_r(EL_n(R))` is separable, stably finite
and not MF; and `Rˣ` is not MF. -/
def PrintedOneSidedRingMaximalGroupClausesRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      (∀ (n : ℕ), 2 ≤ n →
          (Countable (elementaryGroup (Fin n) R) ∧
              Nontrivial (elementaryGroup (Fin n) R) ∧
                ¬ IsOperatorMF (elementaryGroup (Fin n) R)) ∧
            TopologicalSpace.SeparableSpace
                (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
              IsStablyFiniteCStarAlgebra
                  (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
                ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R))) ∧
        ¬ IsOperatorMF Rˣ

/-- **`cor:one-sided-ring-maximal`, second sentence and tex 1072–1075, at every `n ≥ 2`**, with
nothing assumed. -/
theorem printedOneSidedRingMaximalGroupClausesRankTwo :
    PrintedOneSidedRingMaximalGroupClausesRankTwo := by
  intro R _ _ _ s t hts hfull
  refine ⟨fun n hn ↦ ?_,
    FullDefectRingEJZUnconditional.manuscriptUnitGroupNotMFAllCharacteristics R s t hts hfull⟩
  obtain ⟨hc, hnt, _, hop⟩ := printedElementaryGroupNotMFRankTwo R s t hts hfull n hn
  exact ⟨⟨hc, hnt, hop⟩,
    FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalReducedCStarRankTwoAllCharacteristics
      R s t hts hfull n hn⟩

/-- **The printed sentence of tex 1072–1075, for one ring.**  If `R ≠ 0` is countable and `s, t ∈ R`
satisfy `ts = 1` and `∑ₖ aₖ(1 - st)bₖ = 1`, then for every `n ≥ 2`, `G = EL_n(R)` is countable and
nontrivial, and it is not MF. -/
theorem manuscriptSentence_elementaryGroupCountableNontrivialNotMF
    (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R) (hts : t * s = 1)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1)
    (n : ℕ) (hn : 2 ≤ n) :
    Countable (elementaryGroup (Fin n) R) ∧
      Nontrivial (elementaryGroup (Fin n) R) ∧
        ¬ IsOperatorMF (elementaryGroup (Fin n) R) :=
  let h := printedElementaryGroupNotMFRankTwo R s t hts hfull n hn
  ⟨h.1, h.2.1, h.2.2.2⟩

end GroupApproximation.Full.NM10

#audit_closed_axioms GroupApproximation.Full.NM10.printedElementaryGroupNotMFRankTwo
#audit_closed_axioms GroupApproximation.Full.NM10.printedElementaryGroupNotMF_of_rankTwo
#audit_closed_axioms GroupApproximation.Full.NM10.printedOneSidedRingMaximalGroupClausesRankTwo
#audit_axioms
  GroupApproximation.Full.NM10.manuscriptSentence_elementaryGroupCountableNontrivialNotMF
