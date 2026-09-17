import GroupApproximation.Leavitt.RankDescentEmbedding
import GroupApproximation.Leavitt.RankTwoNormalGeneration
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupRankDescent
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# Audit repairs, `thm:full-defect-ring` (rank two) and `cor:one-sided-ring-maximal`

## The value of `Ψ` on a root

`non_mf_groups_exist.tex`, lines 994--1002:

> Since $(1-p)S_i=0$ and $T_j(1-p)=0$, we have $\jmath(AB)=\jmath(A)\jmath(B)$ and
> $\jmath(I)=1$, so $\Psi(A)=\operatorname{diag}(\jmath(A),1)$ defines a homomorphism
> $\GL_4(R)\to\GL_2(R)$, and for $i\ne j$ and $r\in R$,
> \[ \Psi(e_{ij}(r))=\operatorname{diag}(1+S_irT_j,1)=[e_{12}(S_ir),e_{21}(T_j)] \]
> by the computation in Lemma~\ref{lem:rank-two}, since $T_jS_i=0$.

The existing census declarations give multiplicativity of `j` and the commutator form of
`Ψ(e_ij(r))`, but not the middle term of the display.  `manuscriptSentence_psiOnRootsDiag`
states the whole display for every family `S, T` with `T_i S_j = δ_ij` (the printed words
are the instance `S = wordS Q`, `T = wordT Q`): `T_j S_i = 0`, the matrix of `Ψ(e_ij(r))`
is `diag(1 + S_i r T_j, 1)` (as the image of `1 + S_i r T_j` under `x ↦ diag(x, 1)`, and
entrywise as `1 + E_00(S_i r T_j)`), and `Ψ(e_ij(r)) = [e_12(S_i r), e_21(T_j)]`.

Route: `RankDescent.psi_elementaryRoot` gives the commutator; `RankDescent.gen_val`
(the computation of `lem:rank-two`, needing `T_j (S_i r) = 0`) gives its matrix.

## The unit group

`non_mf_groups_exist.tex`, lines 1072--1075:

> Finally, the map $\jmath$ from the proof of Theorem~\ref{thm:full-defect-ring} is
> injective, since $T_i\jmath(A)S_j=A_{ij}$, and sends $\EL_4(R)$ into $R^\times$; that
> group is not MF, and MF passes to subgroups.

`manuscriptSentence_jEmbedsElementaryIntoUnits`: for a nonzero countable ring with
`ts = 1` and `1 - st` full, the printed words `S, T` built from `s, t` satisfy
`T_i S_j = δ_ij`; `T_i j(A) S_j = A_ij`; `j` is injective; `j` restricted to `EL_4(R)`
is a group homomorphism `EL_4(R) → R^×` with the value `j(g)` and it is injective;
`EL_4(R)` is not MF; MF passes along injective homomorphisms; and `R^×` is not MF.
Everything is proved: the non-MF input is the closed endpoint
`FullDefectRingEJZUnconditional.manuscriptElementaryGroupNotMFAllCharacteristics`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditOneSided2

open scoped commutatorElement

attribute [local instance] Manuscript.OneSidedMFRadical.FullDefectRing.countable_elementaryGroup

/-! ## `Ψ(e_ij(r)) = diag(1 + S_i r T_j, 1) = [e_12(S_i r), e_21(T_j)]` -/

/-- **Printed (tex 994--1002).**  For `T_i S_j = δ_ij` and `i ≠ j`: `T_j S_i = 0`,
`Ψ(e_ij(r)) = diag(1 + S_i r T_j, 1)`, entrywise `1 + E_00(S_i r T_j)`, and
`Ψ(e_ij(r)) = [e_12(S_i r), e_21(T_j)]`. -/
theorem manuscriptSentence_psiOnRootsDiag {R : Type} [Ring R] (S T : Fin 4 → R)
    (hTS : ∀ i j, T i * S j = if i = j then 1 else 0) (i j : Fin 4) (hij : i ≠ j) (r : R) :
    T j * S i = 0 ∧
      ((RankDescent.psi S T hTS (elementaryRoot i j hij r) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
          Matrix (Fin 2) (Fin 2) R) = RankDescent.blockDiagHom R (1 + S i * r * T j) ∧
      ((RankDescent.psi S T hTS (elementaryRoot i j hij r) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
          Matrix (Fin 2) (Fin 2) R) = 1 + Matrix.single (0 : Fin 2) (0 : Fin 2) (S i * r * T j) ∧
      RankDescent.psi S T hTS (elementaryRoot i j hij r) =
        ⁅RankDescent.upperRoot (S i * r), RankDescent.lowerRoot (T j)⁆ := by
  have hTSji : T j * S i = 0 := by
    rw [hTS j i, if_neg (Ne.symm hij)]
  have hbv : T j * (S i * r) = 0 := by
    rw [← mul_assoc, hTSji, zero_mul]
  have hval : ((RankDescent.psi S T hTS (elementaryRoot i j hij r) :
      (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) =
        1 + Matrix.single (0 : Fin 2) (0 : Fin 2) (S i * r * T j) := by
    rw [RankDescent.psi_elementaryRoot]
    exact RankDescent.gen_val (S i * r) (T j) hbv
  have hdiag : RankDescent.blockDiagHom R (1 + S i * r * T j) =
      1 + Matrix.single (0 : Fin 2) (0 : Fin 2) (S i * r * T j) := by
    show 1 + Matrix.single (0 : Fin 2) (0 : Fin 2) (1 + S i * r * T j - 1) = _
    rw [add_sub_cancel_left]
  exact ⟨hTSji, hval.trans hdiag.symm, hval, RankDescent.psi_elementaryRoot S T hTS i j hij r⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditOneSided2.manuscriptSentence_psiOnRootsDiag

/-! ## `j` embeds `EL_4(R)` in `R^×`, which is therefore not MF -/

/-- **Printed (tex 1072--1075).**  For a nonzero countable ring with `ts = 1` and
`1 - st` full, the printed words `S, T` satisfy `T_i S_j = δ_ij`; `T_i j(A) S_j = A_ij`,
so `j` is injective; `j` sends `EL_4(R)` injectively into `R^×`; `EL_4(R)` is not MF;
MF passes to subgroups (along injective homomorphisms); and `R^×` is not MF. -/
theorem manuscriptSentence_jEmbedsElementaryIntoUnits (R : Type) [Ring R] [Countable R]
    [Nontrivial R] (s t : R) (hts : t * s = 1)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) :
    ∃ (S T : Fin 4 → R) (hTS : ∀ i j, T i * S j = if i = j then 1 else 0),
      (∀ (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4),
          T i * RankDescent.jMap S T A * S j = A i j) ∧
        Function.Injective (RankDescent.jMap S T) ∧
        (∀ g : elementaryGroup (Fin 4) R,
          ((Manuscript.OneSidedMFRadical.FullDefectRankTwo.elementaryToUnits S T hTS g : Rˣ) :
              R) =
            RankDescent.jMap S T
              ((g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)) ∧
        Function.Injective
          (Manuscript.OneSidedMFRadical.FullDefectRankTwo.elementaryToUnits S T hTS) ∧
        ¬ IsCDEOperatorMF (elementaryGroup (Fin 4) R) ∧
        (∀ (G M : Type) [Group G] [Group M] (φ : G →* M),
          Function.Injective φ → IsOperatorMF M → IsOperatorMF G) ∧
        ¬ IsOperatorMF Rˣ := by
  obtain ⟨m, a, b, hab⟩ := hfull
  let Q : RankDescent.ProperlyInfiniteUnit R :=
    RankDescent.ofFull (⟨s, t, hts⟩ : OneSidedCompressor.OneSidedInverse R) a b hab
  have hTS := RankDescent.wordT_mul_wordS Q
  exact ⟨RankDescent.wordS Q, RankDescent.wordT Q, hTS,
    RankDescent.wordT_mul_jMap_mul_wordS (RankDescent.wordS Q) (RankDescent.wordT Q) hTS,
    RankDescent.jMap_injective (RankDescent.wordS Q) (RankDescent.wordT Q) hTS,
    fun _ ↦ rfl,
    Manuscript.OneSidedMFRadical.FullDefectRankTwo.elementaryToUnits_injective
      (RankDescent.wordS Q) (RankDescent.wordT Q) hTS,
    Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptElementaryGroupNotMFAllCharacteristics
      R s t hts ⟨m, a, b, hab⟩ 4 le_rfl,
    fun _ _ _ _ φ hφ hM ↦
      Manuscript.OneSidedMFRadical.FullDefectRankTwo.isOperatorMF_of_injective φ hφ hM,
    Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptUnitGroupNotMFAllCharacteristics
      R s t hts ⟨m, a, b, hab⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditOneSided2.manuscriptSentence_jEmbedsElementaryIntoUnits

end AuditOneSided2
end NonMF
end Manuscript
end GroupApproximation
