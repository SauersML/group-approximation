import GroupApproximation.Manuscript.ChainCore.BilateralThreeZSentences
import GroupApproximation.Algebra.BilateralThreeCellZOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three`: the central element `z` and the compression criterion

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three` (tex 1577–1592):

> (tex 1577) Then $c\in C_B(L)$ and
> \[ WcW^{-1}=e_{13}(f_{0,-2}),\quad \delta=[WcW^{-1},\ell]=e_{23}(-f_{0,-2}),\quad
>    [y,\delta]=z^{-1}. \]
> (tex 1583) Hence $z\in\mathfrak D_B(L)$.  It commutes with $L$, since both its
> supports lie outside $P$; with $W$, since its two levels are fixed;
> and with $c,y$, by the matrix-unit products.  So $\langle z\rangle$
> is a nontrivial finite central subgroup of $B$, of order
> $\operatorname{char}(k)$.  Theorem~\ref{thm:compression-criterion}
> kills $z$ under every MF homomorphism from $B$, hence from $\GL_3(R_X)$.
> The identities
> \[ [z,e_{31}(f_{-2,0})]=e_{31}(f_{-1,0}),\quad [e_{23}(f_{0,-1}),e_{31}(f_{-1,0})]=e_{21}(d) \]
> then kill the defect root.

Standing objects as in `BilateralB.CycleCompressor`: `R_X = ClopenCrossedProduct T k` over a finite
field `k`, the cell `bilateralCell T k hP hTP`, the printed coefficient set
`S = bilateralCellSet T k hP hTP` (from the finitely generated ring `cellRing`),
`L = coreGroup S`, `B = Cell.B S`.  Coordinates are 0-indexed, so the printed `e_{13}` is
`elementaryUnit 0 2`.

Proof route (all corpus ingredients are unconditional):
* the display is matrix-unit arithmetic (`Cell.W_conj_c`, `Cell.delta_eq`, `Cell.commutator_y_delta`);
* `z ∈ 𝔇_B(L)` is `bilateralCell_z_mem_printedDefect` (generators of the printed defect);
* the centrality and the order `char(k)` come from `Cell.z_commute_B` and the closed
  `ClopenCrossedProduct.manuscriptSentence_bilateralThreeZCentralOfOrderChar` (using `d = 1_D ≠ 0`);
* the compression criterion step is `printedBilateralThreeCompressionKillsZ_closed`, whose proof uses
  `hasKazhdanPropertyT_bilateralCoreGroup` (EJZ property `(T)` of `EL_3` over the finitely generated
  ring `S`, proved in the corpus without hypotheses) and `manuscriptOneSidedCompressionCriterion`;
* the defect root is killed by `killed_of_commutators` from the two displayed identities.

* `manuscriptSentence_bilateralThreeCInCentralizer` (tex 1577)
* `manuscriptSentence_bilateralThreeZInDefect` (tex 1583)
* `manuscriptSentence_bilateralThreeZCommutes` (tex 1583)
* `manuscriptSentence_bilateralThreeZCentralOrderChar` (tex 1583–1587)
* `manuscriptSentence_bilateralThreeCompressionKillsZ` (tex 1587–1588)
* `manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot` (tex 1589–1592)
-/

namespace GroupApproximation.Manuscript.NonMF.BilateralB

open GroupApproximation.BilateralThreeCell GroupApproximation.ClopenCrossedProduct
open GroupApproximation.Manuscript.ChainCore.BilateralThree
open GroupApproximation.Manuscript.OneSidedMFRadical
open scoped commutatorElement

section Clopen

variable {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] {P : Set X}
  (hP : IsClopen P) (hTP : T '' P ⊆ P)

/-- **tex 1577**, "Then $c\in C_B(L)$ and $WcW^{-1}=e_{13}(f_{0,-2})$,
$\delta=[WcW^{-1},\ell]=e_{23}(-f_{0,-2})$, $[y,\delta]=z^{-1}$."
`c ∈ B` commutes with every element of `L`, and the three displayed identities. -/
theorem manuscriptSentence_bilateralThreeCInCentralizer :
    ((bilateralCell T k hP hTP).c ∈ (bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP) ∧
        ∀ x ∈ coreGroup (bilateralCellSet T k hP hTP), Commute (bilateralCell T k hP hTP).c x) ∧
      (bilateralCell T k hP hTP).W * (bilateralCell T k hP hTP).c * (bilateralCell T k hP hTP).W⁻¹ =
        elementaryUnit (0 : Fin 3) 2 (by decide) ((bilateralCell T k hP hTP).f 0 (-2)) ∧
      ⁅(bilateralCell T k hP hTP).W * (bilateralCell T k hP hTP).c * (bilateralCell T k hP hTP).W⁻¹,
          (bilateralCell T k hP hTP).ell⁆ =
        elementaryUnit (1 : Fin 3) 2 (by decide) (-(bilateralCell T k hP hTP).f 0 (-2)) ∧
      ⁅(bilateralCell T k hP hTP).y,
          ⁅(bilateralCell T k hP hTP).W * (bilateralCell T k hP hTP).c *
              (bilateralCell T k hP hTP).W⁻¹, (bilateralCell T k hP hTP).ell⁆⁆ =
        (bilateralCell T k hP hTP).z⁻¹ := by
  have hS := (bilateralCell T k hP hTP).corner_of_mem_range (S := cellRing T k hP hTP)
  refine ⟨⟨(bilateralCell T k hP hTP).c_mem_B (bilateralCellSet T k hP hTP),
      (bilateralCell T k hP hTP).c_commute_coreGroup hS⟩,
    (bilateralCell T k hP hTP).W_conj_c, (bilateralCell T k hP hTP).delta_eq, ?_⟩
  rw [(bilateralCell T k hP hTP).delta_eq]
  exact (bilateralCell T k hP hTP).commutator_y_delta

/-- **tex 1583**, "Hence $z\in\mathfrak D_B(L)$."  `z ∈ B`, and as an element of `B` it lies in the
printed defect `𝔇_B(L)` of `L = EL_3(S)` inside `B`. -/
theorem manuscriptSentence_bilateralThreeZInDefect :
    ∃ hz : (bilateralCell T k hP hTP).z ∈
        (bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP),
      (⟨(bilateralCell T k hP hTP).z, hz⟩ :
          ↥((bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP))) ∈
        printedDefect ((coreGroup (bilateralCellSet T k hP hTP)).subgroupOf
          ((bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP))) :=
  ⟨bilateralCell_z_mem_B T k hP hTP, bilateralCell_z_mem_printedDefect T k hP hTP⟩

/-- **tex 1583**, "It commutes with $L$, since both its supports lie outside $P$; with $W$, since its
two levels are fixed; and with $c,y$, by the matrix-unit products."
`z` commutes with every element of `L`; its coefficient `f_{-1,-2}` is killed by `p` on both sides;
`z` commutes with `W`, the third coordinate `ur` of `W` commuting with `f_{-1,-2}`; and `z` commutes
with `c` and `y`. -/
theorem manuscriptSentence_bilateralThreeZCommutes :
    (∀ x ∈ coreGroup (bilateralCellSet T k hP hTP), Commute (bilateralCell T k hP hTP).z x) ∧
      ((bilateralCell T k hP hTP).p * (bilateralCell T k hP hTP).f (-1) (-2) = 0 ∧
        (bilateralCell T k hP hTP).f (-1) (-2) * (bilateralCell T k hP hTP).p = 0) ∧
      Commute (bilateralCell T k hP hTP).z (bilateralCell T k hP hTP).W ∧
      ((bilateralCell T k hP hTP).u : ClopenCrossedProduct T k) * (bilateralCell T k hP hTP).r *
          (bilateralCell T k hP hTP).f (-1) (-2) =
        (bilateralCell T k hP hTP).f (-1) (-2) *
          (((bilateralCell T k hP hTP).u : ClopenCrossedProduct T k) *
            (bilateralCell T k hP hTP).r) ∧
      Commute (bilateralCell T k hP hTP).z (bilateralCell T k hP hTP).c ∧
      Commute (bilateralCell T k hP hTP).z (bilateralCell T k hP hTP).y := by
  have hS := (bilateralCell T k hP hTP).corner_of_mem_range (S := cellRing T k hP hTP)
  exact ⟨(bilateralCell T k hP hTP).z_commute_coreGroup hS,
    ⟨(bilateralCell T k hP hTP).p_mul_f (by norm_num : (-1 : ℤ) < 0) (-2),
      (bilateralCell T k hP hTP).f_mul_p (-1) (by norm_num : (-2 : ℤ) < 0)⟩,
    (bilateralCell T k hP hTP).z_commute_W, (bilateralCell T k hP hTP).W_z_scalar,
    (bilateralCell T k hP hTP).z_commute_c, (bilateralCell T k hP hTP).z_commute_y⟩

/-- **tex 1583–1587**, "So $\langle z\rangle$ is a nontrivial finite central subgroup of $B$, of
order $\operatorname{char}(k)$."  Under the printed standing hypothesis that `D = P∖T(P)` is
nonempty (tex 1550): `⟨z⟩ ≤ B`, every element of `⟨z⟩` commutes with every element of `B`,
`⟨z⟩ ≠ ⊥`, `⟨z⟩` is finite, and `|⟨z⟩| = orderOf z = char(k)`. -/
theorem manuscriptSentence_bilateralThreeZCentralOrderChar (hD : (P \ T '' P).Nonempty) :
    Subgroup.zpowers (bilateralCell T k hP hTP).z ≤
        (bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP) ∧
      (∀ x ∈ Subgroup.zpowers (bilateralCell T k hP hTP).z,
        ∀ g ∈ (bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP), Commute x g) ∧
      Subgroup.zpowers (bilateralCell T k hP hTP).z ≠ ⊥ ∧
      (Subgroup.zpowers (bilateralCell T k hP hTP).z :
        Set (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T k))ˣ).Finite ∧
      Nat.card ↥(Subgroup.zpowers (bilateralCell T k hP hTP).z) = ringChar k ∧
      orderOf (bilateralCell T k hP hTP).z = ringChar k := by
  obtain ⟨hzB, hcent, hne, hfin, hcard, hord⟩ :=
    manuscriptSentence_bilateralThreeZCentralOfOrderChar X T k P hP hTP hD
      (bilateralCellSet T k hP hTP)
      ((bilateralCell T k hP hTP).corner_of_mem_range (S := cellRing T k hP hTP)) ⟨1, rfl⟩
  refine ⟨Subgroup.zpowers_le.mpr hzB, ?_, hne, hfin, hcard, hord⟩
  intro x hx g hg
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (hcent g hg).zpow_left j

/-- **tex 1587–1588**, "Theorem~\ref{thm:compression-criterion} kills $z$ under every MF homomorphism
from $B$, hence from $\GL_3(R_X)$."  For compact metrizable `X` (the standing hypothesis on the
crossed product, tex 1345): every homomorphism from `B` to an MF group kills `z`, and so does every
homomorphism from `GL_3(R_X)`. -/
theorem manuscriptSentence_bilateralThreeCompressionKillsZ [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : ↥((bilateralCell T k hP hTP).B (bilateralCellSet T k hP hTP)) →* M,
          f ⟨(bilateralCell T k hP hTP).z, bilateralCell_z_mem_B T k hP hTP⟩ = 1) ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T k))ˣ →* M,
          f (bilateralCell T k hP hTP).z = 1 :=
  printedBilateralThreeCompressionKillsZ_closed X T k P hP hTP

/-- **tex 1589–1592**, "The identities $[z,e_{31}(f_{-2,0})]=e_{31}(f_{-1,0})$,
$[e_{23}(f_{0,-1}),e_{31}(f_{-1,0})]=e_{21}(d)$ then kill the defect root."  The two identities
hold with `d = 1_{P∖T(P)}`, and every homomorphism from `GL_3(R_X)` to an MF group kills
`e_{21}(d)`. -/
theorem manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    ⁅(bilateralCell T k hP hTP).z,
        elementaryUnit (2 : Fin 3) 0 (by decide) ((bilateralCell T k hP hTP).f (-2) 0)⁆ =
      elementaryUnit (2 : Fin 3) 0 (by decide) ((bilateralCell T k hP hTP).f (-1) 0) ∧
    ⁅elementaryUnit (1 : Fin 3) 2 (by decide) ((bilateralCell T k hP hTP).f 0 (-1)),
        elementaryUnit (2 : Fin 3) 0 (by decide) ((bilateralCell T k hP hTP).f (-1) 0)⁆ =
      elementaryUnit (1 : Fin 3) 0 (by decide) (defectD T k hP) ∧
    ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ f : (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T k))ˣ →* M,
        f (elementaryUnit (1 : Fin 3) 0 (by decide) (defectD T k hP)) = 1 := by
  have h1 := (bilateralCell T k hP hTP).commutator_z_root
  have h2 := (bilateralCell T k hP hTP).commutator_roots_defect
  rw [bilateralCell_d T k hP hTP] at h2
  refine ⟨h1, h2, fun M _ hM f => ?_⟩
  exact killed_of_commutators f
    ((printedBilateralThreeCompressionKillsZ_closed X T k P hP hTP).2 M hM f) h1 h2

end Clopen

end GroupApproximation.Manuscript.NonMF.BilateralB

#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeCInCentralizer
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeZInDefect
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeZCommutes
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeZCentralOrderChar
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeCompressionKillsZ
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralB.manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot
