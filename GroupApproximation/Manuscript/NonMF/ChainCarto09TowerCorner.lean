import GroupApproximation.Manuscript.NonMF.RankBudget.TowerCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: tower corner and flattening without `hr : 1 ≤ r`

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`, tex 1731–1741:

> Thus $R_X$ is a unital corner of $M_{2r-1}(P_C)$, via $x\mapsto(b_i x a_j)_{ij}$.   (tex 1731–1732)
> Unitization embeds $\GL_{nr}(P_C)$ into $\GL_n(R_X)$.                               (tex 1739)
> For $n\ge2$, block elementary flattening puts the image of
> $\EL_{nr}(P_C)$ inside $\EL_n(R_X)$.                                                   (tex 1740–1741)

The standing hypothesis of the section (`sec:chain-core`, tex 1343):

> Let $X$ be a nonempty compact metrizable zero-dimensional space, and let $T\colon X\to X$ be a
> homeomorphism.

The endpoints of `Manuscript/NonMF/RankBudget/TowerCorner` (lines 70, 94, 125) carry an extra
hypothesis `hr : 1 ≤ r`, which the tex never prints.  This module restates the three sentences
with `hr` removed, replacing it by the printed hypothesis `[Nonempty X]` (tex 1343).

Proof route.  `one_le_of_isReturnSection`: a return section `C` of spread `r` satisfies
`X = ⋃_{|j|<r} T^j C` (`IsReturnSection.exists_mem_image`).  Applied to any point of the nonempty
`X` it produces `j : ℤ` with `0 ≤ |j| < r`, so `r ≥ 1`.  The three endpoints then call the corpus
endpoints with this derived `hr`; the statements are verbatim those of `TowerCorner` minus `hr`.

Static re-audit of the corpus route (no compilation):
* `ChainCore.returnTowerUnits k hC hr : ReturnTowerUnits R_X (2r-1) r`
  (`Dynamics/ReturnTowerCrossedProduct.lean:274`) uses `hr` only for the field `le : r ≤ 2r - 1`
  (`by omega`); its `p` is `coeff (charFn k hC.isClopen)`, definitionally `ChainCore.returnP k hC`
  (`Dynamics/ReturnRingUnit.lean:49`), so `τ.Base = Corner R_X τ.p _` and
  `ChainCore.ReturnCorner k hC = Corner R_X (returnP k hC) _` (`ReturnRingUnit.lean:203`) agree up to
  unfolding plus proof irrelevance.
* `τ.a i = towerA k hC ↑i`, `τ.b i = towerB k hC ↑i` by `rfl` (`returnTowerUnits_a/_b`), and
  `τ.lo a = Fin.castLE τ.le a` has value `↑a`, matching the printed `a_a`, `b_b` for `a < r`.
* `ReturnTowerUnits.cornerEquiv`, `flatUnitizeGL_injective`, `phi_one`, `map_flat_elementaryGroup_le`
  (`Algebra/ReturnTowerUnits.lean:210, 421, 309, 435`) take no `Statement` hypotheses.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto09

/-- A return section of spread `r` in a nonempty space forces `r ≥ 1`: covering a point by
`⋃_{|j|<r} T^j C` needs some integer `j` with `|j| < r`. -/
theorem one_le_of_isReturnSection {X : Type*} [TopologicalSpace X] [Nonempty X] {T : X ≃ₜ X}
    {r : ℕ} {C : Set X} (hC : GroupApproximation.ChainCore.IsReturnSection T r C) : 1 ≤ r := by
  obtain ⟨j, hj, -⟩ := hC.exists_mem_image (Classical.arbitrary X)
  have h0 : (0 : ℤ) < (r : ℤ) := lt_of_le_of_lt (abs_nonneg j) hj
  omega

/-- **tex 1731–1732**, "Thus $R_X$ is a unital corner of $M_{2r-1}(P_C)$, via
$x\mapsto(b_i x a_j)_{ij}$", for nonempty `X` (tex 1343) and no assumption on `r`. -/
theorem manuscriptSentence_returnRingUnitalCornerOfTowerMatrices
    {X : Type*} [TopologicalSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (k : Type*) [Ring k] (hC : GroupApproximation.ChainCore.IsReturnSection T r C) :
    ∃ (E : Matrix (Fin (2 * r - 1)) (Fin (2 * r - 1)) (GroupApproximation.ChainCore.ReturnCorner k hC))
      (hE : IsIdempotentElem E)
      (e : GroupApproximation.ClopenCrossedProduct T k ≃+*
        GroupApproximation.MFQuotientUnits.Corner
          (Matrix (Fin (2 * r - 1)) (Fin (2 * r - 1)) (GroupApproximation.ChainCore.ReturnCorner k hC))
          E hE),
      ∀ (x : GroupApproximation.ClopenCrossedProduct T k) (i j : Fin (2 * r - 1)),
        (((e x : Matrix (Fin (2 * r - 1)) (Fin (2 * r - 1))
              (GroupApproximation.ChainCore.ReturnCorner k hC)) i j :
            GroupApproximation.ChainCore.ReturnCorner k hC) : GroupApproximation.ClopenCrossedProduct T k) =
          GroupApproximation.ChainCore.towerB k hC i * x * GroupApproximation.ChainCore.towerA k hC j :=
  GroupApproximation.Manuscript.NonMF.RankBudget.manuscriptSentence_returnRingUnitalCornerOfTowerMatrices
    T k hC (one_le_of_isReturnSection hC)

/-- **tex 1739**, "Unitization embeds $\GL_{nr}(P_C)$ into $\GL_n(R_X)$", for nonempty `X`
(tex 1343) and no assumption on `r`: an injective `ψ : GL_{nr}(P_C) → GL_n(R_X)` with
`ψ(g)_{ij} = δ_{ij}(1 - ∑_{l<r} a_l b_l) + ∑_{a,b<r} a_a g_{(i,a),(j,b)} b_b`. -/
theorem manuscriptSentence_unitizationEmbedsGL
    {X : Type*} [TopologicalSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (k : Type*) [Ring k] (hC : GroupApproximation.ChainCore.IsReturnSection T r C)
    (n : ℕ) :
    ∃ ψ : (Matrix (Fin n × Fin r) (Fin n × Fin r) (GroupApproximation.ChainCore.ReturnCorner k hC))ˣ →*
        (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ,
      Function.Injective ψ ∧
        ∀ (g : (Matrix (Fin n × Fin r) (Fin n × Fin r) (GroupApproximation.ChainCore.ReturnCorner k hC))ˣ)
          (i j : Fin n),
          ((ψ g : (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ) :
              Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k)) i j =
            (if i = j then
                1 - ∑ l : Fin r,
                  GroupApproximation.ChainCore.towerA k hC l * GroupApproximation.ChainCore.towerB k hC l
              else 0) +
              ∑ a : Fin r, ∑ b : Fin r,
                GroupApproximation.ChainCore.towerA k hC a *
                  ((g : Matrix (Fin n × Fin r) (Fin n × Fin r)
                      (GroupApproximation.ChainCore.ReturnCorner k hC)) (i, a) (j, b) :
                    GroupApproximation.ClopenCrossedProduct T k) *
                  GroupApproximation.ChainCore.towerB k hC b :=
  GroupApproximation.Manuscript.NonMF.RankBudget.manuscriptSentence_unitizationEmbedsGL
    T k hC (one_le_of_isReturnSection hC) n

/-- **tex 1740–1741**, "For $n\ge2$, block elementary flattening puts the image of
$\EL_{nr}(P_C)$ inside $\EL_n(R_X)$", for nonempty `X` (tex 1343) and no assumption on `r`. -/
theorem manuscriptSentence_blockElementaryFlatteningMapsEL
    {X : Type*} [TopologicalSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (k : Type*) [Ring k] (hC : GroupApproximation.ChainCore.IsReturnSection T r C)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ ψ : (Matrix (Fin n × Fin r) (Fin n × Fin r) (GroupApproximation.ChainCore.ReturnCorner k hC))ˣ →*
        (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ,
      Function.Injective ψ ∧
        (∀ (g : (Matrix (Fin n × Fin r) (Fin n × Fin r) (GroupApproximation.ChainCore.ReturnCorner k hC))ˣ)
          (i j : Fin n),
          ((ψ g : (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ) :
              Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k)) i j =
            (if i = j then
                1 - ∑ l : Fin r,
                  GroupApproximation.ChainCore.towerA k hC l * GroupApproximation.ChainCore.towerB k hC l
              else 0) +
              ∑ a : Fin r, ∑ b : Fin r,
                GroupApproximation.ChainCore.towerA k hC a *
                  ((g : Matrix (Fin n × Fin r) (Fin n × Fin r)
                      (GroupApproximation.ChainCore.ReturnCorner k hC)) (i, a) (j, b) :
                    GroupApproximation.ClopenCrossedProduct T k) *
                  GroupApproximation.ChainCore.towerB k hC b) ∧
        (GroupApproximation.elementaryGroup (Fin n × Fin r)
            (GroupApproximation.ChainCore.ReturnCorner k hC)).map ψ ≤
          GroupApproximation.elementaryGroup (Fin n) (GroupApproximation.ClopenCrossedProduct T k) :=
  GroupApproximation.Manuscript.NonMF.RankBudget.manuscriptSentence_blockElementaryFlatteningMapsEL
    T k hC (one_le_of_isReturnSection hC) n hn

end GroupApproximation.Manuscript.NonMF.ChainCarto09

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto09.one_le_of_isReturnSection
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto09.manuscriptSentence_returnRingUnitalCornerOfTowerMatrices
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto09.manuscriptSentence_unitizationEmbedsGL
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto09.manuscriptSentence_blockElementaryFlatteningMapsEL
