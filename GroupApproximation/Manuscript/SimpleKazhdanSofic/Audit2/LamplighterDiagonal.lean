import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFDiagonalCommutators
import GroupApproximation.Meta.AxiomGuard

/-!
# Audit repair: `ξ ↦ diag(u_ξ,1,1)` over the lamplighter ring `R_Δ`

`simple_kazhdan_sofic_group.tex` at 1eefb3bbbf0eafe710276b85dbf87512c6ddc95a, proof of `lem:host`,
tex l.580–586:

> Finally, $\xi\mapsto\operatorname{diag}(u_\xi,1,1)$ is an injective homomorphism
> $\Lambda\to\GL_3(R_\Delta)$.  (census key `66cb283340f3`)
>
> It maps $[\Lambda,\Lambda]$ into $G_\Delta$, since over $\F_2$ every unit $v$ satisfies
> $\operatorname{diag}(v,v^{-1},1)=e_{12}(v)e_{21}(v^{-1})e_{12}(v)\,e_{12}(1)e_{21}(1)e_{12}(1)$, and
> the product of these matrices for $v=v_1$, $v_2$ and $(v_2v_1)^{-1}$ is
> $\operatorname{diag}(v_1v_2v_1^{-1}v_2^{-1},1,1)$. As $\Delta\le\Lambda$, the group
> $[\Lambda,\Lambda]$ contains $[\Delta,\Delta]$.  (census key `69f426d03d8f`)

The existing endpoints `printedLEFDiagonalEmbedding` and `printedLEFDiagonalIdentities` are stated
over an arbitrary ring with an injective `u : Λ →* Rˣ`, or with `2 = 0`. They never meet the concrete
`R_Δ`. This module puts them at `R_Δ = LampRing Δ`, `Λ = LampAffine Δ` and
`u = ClopenGroupCrossedProduct.unitHom`.

* `manuscriptSentence_lamplighterDiagonalEmbedding`: the injective homomorphism, with its values.
  Injectivity of `u` is `Lamplighter.unitHom_injective`.
* `two_eq_zero_lampRing`: `2 = 0` in `R_Δ`, which is the image of `2 = 0` in `F_2`.
* `manuscriptSentence_lamplighterDiagonalCommutators`: four facts.
  1. `2 = 0` in `R_Δ`.
  2. The printed identities over `R_Δ`, from `printedLEFDiagonalIdentities`.
  3. `[Λ,Λ]` maps into `G_Δ = EL_3(R_Δ)`, from `lefDiagonalHom_commutator_le`.
  4. `[Δ,Δ] ≤ [Λ,Λ]` through `δ ↦ (0, δ)`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit2

open RankNElimination Lamplighter

variable (Δ : Type) [Group Δ]

/-- **tex l.580–581.**  `ξ ↦ diag(u_ξ,1,1)` is an injective homomorphism `Λ → GL_3(R_Δ)`. -/
theorem manuscriptSentence_lamplighterDiagonalEmbedding :
    ∃ φ : LampAffine Δ →* (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ,
      Function.Injective φ ∧
        ∀ ξ : LampAffine Δ, (φ ξ : Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
          Matrix.diagonal
            ![((ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2) ξ :
              (LampRing Δ)ˣ) : LampRing Δ), 1, 1] :=
  ⟨lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2)),
    lefDiagonalHom_injective (unitHom_injective Δ), lefDiagonalHom_val _⟩

/-- `R_Δ` is an `F_2`-algebra: `2 = 0` in it. -/
theorem two_eq_zero_lampRing : (2 : LampRing Δ) = 0 := by
  have h' : ((ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)).comp
      (LocallyConstant.constRingHom : ZMod 2 →+* LocallyConstant (LampSpace Δ) (ZMod 2)))
        (2 : ZMod 2) = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, map_zero]
  calc
    (2 : LampRing Δ) = ((ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)).comp
      (LocallyConstant.constRingHom : ZMod 2 →+* LocallyConstant (LampSpace Δ) (ZMod 2)))
        (2 : ZMod 2) := (map_ofNat _ 2).symm
    _ = 0 := h'

/-- **tex l.581–586.**  Four facts.

1. `2 = 0` in `R_Δ`.
2. Every unit `v` of `R_Δ` satisfies
   `diag(v,v^{-1},1) = e_12(v)e_21(v^{-1})e_12(v) e_12(1)e_21(1)e_12(1)`. The product of these
   matrices for `v = c`, `c'`, `(c'c)^{-1}` is `diag(cc'c^{-1}c'^{-1},1,1)`.
3. `ξ ↦ diag(u_ξ,1,1)` maps `[Λ,Λ]` into `G_Δ = EL_3(R_Δ)`.
4. `[Δ,Δ] ≤ [Λ,Λ]`. -/
theorem manuscriptSentence_lamplighterDiagonalCommutators :
    (2 : LampRing Δ) = 0 ∧
      (∀ c c' : (LampRing Δ)ˣ,
        (∀ v : (LampRing Δ)ˣ,
          ((diagPairAt (0 : Fin 3) 1 v v⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
              Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
              Matrix.diagonal ![(v : LampRing Δ), ((v⁻¹ : (LampRing Δ)ˣ) : LampRing Δ), 1] ∧
            (diagPairAt (0 : Fin 3) 1 v v⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) =
              elementaryUnit 0 1 (by decide) (v : LampRing Δ) *
                  elementaryUnit 1 0 (by decide) ((v⁻¹ : (LampRing Δ)ˣ) : LampRing Δ) *
                  elementaryUnit 0 1 (by decide) (v : LampRing Δ) *
                (elementaryUnit 0 1 (by decide) 1 * elementaryUnit 1 0 (by decide) 1 *
                  elementaryUnit 0 1 (by decide) 1)) ∧
          (((diagPairAt (0 : Fin 3) 1 c c⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) *
              diagPairAt 0 1 c' c'⁻¹ * diagPairAt 0 1 (c' * c)⁻¹ ((c' * c)⁻¹)⁻¹ :
                (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
              Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
            Matrix.diagonal ![((c * c' * c⁻¹ * c'⁻¹ : (LampRing Δ)ˣ) : LampRing Δ), 1, 1]) ∧
        (commutator (LampAffine Δ)).map
            (lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))) ≤
          elementaryGroup (Fin 3) (LampRing Δ) ∧
          (commutator Δ).map (SemidirectProduct.inr : Δ →* LampAffine Δ) ≤
            commutator (LampAffine Δ) := by
  refine ⟨two_eq_zero_lampRing Δ, printedLEFDiagonalIdentities (LampRing Δ) (two_eq_zero_lampRing Δ),
    lefDiagonalHom_commutator_le _, ?_⟩
  rw [commutator_def, commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

end Audit2
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit2.manuscriptSentence_lamplighterDiagonalEmbedding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit2.two_eq_zero_lampRing
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit2.manuscriptSentence_lamplighterDiagonalCommutators
