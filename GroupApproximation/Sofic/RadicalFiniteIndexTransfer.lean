import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.ThreeRadicalsCoincide

/-!
# Finite-index heredity for the MF radical, where it coincides with the finite residual

Section 49 of the ascending-HNN dossier proves
`Res_MF(H) = H ∩ Res_MF(G)` for every finite-index `H ≤ G`, by inducing a
corona representation of `H` to a block-monomial corona representation of `G`.
That induction is the analytic content and is not carried out here.

What *is* carried out is the half that needs no induction, and the transfer that
makes the other half free wherever the radicals are already known to coincide --
which is exactly the situation in the concrete affine family, by
`ThreeRadicalsCoincide` and the five-way refinement above it.  `Lemma 49.4` for
the finite residual is already proved in `Algebra/FiniteResidual`, so once
`Res_MF = Res_fin` on both sides the MF statement is a rewrite.

The consequence recorded at the end is Theorem 49.5: no finite-index subgroup
repairs the approximation failure.  Every finite-index subgroup of such a group
carries the *same* nontrivial radical and is therefore itself non-MF.  That is
the statement which upgrades "not MF" to "not virtually MF".
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **The easy half, for an arbitrary subgroup.**  Restriction of a corona
representation of `G` to `K` is a corona representation of `K`, so anything
invisible in `K` is invisible in `G`.  This is functoriality of the radical
along the inclusion. -/
theorem coe_mem_actualCoronaMFResidual_of_mem {K : Subgroup G} (x : K)
    (hx : x ∈ actualCoronaMFResidual K) :
    (x : G) ∈ actualCoronaMFResidual G :=
  map_actualCoronaMFResidual_le K.subtype (Subgroup.mem_map_of_mem _ hx)

/-- A finite-index subgroup contains the finite residual, since the residual is
the infimum over *all* finite-index subgroups. -/
theorem finiteResidual_le_of_finiteIndex (K : Subgroup G) [K.FiniteIndex] :
    finiteResidual G ≤ K :=
  sInf_le (by exact ‹K.FiniteIndex›)

/-- **§49.2, transferred.**  Wherever the MF radical and the finite residual
agree on both sides, the MF radical inherits the finite-index heredity of the
finite residual (`Lemma 49.4`), with no induction of representations. -/
theorem mem_actualCoronaMFResidual_subgroup_iff_of_eq_finiteResidual
    {K : Subgroup G} [K.FiniteIndex]
    (hG : actualCoronaMFResidual G = finiteResidual G)
    (hK : actualCoronaMFResidual K = finiteResidual K) (x : K) :
    x ∈ actualCoronaMFResidual K ↔ (x : G) ∈ actualCoronaMFResidual G := by
  rw [hK, hG]
  exact mem_finiteResidual_subgroup_iff x

/-- **Theorem 49.5.**  A finite-index subgroup carries the same nontrivial
radical, hence is not MF either: the failure is not a finite-index artifact and
cannot be repaired by passing to a subgroup of finite index. -/
theorem not_isCDEOperatorMF_of_finiteIndex_of_eq_finiteResidual
    {K : Subgroup G} [K.FiniteIndex] [Countable K]
    (hG : actualCoronaMFResidual G = finiteResidual G)
    (hK : actualCoronaMFResidual K = finiteResidual K)
    (hne : actualCoronaMFResidual G ≠ ⊥) :
    ¬ IsCDEOperatorMF K := by
  intro hmf
  -- an MF group has trivial radical
  have hbot : actualCoronaMFResidual K = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hmf
  -- but the ambient radical is nontrivial and sits inside `K`
  obtain ⟨x, hxmem, hxne⟩ : ∃ x : G, x ∈ actualCoronaMFResidual G ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (fun y hy => Subgroup.mem_bot.mpr (hcon y hy)) bot_le)
  have hxK : x ∈ K := by
    rw [hG] at hxmem
    exact finiteResidual_le_of_finiteIndex K hxmem
  have : (⟨x, hxK⟩ : K) ∈ actualCoronaMFResidual K :=
    (mem_actualCoronaMFResidual_subgroup_iff_of_eq_finiteResidual hG hK
      ⟨x, hxK⟩).mpr hxmem
  rw [hbot, Subgroup.mem_bot] at this
  exact hxne (congrArg Subtype.val this)

end GroupApproximation
