import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityNormalSubgroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# Step 2 of the simplicity proof: the tower product rule and the copy of `GL_d(F_2)`

`simple_kazhdan_sofic_group.tex` (HEAD), subsection "Simplicity", Step 2.

tex l.273–276:

> Since $\epsilon_{ab}\epsilon_{a'b'}=e_{a(V\cap b^{-1}a'V)}\,u_{ab^{-1}a'b'^{-1}}$
> and $b^{-1}a'\in B_{2w}$, we get
> $\epsilon_{ab}\epsilon_{a'b'}=\delta_{ba'}\epsilon_{ab'}$.

tex l.276–279:

> As $h\ne I_3$, $V$ is nonempty, so the $\epsilon_{ab}$ span a ring
> $A_V\cong M_{|B_w|}(\F_2)$ with unit $1_V=\sum_a\epsilon_{aa}$, and
> $y\mapsto(1-1_V)I_3+y$ embeds $\GL_3(A_V)\cong\GL_d(\F_2)$ in $\GL_3(R)$.

The ring `R` carries a covariant pair (`IsCovariantPair coeff u`: an injective
`coeff : LC(Z, F_2) → R` and units `u_ξ` with `u_ξ e_U = e_{ξU} u_ξ`), and `ε_ab = e_{aV} u_{ab⁻¹}`
is `SimpleKazhdanSofic.epsilon`. The balls `B_w ⊆ B_{2w}` are finite sets `B ⊆ D` with
`B = B⁻¹` and `B·B ⊆ D`, which the printed word-length balls satisfy.

Proof routes.
* `manuscriptSentence_epsilonProductRule`: expand the product with the covariance
  `u_{ab⁻¹} e_{a'V} = e_{ab⁻¹a'V} u_{ab⁻¹}` and multiply the indicators, using
  `aV ∩ ab⁻¹a'V = a(V ∩ b⁻¹a'V)`. Then `b⁻¹a' ∈ D` by the ball hypotheses. Since `V` is small,
  `V ∩ b⁻¹a'V = ∅` for `b ≠ a'`, so the translates `aV`, `a ∈ B`, are pairwise disjoint. The
  δ-rule is `General.epsilon_mul_epsilon`.
* `manuscriptSentence_epsilonRingAndCopy`: if `V = ∅` then `e_V = 0` and `h = e_ij(0) = I`.
  `ψ = General.epsilonHom` maps `M_B(F_2)` onto the span of the `ε_ab` (generators are images of
  matrix units, and `ψ(M) = ∑ M_ab ε_ab`). It is injective and multiplicative, so the span is a
  ring isomorphic to `M_B(F_2)` with unit `ψ(1) = ∑_a ε_aa`. `General.copyGL` is
  `y ↦ (1 - 1_V) I + y` on `GL_ι(A_V)`, composed with block flattening `GL_{ι×B}(F_2) ≅ GL_ι(M_B(F_2))`,
  and it is injective, with `|ι × B| = |ι|·|B|`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit1

open scoped Pointwise

variable {Λ Z R : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [Ring R] {coeff : LocallyConstant Z (ZMod 2) →+* R} {u : Λ →* Rˣ}

/-- **tex l.273–276.** For small `V` (condition (i): `V ∩ ξV = ∅` for `ξ ∈ D ∖ {e}`) and balls
`B = B⁻¹`, `B·B ⊆ D`: the product formula `ε_ab ε_a'b' = e_{a(V ∩ b⁻¹a'V)} u_{ab⁻¹a'b'⁻¹}`,
`b⁻¹a' ∈ D`, the resulting disjointness, and `ε_ab ε_a'b' = δ_{ba'} ε_ab'`. -/
theorem manuscriptSentence_epsilonProductRule [DecidableEq Λ] (hcov : IsCovariantPair coeff u)
    {D B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hsmall : ∀ ξ ∈ D, ξ ≠ 1 → Disjoint V (ξ • V))
    (hBinv : ∀ a ∈ B, a⁻¹ ∈ B) (hD : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ D) :
    (∀ a b a' b' : Λ, epsilon coeff u hV a b * epsilon coeff u hV a' b' =
        coeff (LocallyConstant.charFn (ZMod 2)
            (isClopen_smul a (hV.inter (isClopen_smul (b⁻¹ * a') hV)))) *
          (u (a * b⁻¹ * (a' * b'⁻¹)) : R)) ∧
      (∀ b ∈ B, ∀ a' ∈ B, b⁻¹ * a' ∈ D) ∧
      (∀ b ∈ B, ∀ a' ∈ B, b ≠ a' → V ∩ (b⁻¹ * a') • V = ∅) ∧
      TranslatesDisjoint B V ∧
      ∀ a b a' b' : Λ, b ∈ B → a' ∈ B →
        epsilon coeff u hV a b * epsilon coeff u hV a' b' =
          if b = a' then epsilon coeff u hV a b' else 0 := by
  have hBD : ∀ b ∈ B, ∀ a' ∈ B, b⁻¹ * a' ∈ D := fun b hb a' ha' => hD b⁻¹ (hBinv b hb) a' ha'
  have hdisj : TranslatesDisjoint B V := by
    intro a ha b hb hab
    rw [Set.disjoint_left]
    intro z hza hzb
    have h1 : a⁻¹ • z ∈ V := Set.mem_smul_set_iff_inv_smul_mem.mp hza
    have h2 : b⁻¹ • z ∈ V := Set.mem_smul_set_iff_inv_smul_mem.mp hzb
    have hne1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
    have hmem : a⁻¹ • z ∈ (a⁻¹ * b) • V := by
      rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
      exact h2
    exact Set.disjoint_left.mp (hsmall _ (hBD a ha b hb) hne1) h1 hmem
  refine ⟨fun a b a' b' => ?_, hBD, fun b hb a' ha' hba => ?_, hdisj,
    fun a b a' b' hb ha' => General.epsilon_mul_epsilon hcov hV hdisj hb ha'⟩
  · have hset : a • V ∩ (a * b⁻¹) • a' • V = a • (V ∩ (b⁻¹ * a') • V) := by
      rw [Set.smul_set_inter, smul_smul, smul_smul, mul_assoc]
    unfold epsilon
    rw [mul_assoc, ← mul_assoc (u (a * b⁻¹) : R), hcov.covariance (a * b⁻¹) (isClopen_smul a' hV),
      mul_assoc, ← Units.val_mul, ← map_mul u, ← mul_assoc, ← map_mul coeff,
      charFn_mul_charFn_inter]
    congr 2
    exact charFn_congr _ _ hset
  · have hne1 : b⁻¹ * a' ≠ 1 := fun h => hba (inv_mul_eq_one.mp h)
    exact Set.disjoint_iff_inter_eq_empty.mp (hsmall _ (hBD b hb a' ha') hne1)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_epsilonProductRule

/-- **tex l.276–279.** If `h = e_ij(e_V) ≠ I`, then `V` is nonempty; the `ε_ab`, `a, b ∈ B`, span
the image of the injective multiplicative map `ψ : M_B(F_2) → R` (so the span `A_V` is a ring
isomorphic to `M_{|B|}(F_2)`); its unit is `1_V = ψ(1) = ∑_a ε_aa`; and `y ↦ (1 - 1_V) I + y`
on `GL_ι(A_V) ≅ GL_{ι × B}(F_2)` is an injective homomorphism into `GL_ι(R)`, with
`|ι × B| = |ι|·|B|`. -/
theorem manuscriptSentence_epsilonRingAndCopy [DecidableEq Λ] (hcov : IsCovariantPair coeff u)
    {B : Finset Λ} {V : Set Z} (hV : IsClopen V) (hdisj : TranslatesDisjoint B V)
    (ι : Type*) [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (hh : elementaryUnit i j hij (coeff (LocallyConstant.charFn (ZMod 2) hV)) ≠ 1) :
    V.Nonempty ∧
      (∀ x : R, x ∈ epsilonSpan coeff u B hV ↔ ∃ M, General.epsilonHom hcov hdisj hV M = x) ∧
      Function.Injective (General.epsilonHom hcov hdisj hV) ∧
      (∀ x ∈ epsilonSpan coeff u B hV, ∀ y ∈ epsilonSpan coeff u B hV,
        x * y ∈ epsilonSpan coeff u B hV) ∧
      General.epsilonHom hcov hdisj hV 1 = ∑ a : B, epsilon coeff u hV a a ∧
      (∑ a : B, epsilon coeff u hV a a) ∈ epsilonSpan coeff u B hV ∧
      (∀ x ∈ epsilonSpan coeff u B hV,
        (∑ a : B, epsilon coeff u hV a a) * x = x ∧ x * (∑ a : B, epsilon coeff u hV a a) = x) ∧
      (∀ x : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ,
        ((General.copyGL hcov ι hdisj hV x : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
          Matrix.scalar ι (1 - ∑ a : B, epsilon coeff u hV a a) +
            ((General.blockFlatEquiv ι B x : (Matrix ι ι (Matrix B B (ZMod 2)))ˣ) :
              Matrix ι ι (Matrix B B (ZMod 2))).map (General.epsilonHom hcov hdisj hV)) ∧
      Function.Injective (General.copyGL hcov ι hdisj hV) ∧
      Fintype.card (ι × B) = Fintype.card ι * B.card := by
  have hne : V.Nonempty := by
    by_contra hne
    have hV0 : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h0 : LocallyConstant.charFn (ZMod 2) hV = 0 := by
      refine LocallyConstant.ext fun z => ?_
      have hz : z ∉ V := by
        rw [hV0]
        exact Set.notMem_empty z
      rw [LocallyConstant.coe_charFn, Set.indicator_of_notMem hz, LocallyConstant.zero_apply]
    rw [h0, map_zero, elementaryUnit_zero] at hh
    exact hh rfl
  have hgen : ∀ a b : B, epsilon coeff u hV a b ∈ epsilonSpan coeff u B hV :=
    fun a b => AddSubgroup.subset_closure ⟨a, a.2, b, b.2, rfl⟩
  have hspan : ∀ x : R, x ∈ epsilonSpan coeff u B hV ↔
      ∃ M, General.epsilonHom hcov hdisj hV M = x := by
    intro x
    refine ⟨fun hx => General.mem_range_epsilonHom_of_mem_epsilonSpan hcov hdisj hV hx, ?_⟩
    rintro ⟨M, rfl⟩
    rw [General.epsilonHom_apply]
    exact _root_.sum_mem fun a _ => _root_.sum_mem fun b _ => _root_.nsmul_mem (hgen a b) _
  have hone : General.epsilonHom hcov hdisj hV 1 = ∑ a : B, epsilon coeff u hV a a := by
    rw [General.epsilonHom_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hoff : ∀ b : B, b ≠ a →
        ((1 : Matrix B B (ZMod 2)) a b).val • epsilon coeff u hV a b = 0 := by
      intro b hb
      rw [Matrix.one_apply_ne hb.symm, ZMod.val_zero, zero_nsmul]
    rw [Fintype.sum_eq_single a hoff, Matrix.one_apply_eq, show (1 : ZMod 2).val = 1 from rfl,
      one_nsmul]
  have hmem1 : (∑ a : B, epsilon coeff u hV a a) ∈ epsilonSpan coeff u B hV := by
    rw [← hone]
    exact (hspan _).2 ⟨1, rfl⟩
  have hunit : ∀ x ∈ epsilonSpan coeff u B hV,
      (∑ a : B, epsilon coeff u hV a a) * x = x ∧ x * (∑ a : B, epsilon coeff u hV a a) = x := by
    intro x hx
    obtain ⟨M, rfl⟩ := (hspan x).1 hx
    refine ⟨?_, ?_⟩
    · rw [← hone, ← map_mul (General.epsilonHom hcov hdisj hV), one_mul]
    · rw [← hone, ← map_mul (General.epsilonHom hcov hdisj hV), mul_one]
  have hcopy1 : ∀ x : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ,
      ((General.copyGL hcov ι hdisj hV x : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
        Matrix.scalar ι (1 - General.epsilonHom hcov hdisj hV 1) +
          ((General.blockFlatEquiv ι B x : (Matrix ι ι (Matrix B B (ZMod 2)))ˣ) :
            Matrix ι ι (Matrix B B (ZMod 2))).map (General.epsilonHom hcov hdisj hV) :=
    fun _ => rfl
  have hcopy : ∀ x : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ,
      ((General.copyGL hcov ι hdisj hV x : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
        Matrix.scalar ι (1 - ∑ a : B, epsilon coeff u hV a a) +
          ((General.blockFlatEquiv ι B x : (Matrix ι ι (Matrix B B (ZMod 2)))ˣ) :
            Matrix ι ι (Matrix B B (ZMod 2))).map (General.epsilonHom hcov hdisj hV) := by
    intro x
    rw [hcopy1, hone]
  have hcard : Fintype.card (ι × B) = Fintype.card ι * B.card := by
    rw [Fintype.card_prod, Fintype.card_coe]
  exact ⟨hne, hspan, General.epsilonHom_injective hcov hdisj hV hne,
    fun x hx y hy => General.epsilonSpan_mul_mem hcov hV hdisj hx hy, hone, hmem1, hunit, hcopy,
    General.copyGL_injective hcov hdisj hV hne, hcard⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_epsilonRingAndCopy

end Audit1
end SimpleKazhdanSofic
end GroupApproximation
