import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsKernelFaithful
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel statement from the normal-form lemma

`rnKer_kernel_of_normalForm` proves `RNRelatorsCoreKernelStatement` from the residual
`RNKerNormalFormStatement`.  The residual says that every element of
`Q = RNFree X H ⧸ ⟪nfRelators H x₀⟫` can be written as `rfV v * Π rfConjL e_i h_i`, where
each `e_i` carries `cone [x₀]` onto `cone w_i` and the words `w_i` are pairwise incomparable.

The reduction is the faithfulness half of the Rover–Nekrashevych argument, and it is proved
here in full.  Take `k` in the kernel and write it in normal form.
1. The normal-form word acts trivially, so at some depth `D` every state of every `h_i` is
   trivial (`rnKer_states_trivial`).
2. Each factor `rfConjL e_i h_i` then lies in the image of `V_X`, by repeated splitting
   (`rnKer_rfConjL_mem_range`).  So `k ≡ nfV u` in `Q` for some `u ∈ V_X`.
3. `nfV u` acts trivially, so `u = 1` and `k ∈ ⟪nfRelators H x₀⟫`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **RESIDUAL: the normal-form lemma.**  Every element of the quotient
`RNFree X H ⧸ ⟪nfRelators H x₀⟫` equals `rfV v * Π rfConjL e_i h_i`, where each `e_i` carries
`cone [x₀]` onto `cone w_i` (`MapsCone`) and the recorded words `w_i` are pairwise
incomparable.

**THIS IS NOT LOGICALLY WEAKER THAN `RNRelatorsCoreKernelStatement`.  IT IS A SUB-STEP.**
Both are true propositions, and each follows from the other together with standard facts.
* Target ⇒ residual: if the target holds, `Q ≅ V_X(H)`.  Every `g ∈ V_X(H)` acts on some
  complete prefix code `{w_i}` of nonempty words by `w_i y ↦ u_i (h_i y)` with `h_i ∈ H`, so
  `g = v * Π localize w_i h_i = v * Π e_i (localize [x₀] h_i) e_i⁻¹`.
* Residual ⇒ target: `rnKer_kernel_of_normalForm` below.
What is proved here is the whole faithfulness half: the trivial action forces trivial deep
states, the splitting relators absorb those states into `V_X`, and `V_X` acts faithfully.
What remains is the existence half, i.e. rewriting an arbitrary word into normal form using
the commutation, disjoint-cone, splitting and root relators.

**Truth.** It is TRUE, being a consequence of the true target as described above.  The
finite-presentation hypotheses are carried along only to match the target's shape. -/
def RNKerNormalFormStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H → Group.IsFinitelyPresented ↥(higmanThompsonV X) →
      ∃ x₀ : X, ∀ q : RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀),
        ∃ (v : ↥(higmanThompsonV X)) (L : List (↥(higmanThompsonV X) × List X × ↥H)),
          (∀ p ∈ L, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) ∧
          L.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) ∧
          q = rfV H (Subgroup.normalClosure (nfRelators H x₀)) v *
            (L.map fun p =>
              rfConjL H (Subgroup.normalClosure (nfRelators H x₀)) p.1 p.2.2).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNKerNormalFormStatement

/-- **Endpoint.** The normal-form lemma gives the kernel statement. -/
theorem rnKer_kernel_of_normalForm (hNF : RNKerNormalFormStatement) :
    RNRelatorsCoreKernelStatement := by
  intro X _ _ H hH hfp hV
  obtain ⟨x₀, hq⟩ := hNF X H hH hfp hV
  refine ⟨x₀, fun k hk => ?_⟩
  have hS : nfSplitRelators H x₀ ⊆ nfRelators H x₀ := by
    intro r hr
    unfold nfRelators
    exact Set.mem_union_left _ (Set.mem_union_right _ hr)
  have hsplit : nfSplitRelators H x₀ ⊆ Subgroup.normalClosure (nfRelators H x₀) :=
    Set.Subset.trans hS Subgroup.subset_normalClosure
  have hNker : Subgroup.normalClosure (nfRelators H x₀) ≤ (rnFreeHom H x₀).ker :=
    Subgroup.normalClosure_le_normal (nfRelators_subset_ker H x₀)
  have hk1 : rnFreeToPerm H x₀ k = 1 := (nf_mem_ker_iff H x₀ k).mp hk
  obtain ⟨v, L, hL, hpair, hkq⟩ :=
    hq ((k : RNFree X H) : RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀))
  have hkq' : ((k : RNFree X H) : RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀)) =
      ((rnKerWord H v L : RNFree X H) :
        RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀)) :=
    hkq.trans (rnKerWord_mk H (Subgroup.normalClosure (nfRelators H x₀)) v L).symm
  have hw1 : rnFreeToPerm H x₀ (rnKerWord H v L) = 1 := by
    have hmem := hNker (QuotientGroup.eq.mp hkq')
    rw [nf_mem_ker_iff, map_mul, map_inv, hk1, inv_one, one_mul] at hmem
    exact hmem
  obtain ⟨D, hD⟩ := rnKer_states_trivial H x₀ v L hL hpair hw1
  have hrange : ((k : RNFree X H) : RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀)) ∈
      (rfV H (Subgroup.normalClosure (nfRelators H x₀))).range := by
    rw [hkq]
    refine Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨v, rfl⟩)
      (Subgroup.list_prod_mem _ fun y hy => ?_)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact rnKer_rfConjL_mem_range H _ hH x₀ hsplit D p.2.2 (hD p hp) p.1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hrange
  have hu' : ((nfV H u : RNFree X H) :
      RNFree X H ⧸ Subgroup.normalClosure (nfRelators H x₀)) = k := hu
  have hmem := hNker (QuotientGroup.eq.mp hu')
  rw [nf_mem_ker_iff, map_mul, map_inv, hk1, mul_one, nf_toPerm_V, inv_eq_one] at hmem
  have hu1 : u = 1 := Subtype.ext hmem
  rw [hu1, map_one] at hu
  exact (QuotientGroup.eq_one_iff k).mp hu.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_kernel_of_normalForm

/-- **Endpoint.** The normal-form lemma gives the finite core statement. -/
theorem rnKer_finiteCore_of_normalForm (hNF : RNKerNormalFormStatement) :
    RNRelatorsFiniteCoreStatement :=
  rnRelatorsFiniteCore_of_kernel (rnKer_kernel_of_normalForm hNF)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_finiteCore_of_normalForm

end GroupApproximation.BooneHigman.Metabelian.Envelope
