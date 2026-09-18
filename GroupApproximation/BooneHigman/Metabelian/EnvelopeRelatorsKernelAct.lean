import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsKernelRange
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal-form words and their action on the Cantor set

* `rnKer_prod_localize_fix`, `rnKer_prod_localize_apply`: a product of maps localized at
  pairwise incomparable words acts on the cone of each word through that word's map alone.
* `rnKerWord H v L`: the word `v * Π (e * L(h) * e⁻¹)` in `RNFree X H`, for a list `L` of
  triples `(e, w, h)` (the word `w` records the cone `e` carries `[x₀]` to).
* `rnKerWord_mk`: its image in `RNFree X H ⧸ N` is `rfV v * Π rfConjL e h`.
* `rnKerWord_toPerm`: its image in `Sym(Cantor X)` is `v * Π localize w (cantorHom h)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

/-- Maps localized at words incomparable with `w` fix the cone of `w` pointwise. -/
theorem rnKer_prod_localize_fix {ι : Type*} (W : ι → List X) (G : ι → Equiv.Perm (Cantor X))
    (w : List X) (y : Cantor X) :
    ∀ M : List ι, (∀ i ∈ M, ¬ W i <+: w ∧ ¬ w <+: W i) →
      (M.map fun i => localize (W i) (G i)).prod (prepend w y) = prepend w y := by
  intro M
  induction M with
  | nil =>
    intro _
    simp
  | cons i M ih =>
    intro hM
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      ih fun j hj => hM j (List.mem_cons_of_mem i hj)]
    exact localize_apply_of_not
      (rcore_not_isStreamPrefix (hM i List.mem_cons_self).1 (hM i List.mem_cons_self).2 y) (G i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_prod_localize_fix

/-- On the cone of `W i`, a product of maps localized at pairwise incomparable words acts as
`localize (W i) (G i)`. -/
theorem rnKer_prod_localize_apply {ι : Type*} (W : ι → List X)
    (G : ι → Equiv.Perm (Cantor X)) :
    ∀ M : List ι, M.Pairwise (fun i j => ¬ W i <+: W j ∧ ¬ W j <+: W i) →
      ∀ i ∈ M, ∀ y : Cantor X,
        (M.map fun j => localize (W j) (G j)).prod (prepend (W i) y) =
          prepend (W i) (G i y) := by
  intro M
  induction M with
  | nil =>
    intro _ i hi
    exact absurd hi List.not_mem_nil
  | cons j M ih =>
    intro hM i hi y
    rw [List.pairwise_cons] at hM
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hi with hij | hi'
    · subst hij
      rw [rnKer_prod_localize_fix W G _ y M fun k hk => ⟨(hM.1 k hk).2, (hM.1 k hk).1⟩,
        localize_apply_prepend]
    · rw [ih hM.2 i hi' y]
      exact localize_apply_of_not
        (rcore_not_isStreamPrefix (hM.1 i hi').1 (hM.1 i hi').2 _) (G j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_prod_localize_apply

/-- The raw normal-form word `v * Π (e * L(h) * e⁻¹)` over a list of triples `(e, w, h)`. -/
def rnKerWord [Finite X] (H : Subgroup (TreeAut X)) (v : ↥(higmanThompsonV X))
    (L : List (↥(higmanThompsonV X) × List X × ↥H)) : RNFree X H :=
  nfV H v * (L.map fun p => nfV H p.1 * nfL H p.2.2 * (nfV H p.1)⁻¹).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKerWord

/-- The image of a raw normal-form word in the quotient. -/
theorem rnKerWord_mk [Finite X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (v : ↥(higmanThompsonV X)) (L : List (↥(higmanThompsonV X) × List X × ↥H)) :
    ((rnKerWord H v L : RNFree X H) : RNFree X H ⧸ N) =
      rfV H N v * (L.map fun p => rfConjL H N p.1 p.2.2).prod := by
  have hfun : (⇑(QuotientGroup.mk' N) ∘ fun p : ↥(higmanThompsonV X) × List X × ↥H =>
      nfV H p.1 * nfL H p.2.2 * (nfV H p.1)⁻¹) = fun p => rfConjL H N p.1 p.2.2 :=
    funext fun p => (rfConjL_apply H N p.1 p.2.2).symm
  show QuotientGroup.mk' N (rnKerWord H v L) = _
  rw [rnKerWord, map_mul, map_list_prod, List.map_map, hfun]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKerWord_mk

/-- The image of a raw normal-form word in `Sym(Cantor X)`, when each `e` carries `[x₀]` onto
its recorded word `w`. -/
theorem rnKerWord_toPerm [Finite X] (H : Subgroup (TreeAut X)) (x₀ : X)
    (v : ↥(higmanThompsonV X)) (L : List (↥(higmanThompsonV X) × List X × ↥H))
    (hL : ∀ p ∈ L, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) :
    rnFreeToPerm H x₀ (rnKerWord H v L) =
      (v : Equiv.Perm (Cantor X)) *
        (L.map fun p => localize p.2.1 (cantorHom (p.2.2 : TreeAut X))).prod := by
  have hmap : L.map (⇑(rnFreeToPerm H x₀) ∘ fun p : ↥(higmanThompsonV X) × List X × ↥H =>
      nfV H p.1 * nfL H p.2.2 * (nfV H p.1)⁻¹) =
      L.map fun p => localize p.2.1 (cantorHom (p.2.2 : TreeAut X)) :=
    List.map_congr_left fun p hp => by
      simp only [Function.comp_apply, map_mul, map_inv, nf_toPerm_V, nf_toPerm_L]
      exact (hL p hp).conj_localize _
  rw [rnKerWord, map_mul, map_list_prod, List.map_map, hmap, nf_toPerm_V]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKerWord_toPerm

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
