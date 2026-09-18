import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragCantor
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragPark
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleDisplace
import GroupApproximation.BooneHigman.V.Transitive
import GroupApproximation.Meta.AxiomGuard

/-!
# Fragmentation in `V_X(H)`: clause (F)

`rnFragmentsStatement_proof : RNFragmentsStatement`.

Route.  Let `K` be the closure of `fragPieces H` (elements of `V = V_X(H)` supported in two cones
of words of length `4`).  Members of `K` are products of pieces (`frag_exists_list`), and any two
pieces are jointly supported in a set missing a cone (`frag_pair`), so it suffices that `V ≤ K`.
* `frag_exists_transport`: cone swaps between long words are pieces, so `K` carries `cone v` onto
  `cone u` by a prefix substitution (`4 ≤ |u|, |v|`; two swaps through `c :: u'` if needed);
* `frag_of_mapsCone`: if `g ∈ V` maps `u y ↦ v (τ y)` with `τ ∈ V`, then `s * g * (u τ⁻¹)` fixes
  `cone u` pointwise, hence lies in `K` (`frag_park`), and so does `g`;
* the generators of `V`: elements of `V_X` (depth words with a letter tail, `τ = 1`) and
  `localize w h` (`u = w ++ c`, `v = w ++ h • c`, `τ = h|_c`, `frag_cantorHom_prepend`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

theorem frag_coneSwap_mem (H : Subgroup (TreeAut X)) {v w : List X} (hv : 4 ≤ v.length)
    (hw : 4 ≤ w.length) (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    coneSwap v w hvw hwv ∈ Subgroup.closure (fragPieces H) :=
  Subgroup.subset_closure (fragPieces_of_long
    (higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV hvw hwv)) hv hw
    (coneSwap_supportedIn hvw hwv))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_coneSwap_mem

/-- **Transport** of long cones inside the closure of the pieces. -/
theorem frag_exists_transport [Nontrivial X] (H : Subgroup (TreeAut X)) {u v : List X}
    (hu : 4 ≤ u.length) (hv : 4 ≤ v.length) :
    ∃ s ∈ Subgroup.closure (fragPieces H), MapsCone s v u := by
  have hu0 : u ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hv0 : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨a, u', rfl⟩ := List.exists_cons_of_ne_nil hu0
  obtain ⟨b, v', rfl⟩ := List.exists_cons_of_ne_nil hv0
  by_cases hab : b = a
  · obtain ⟨c, hc⟩ := exists_ne a
    have hcb : c ≠ b := fun h => hc (h.trans hab)
    have hz : 4 ≤ (c :: u').length := by
      simp only [List.length_cons] at hu ⊢
      omega
    have h1 : ¬ (b :: v') <+: (c :: u') := not_prefix_cons_of_ne (Ne.symm hcb) v' u'
    have h2 : ¬ (c :: u') <+: (b :: v') := not_prefix_cons_of_ne hcb u' v'
    have h3 : ¬ (c :: u') <+: (a :: u') := not_prefix_cons_of_ne hc u' u'
    have h4 : ¬ (a :: u') <+: (c :: u') := not_prefix_cons_of_ne (Ne.symm hc) u' u'
    refine ⟨coneSwap (c :: u') (a :: u') h3 h4 * coneSwap (b :: v') (c :: u') h1 h2,
      (Subgroup.closure (fragPieces H)).mul_mem (frag_coneSwap_mem H hz hu h3 h4)
        (frag_coneSwap_mem H hv hz h1 h2), ?_⟩
    exact (mapsCone_coneSwap_left h1 h2).comp (mapsCone_coneSwap_left h3 h4)
  · exact ⟨coneSwap (b :: v') (a :: u') (not_prefix_cons_of_ne hab v' u')
      (not_prefix_cons_of_ne (Ne.symm hab) u' v'), frag_coneSwap_mem H hv hu _ _,
      mapsCone_coneSwap_left _ _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_exists_transport

/-- **Step.**  An element of `V` carrying `cone u` onto `cone v` through `τ ∈ V` lies in the
closure of the pieces. -/
theorem frag_of_mapsCone [Nontrivial X] (H : Subgroup (TreeAut X)) {u v : List X}
    (hu : 4 ≤ u.length) (hv : 4 ≤ v.length) {g τ : Equiv.Perm (Cantor X)}
    (hg : g ∈ roverNekrashevych X H) (hτ : τ ∈ roverNekrashevych X H)
    (hgu : ∀ y, g (prepend u y) = prepend v (τ y)) : g ∈ Subgroup.closure (fragPieces H) := by
  obtain ⟨s, hs, hsvu⟩ := frag_exists_transport H hu hv
  have hτK : localize u τ ∈ Subgroup.closure (fragPieces H) :=
    Subgroup.subset_closure (fragPieces_of_long (frag_localize_mem H u hτ) hu hu
      ((localize_supportedIn u τ).mono Set.subset_union_left))
  have he : s * g * localize u (τ⁻¹) ∈ roverNekrashevych X H :=
    (roverNekrashevych X H).mul_mem ((roverNekrashevych X H).mul_mem (frag_closure_le H hs) hg)
      (frag_localize_mem H u ((roverNekrashevych X H).inv_mem hτ))
  have hfix : ∀ y, (s * g * localize u (τ⁻¹)) (prepend u y) = prepend u y := by
    intro y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, localize_apply_prepend, hgu, hsvu,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  have heK := frag_park H hu he hfix
  have hdecomp : g = s⁻¹ * (s * g * localize u (τ⁻¹)) * localize u τ := by
    simp only [map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [hdecomp]
  exact (Subgroup.closure (fragPieces H)).mul_mem
    ((Subgroup.closure (fragPieces H)).mul_mem ((Subgroup.closure (fragPieces H)).inv_mem hs)
      heK) hτK

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_of_mapsCone

/-- Generators from `V_X`. -/
theorem frag_of_V [Nontrivial X] (H : Subgroup (TreeAut X)) {f : Equiv.Perm (Cantor X)}
    (hf : f ∈ higmanThompsonV X) : f ∈ Subgroup.closure (fragPieces H) := by
  obtain ⟨x₀, -, -⟩ := exists_pair_ne X
  obtain ⟨M, hM⟩ := mem_higmanThompsonV.mp ((higmanThompsonV X).inv_mem hf)
  obtain ⟨r, hr⟩ := hM (List.replicate M x₀) List.length_replicate
  have hr' :
      MapsCone f (r ++ List.replicate 4 x₀) (List.replicate M x₀ ++ List.replicate 4 x₀) := by
    have h := hr.inv
    rw [inv_inv] at h
    exact h.append _
  have hu : 4 ≤ (r ++ List.replicate 4 x₀).length := by
    rw [List.length_append, List.length_replicate]
    omega
  have hv : 4 ≤ (List.replicate M x₀ ++ List.replicate 4 x₀).length := by
    rw [List.length_append, List.length_replicate, List.length_replicate]
    omega
  refine frag_of_mapsCone H (τ := 1) hu hv (higmanThompsonV_le_rn H hf)
    (roverNekrashevych X H).one_mem fun y => ?_
  rw [Equiv.Perm.one_apply]
  exact hr' y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_of_V

/-- Generators `localize w h` with `h ∈ H`. -/
theorem frag_of_localize [Nontrivial X] (H : Subgroup (TreeAut X)) (hH : IsSelfSimilar H)
    (w : List X) {h : TreeAut X} (hh : h ∈ H) :
    localize w (cantorHom h) ∈ Subgroup.closure (fragPieces H) := by
  obtain ⟨x₀, -, -⟩ := exists_pair_ne X
  have hu : 4 ≤ (w ++ List.replicate 4 x₀).length := by
    rw [List.length_append, List.length_replicate]
    omega
  have hv : 4 ≤ (w ++ h • List.replicate 4 x₀).length := by
    rw [List.length_append, TreeAut.length_smul, List.length_replicate]
    omega
  refine frag_of_mapsCone H hu hv (localize_mem_roverNekrashevych H w hh)
    (cantorHom_mem_roverNekrashevych H (hH.state_mem hh (List.replicate 4 x₀))) fun y => ?_
  rw [prepend_append, localize_apply_prepend, frag_cantorHom_prepend, prepend_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_of_localize

theorem frag_rn_le_closure [Nontrivial X] (H : Subgroup (TreeAut X)) (hH : IsSelfSimilar H) :
    roverNekrashevych X H ≤ Subgroup.closure (fragPieces H) := by
  refine (Subgroup.closure_le _).mpr ?_
  intro f hf
  rcases hf with hf | ⟨w, h, hh, rfl⟩
  · exact frag_of_V H hf
  · exact frag_of_localize H hH w hh

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_rn_le_closure

end

/-- **Clause (F).**  `V_X(H)` fragments into pieces jointly supported in sets missing a cone. -/
theorem rnFragmentsStatement_proof : RNFragmentsStatement := by
  intro X _ _ H hH g₁ hg₁ g₂ hg₂
  obtain ⟨l₁, hl₁, hp₁⟩ := frag_exists_list (frag_rn_le_closure H hH hg₁)
  obtain ⟨l₂, hl₂, hp₂⟩ := frag_exists_list (frag_rn_le_closure H hH hg₂)
  exact ⟨l₁, l₂, fun a ha => (mem_fragPieces.mp (hl₁ a ha)).1,
    fun b hb => (mem_fragPieces.mp (hl₂ b hb)).1, hp₁, hp₂,
    fun a ha b hb => frag_pair (hl₁ a ha) (hl₂ b hb)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFragmentsStatement_proof

/-- `RNDisplaceCompressStatement` reduces to compression alone. -/
theorem rnDisplaceCompress_of_compress (hC : RNCompressStatement) :
    RNDisplaceCompressStatement :=
  rnDisplaceCompress_of_compress_fragments hC rnFragmentsStatement_proof

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnDisplaceCompress_of_compress

end GroupApproximation.BooneHigman.Metabelian.Envelope
