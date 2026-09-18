import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleCompressImage
import GroupApproximation.Meta.AxiomGuard

/-!
# A commutator of `V_X` carrying the complement of a cone into the cone

Second half of clause (C) (`RNCompressStatement`), model case.

Route.  Fix a letter `x`.  The product over the letters `y ≠ x` of the cone swaps
`[y] ↔ [x, y]` (`exists_shrink_list`, by induction on a duplicate-free list of letters) is an
`h ∈ V_X` fixing `cone [x, x]` pointwise and carrying `(cone [x])ᶜ` into `cone [x]`
(`exists_shrink`).  With `f ∈ V_X` mapping `cone [x, x]` onto `cone [x]` and `t = h * f`,
for `p ∉ cone [x]` the point `t⁻¹ p` lies in `cone [x, x]`, so `h⁻¹` fixes it and
`⁅h, t⁆ p = h p ∈ cone [x]` (`exists_commutator_shrink`).  Conjugating by `f ∈ V_X` mapping
`cone v` onto `cone [x]` gives the same for any nonempty `v`
(`exists_commutator_compress_cone`), with the commutator in `⁅V_X, V_X⁆`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

variable {X : Type*}

theorem notMem_cone_of_mapsCone {f : Equiv.Perm (Cantor X)} {v w : List X} {q : Cantor X}
    (hf : MapsCone f v w) (hq : q ∉ cone v) : f q ∉ cone w := by
  intro hfq
  obtain ⟨z, hz⟩ := mem_cone_iff.mp hfq
  rw [← hf z] at hz
  obtain rfl := Equiv.injective f hz
  exact hq (prepend_mem_cone v z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.notMem_cone_of_mapsCone

theorem mem_cone_singleton_of_eq {x : X} {p : Cantor X} (h : p 0 = x) : p ∈ cone [x] := by
  show IsStreamPrefix [x] p
  intro k hk
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.mem_cone_singleton_of_eq

theorem exists_shrink_list [Finite X] (x : X) (L : List X) (hnd : L.Nodup) (hx : x ∉ L) :
    ∃ h ∈ higmanThompsonV X, (∀ y, y ∉ L → ∀ p ∈ cone [x, y], h p = p) ∧
      (∀ y ∈ L, ∀ p ∈ cone [y], h p ∈ cone [x]) := by
  induction L with
  | nil => exact ⟨1, one_mem _, fun _ _ _ _ => rfl, fun _ hy => by simp at hy⟩
  | cons y L ih =>
    obtain ⟨hyL, hnd'⟩ := List.nodup_cons.mp hnd
    have hxL : x ∉ L := fun e => hx (List.mem_cons_of_mem y e)
    have hxy : x ≠ y := fun e => hx (by rw [e]; exact List.mem_cons_self)
    obtain ⟨h, hV, hfix, hmap⟩ := ih hnd' hxL
    have h1 : ¬ [y] <+: [x, y] := not_prefix_cons_of_ne hxy.symm [] [y]
    have h2 : ¬ [x, y] <+: [y] := not_prefix_cons_of_ne hxy [y] []
    refine ⟨h * coneSwap [y] [x, y] h1 h2, mul_mem hV (coneSwap_mem_higmanThompsonV h1 h2),
      ?_, ?_⟩
    · intro z hz p hp
      have hzy : z ≠ y := fun e => hz (by rw [e]; exact List.mem_cons_self)
      have hzL : z ∉ L := fun e => hz (List.mem_cons_of_mem y e)
      have n1 : ¬ IsStreamPrefix [y] p := fun hq =>
        Set.disjoint_left.mp (disjoint_cone (not_prefix_cons_of_ne hxy [z] [])
          (not_prefix_cons_of_ne hxy.symm [] [z])) hp hq
      have n2 : ¬ IsStreamPrefix [x, y] p := fun hq =>
        Set.disjoint_left.mp (disjoint_cone
          (fun e => hzy (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp e).2).1)
          (fun e => hzy (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp e).2).1.symm))
          hp hq
      show h (coneSwap [y] [x, y] h1 h2 p) = p
      rw [coneSwap_apply, coneSwapFun_of_not n1 n2]
      exact hfix z hzL p hp
    · intro z hz p hp
      show h (coneSwap [y] [x, y] h1 h2 p) ∈ cone [x]
      rcases List.mem_cons.mp hz with e | hzL
      · rw [e] at hp
        obtain ⟨q, rfl⟩ := mem_cone_iff.mp hp
        rw [mapsCone_coneSwap_left h1 h2 q, hfix y hyL _ (prepend_mem_cone [x, y] q)]
        exact cone_subset_of_prefix (⟨[y], rfl⟩ : [x] <+: [x, y]) (prepend_mem_cone [x, y] q)
      · have hzy : z ≠ y := fun e => hyL (by rw [← e]; exact hzL)
        have hzx : z ≠ x := fun e => hx (by rw [← e]; exact List.mem_cons_of_mem y hzL)
        have n1 : ¬ IsStreamPrefix [y] p := fun hq =>
          Set.disjoint_left.mp (disjoint_cone (not_prefix_cons_of_ne hzy [] [])
            (not_prefix_cons_of_ne hzy.symm [] [])) hp hq
        have n2 : ¬ IsStreamPrefix [x, y] p := fun hq =>
          Set.disjoint_left.mp (disjoint_cone (not_prefix_cons_of_ne hzx [] [y])
            (not_prefix_cons_of_ne hzx.symm [y] [])) hp hq
        rw [coneSwap_apply, coneSwapFun_of_not n1 n2]
        exact hmap z hzL p hp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_shrink_list

theorem exists_shrink [Finite X] (x : X) : ∃ h ∈ higmanThompsonV X,
    (∀ p ∈ cone [x, x], h p = p) ∧ (∀ p, p ∉ cone [x] → h p ∈ cone [x]) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨h, hV, hfix, hmap⟩ := exists_shrink_list x (Finset.univ.erase x).toList
    (Finset.nodup_toList _) (fun hx => by simp at hx)
  refine ⟨h, hV, hfix x (fun hx => by simp at hx), fun p hp => ?_⟩
  have hp0 : p 0 ≠ x := fun e => hp (mem_cone_singleton_of_eq e)
  exact hmap (p 0) (by simpa using hp0) p (mem_cone_singleton_of_eq rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_shrink

theorem exists_commutator_shrink [Finite X] [Nontrivial X] (x : X) :
    ∃ h ∈ higmanThompsonV X, ∃ t ∈ higmanThompsonV X,
      ∀ p, p ∉ cone [x] → ⁅h, t⁆ p ∈ cone [x] := by
  obtain ⟨h, hV, hfix, hmap⟩ := exists_shrink x
  obtain ⟨f, hfV, hf⟩ :=
    exists_mapsCone_of_ne_nil (List.cons_ne_nil x [x]) (List.cons_ne_nil x [])
  refine ⟨h, hV, h * f, mul_mem hV hfV, fun p hp => ?_⟩
  have e : (h * f) ((h * f)⁻¹ p) = p := Equiv.apply_symm_apply (h * f) p
  have ht : (h * f)⁻¹ p ∈ cone [x, x] := by
    by_contra hq
    have h1 : (h * f) ((h * f)⁻¹ p) ∈ cone [x] := hmap _ (notMem_cone_of_mapsCone hf hq)
    rw [e] at h1
    exact hp h1
  have hq1 : h⁻¹ ((h * f)⁻¹ p) = (h * f)⁻¹ p :=
    Equiv.Perm.inv_eq_iff_eq.mpr (hfix _ ht).symm
  rw [commutatorElement_def]
  show h ((h * f) (h⁻¹ ((h * f)⁻¹ p))) ∈ cone [x]
  rw [hq1, e]
  exact hmap p hp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_commutator_shrink

/-- A commutator of `V_X` carries the complement of any nonempty cone into the cone. -/
theorem exists_commutator_compress_cone [Finite X] [Nontrivial X] {v : List X} (hv : v ≠ []) :
    ∃ k ∈ ⁅higmanThompsonV X, higmanThompsonV X⁆, ∀ p, p ∉ cone v → k p ∈ cone v := by
  obtain ⟨x, -, -⟩ := exists_pair_ne X
  obtain ⟨h, hV, t, htV, hht⟩ := exists_commutator_shrink x
  obtain ⟨f, hfV, hf⟩ := exists_mapsCone_of_ne_nil hv (List.cons_ne_nil x [])
  refine ⟨f⁻¹ * ⁅h, t⁆ * f, ?_, fun p hp => ?_⟩
  · have hid : f⁻¹ * ⁅h, t⁆ * f = ⁅f⁻¹ * h * f, f⁻¹ * t * f⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem (inv_mem hfV) hV) hfV)
      (mul_mem (mul_mem (inv_mem hfV) htV) hfV)
  · obtain ⟨z, hz⟩ := mem_cone_iff.mp (hht (f p) (notMem_cone_of_mapsCone hf hp))
    show f⁻¹ (⁅h, t⁆ (f p)) ∈ cone v
    rw [hz, hf.inv z]
    exact prepend_mem_cone v z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_commutator_compress_cone

end GroupApproximation.BooneHigman.Metabelian.Envelope
