import GroupApproximation.GGT.SystolicDiscMovesAdapter
import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Steps of the distinct mirror fold

The distinct case of HC6 (`MirrorFoldDistinctStatement`) deletes an edge, folds two darts and
deletes a digon edge.  The disc it produces is read through an injective map of darts into the old
disc that commutes with face rotation.  This module proves the general facts used there.

* `EdgeDeletion.digonBack`: after deleting the edge of `a` from a digon `[a, b]`, the dart `b` is
  sent back to `alpha a` and every other dart to itself.  This commutes with face rotation
  (`EdgeDeletion.digonBack_facePerm`).
* `isFaceCycle_of_embed`: an injective dart map commuting with face rotation pulls face cycles back.
* `CycleDisc.exists_of_embed`: a planar map with such a dart map into a cycle disc, reading labels
  compatibly and covering the exterior cycle, is a cycle disc with the same boundary.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

open Equiv

universe u

variable {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}

/-- The value of a reversed dart of the deleted map. -/
theorem value_alpha (x : Dart M a) :
    value M a ((toCombMap M a).alpha x) = M.alpha (value M a x) :=
  alpha_val M a x

/-- After deleting the edge of `a` from a digon `[a, b]`, send `b` back to `alpha a`. -/
def digonBack (b : M.Dart) (x : Dart M a) : M.Dart :=
  if value M a x = b then M.alpha a else value M a x

theorem digonBack_of_eq {b : M.Dart} {x : Dart M a} (h : value M a x = b) :
    digonBack b x = M.alpha a :=
  if_pos h

theorem digonBack_of_ne {b : M.Dart} {x : Dart M a} (h : value M a x ≠ b) :
    digonBack b x = value M a x :=
  if_neg h

theorem digonBack_ne_self (b : M.Dart) (x : Dart M a) : digonBack b x ≠ a := by
  by_cases h : value M a x = b
  · rw [digonBack_of_eq h]
    exact M.alpha_fixedPointFree a
  · rw [digonBack_of_ne h]
    exact value_ne M a x

theorem digonBack_ne {b : M.Dart} (hb : M.alpha a ≠ b) (x : Dart M a) : digonBack b x ≠ b := by
  by_cases h : value M a x = b
  · rw [digonBack_of_eq h]
    exact hb
  · rw [digonBack_of_ne h]
    exact h

theorem digonBack_injective (b : M.Dart) : Function.Injective (digonBack (a := a) b) := by
  intro x y h
  apply value_injective M a
  by_cases hx : value M a x = b <;> by_cases hy : value M a y = b
  · rw [hx, hy]
  · rw [digonBack_of_eq hx, digonBack_of_ne hy] at h
    exact absurd h.symm (value_ne_reverse M a y)
  · rw [digonBack_of_ne hx, digonBack_of_eq hy] at h
    exact absurd h (value_ne_reverse M a x)
  · rwa [digonBack_of_ne hx, digonBack_of_ne hy] at h

/-- **Sending a digon dart back commutes with face rotation.** -/
theorem digonBack_facePerm {b : M.Dart} (hab : M.facePerm a = b) (hba : M.facePerm b = a)
    (hne : a ≠ b) (x : Dart M a) :
    digonBack b ((toCombMap M a).facePerm x) = M.facePerm (digonBack b x) := by
  have hx := value_ne M a x
  unfold digonBack
  rw [value_facePerm_eq_next]
  by_cases hzb : value M a x = b
  · rw [if_pos hzb]
    have hn : next M a (value M a x) = if M.facePerm (M.alpha a) = M.alpha a then M.facePerm a
        else M.facePerm (M.alpha a) := by
      unfold next
      rw [if_pos (show M.facePerm (value M a x) = a by rw [hzb, hba])]
    rw [hn]
    by_cases hl : M.facePerm (M.alpha a) = M.alpha a
    · rw [if_pos hl, if_pos hab, hl]
    · rw [if_neg hl, if_neg]
      intro h
      exact M.alpha_fixedPointFree a (M.facePerm.injective (h.trans hab.symm))
  · rw [if_neg hzb]
    have hfa : M.facePerm (value M a x) ≠ a := fun h =>
      hzb (M.facePerm.injective (h.trans hba.symm))
    by_cases hfr : M.facePerm (value M a x) = M.alpha a
    · have hn : next M a (value M a x) = b := by
        unfold next
        rw [if_neg hfa, if_pos hfr, if_neg (fun h => hne (h.symm.trans hab)), hab]
      rw [hn, if_pos rfl, hfr]
    · have hfb : M.facePerm (value M a x) ≠ b := fun h =>
        hx (M.facePerm.injective (h.trans hab.symm))
      rw [next_of_ne_of_ne M a hfa hfr, if_neg hfb]

end GroupApproximation.GGT.VanKampen.EdgeDeletion

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

/-- A list all of whose entries have preimages is a map. -/
theorem exists_map_eq_of_forall_mem {α β : Type*} (τ : α → β) :
    ∀ l : List β, (∀ z ∈ l, ∃ x, τ x = z) → ∃ l' : List α, l'.map τ = l
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
    obtain ⟨x, hx⟩ := h z (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨l', hl'⟩ := exists_map_eq_of_forall_mem τ l fun w hw => h w (List.mem_cons.mpr (Or.inr hw))
    exact ⟨x :: l', by rw [List.map_cons, hx, hl']⟩

/-- Powers of face rotation along a dart map commuting with face rotation. -/
theorem facePerm_pow_embed {N M : CombMap.{u}} {τ : N.Dart → M.Dart}
    (hcomm : ∀ x, τ (N.facePerm x) = M.facePerm (τ x)) (n : ℕ) (x : N.Dart) :
    τ ((N.facePerm ^ n) x) = (M.facePerm ^ n) (τ x) := by
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcomm, ih]

/-- **An injective dart map commuting with face rotation pulls face cycles back.** -/
theorem isFaceCycle_of_embed {N M : CombMap.{u}} {τ : N.Dart → M.Dart}
    (hτ : Function.Injective τ) (hcomm : ∀ x, τ (N.facePerm x) = M.facePerm (τ x))
    {l : List N.Dart} (hl : M.IsFaceCycle (l.map τ)) : N.IsFaceCycle l := by
  have hne : l ≠ [] := fun h => hl.ne_nil (by rw [h, List.map_nil])
  refine ⟨hne, hl.nodup.of_map τ, ?_, ?_⟩
  · have hc := hl.chain
    rw [List.isChain_map] at hc
    exact hc.imp fun x y h => hτ (by rw [hcomm, h])
  · apply hτ
    have hc := hl.closes
    rw [List.getLast_map, List.head_map] at hc
    rw [hcomm]
    exact hc

variable {V : Type u} {X : TriangleComplex V}

/-- **A planar map embedded in a cycle disc along face rotation is a cycle disc.**  The dart map
`τ` reads the start label of each new dart at its image, and the end label of `τ (alpha x)` is
the start label of `τ x`. -/
theorem CycleDisc.exists_of_embed (D : CycleDisc X) {N : CombMap.{0}} (hN : N.IsPlanar)
    (τ : N.Dart → D.map.Dart) (hτ : Function.Injective τ)
    (hcomm : ∀ x, τ (N.facePerm x) = D.map.facePerm (τ x))
    (hlab : ∀ x, D.lab (D.map.alpha (τ (N.alpha x))) = D.lab (τ x))
    (hrange : ∀ z ∈ D.cyc, ∃ x, τ x = z) :
    ∃ E : CycleDisc X, E.boundary = D.boundary ∧ E.map.faceCount = N.faceCount := by
  obtain ⟨l, hmap⟩ := exists_map_eq_of_forall_mem τ D.cyc hrange
  have hl : N.IsFaceCycle l := isFaceCycle_of_embed hτ hcomm (by rw [hmap]; exact D.isFaceCycle)
  have hsig : ∀ x, D.lab (τ (N.sigma x)) = D.lab (τ x) := fun x => by
    rw [← Systolic.facePerm_alpha N x, hcomm, Systolic.facePerm_apply, D.lab_sigma, hlab]
  have hadj : ∀ x, X.G.Adj (D.lab (τ x)) (D.lab (τ (N.alpha x))) := fun x => by
    have h := D.adj (τ (N.alpha x))
    rw [hlab] at h
    exact h.symm
  have htri : ∀ x, x ∉ l → (N.facePerm ^ 3) x = x ∧
      X.Tri (D.lab (τ x)) (D.lab (τ (N.facePerm x))) (D.lab (τ ((N.facePerm ^ 2) x))) := by
    intro x hx
    have hτx : τ x ∉ D.cyc := by
      rw [← hmap]
      exact fun h => hx ((List.mem_map_of_injective hτ).mp h)
    obtain ⟨h3, htri⟩ := D.tri (τ x) hτx
    refine ⟨hτ ?_, ?_⟩
    · rw [facePerm_pow_embed hcomm, h3]
    · rw [hcomm, facePerm_pow_embed hcomm]
      exact htri
  have hhead : τ (l.head hl.ne_nil) = D.cyc.head D.isFaceCycle.ne_nil := by
    have h1 := congrArg List.head? hmap
    rw [List.head?_map, List.head?_eq_some_head hl.ne_nil,
      List.head?_eq_some_head D.isFaceCycle.ne_nil] at h1
    exact Option.some.inj h1
  have hm : D.cyc.map D.lab = l.map (fun x => D.lab (τ x)) := by
    rw [← hmap]
    exact List.map_map
  let E : CycleDisc X :=
    { map := N
      planar := hN
      lab := fun x => D.lab (τ x)
      lab_sigma := hsig
      adj := hadj
      cyc := l
      isFaceCycle := hl
      tri := htri }
  refine ⟨E, ?_, rfl⟩
  show l.map (fun x => D.lab (τ x)) ++ [D.lab (τ (l.head hl.ne_nil))] =
    D.cyc.map D.lab ++ [D.lab (D.cyc.head D.isFaceCycle.ne_nil)]
  rw [hm, hhead]

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.digonBack_injective
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.digonBack_facePerm
#audit_axioms GroupApproximation.Systolic.isFaceCycle_of_embed
#audit_axioms GroupApproximation.Systolic.CycleDisc.exists_of_embed
