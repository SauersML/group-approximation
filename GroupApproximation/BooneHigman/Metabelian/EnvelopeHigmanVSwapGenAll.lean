import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenMove
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenInduct
import Mathlib.Data.Set.Finite.Lattice
import GroupApproximation.Meta.AxiomGuard

/-!
# The cone swaps generate `V_d`

Every element of `higmanThompsonV X` (`X` finite with at least two letters) lies in every
subgroup of `Equiv.Perm (Cantor X)` containing all cone swaps (`swapGen_mem_of_coneSwap_mem`);
equivalently, a subgroup of `V_X` containing all cone swaps is `⊤` (`swapGen_closure_eq_top`).

Proof: take a depth `N` of `f` and a bound `N + B` on the lengths of its targets, and induct on
`B`, and inside on the number of words of length `N` whose target has the maximal length
`N + B + 1`.
* `B = 0` (`swapGen_mem_base`): all targets have length `≤ N`, so `f⁻¹` has depth `N` with
  targets of length `≥ N`; by pigeonhole these have length exactly `N`, and `swapGen_leaf`
  applies to `f⁻¹`.
* Step (`swapGen_mem_step`): if a longest target `q' ++ [x]` exists, a target `p` of length `< N`
  exists (pigeonhole again), and `coneSwap p q' * f` has strictly fewer longest targets and the
  same bound (`swapGen_move`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- **Base case.** A prefix substitution of depth `N` with targets of length `≤ N` lies in every
subgroup containing all cone swaps. -/
theorem swapGen_mem_base [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    (hG : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G)
    {N : ℕ} {f : Equiv.Perm (Cantor X)}
    (hf : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N) : f ∈ G := by
  have hinv := swapGen_inv_ge hf
  have hleaf : f⁻¹ ∈ G := swapGen_leaf hG N f⁻¹ fun u hu => by
    obtain ⟨v, hv, -⟩ := hinv u hu
    exact ⟨v, hv, swapGen_length_eq_of_le hinv hu hv⟩
  have h2 := G.inv_mem hleaf
  rwa [inv_inv] at h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_mem_base

/-- **Inductive step** on the bound `N + B` for the lengths of the targets. -/
theorem swapGen_mem_step [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    (hG : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G) (B : ℕ)
    (ih : ∀ (N : ℕ) (f : Equiv.Perm (Cantor X)),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N + B) → f ∈ G)
    (N : ℕ) : ∀ f : Equiv.Perm (Cantor X),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N + (B + 1)) → f ∈ G := by
  suffices H : ∀ (n : ℕ) (f : Equiv.Perm (Cantor X)),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N + (B + 1)) →
      {u : List X | u.length = N ∧ ∃ v, MapsCone f u v ∧ v.length = N + B + 1}.ncard = n →
      f ∈ G from
    fun f hf => H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro f hf hn
    rcases Set.eq_empty_or_nonempty
      {u : List X | u.length = N ∧ ∃ v, MapsCone f u v ∧ v.length = N + B + 1} with hA | hA
    · refine ih N f fun w hw => ?_
      obtain ⟨v, hv, hvl⟩ := hf w hw
      refine ⟨v, hv, ?_⟩
      by_contra hlt
      exact Set.eq_empty_iff_forall_notMem.mp hA w ⟨hw, v, hv, by omega⟩
    obtain ⟨w₀, hw₀, q, hq, hqN⟩ := hA
    obtain ⟨q', x, rfl, hq'N⟩ := vgen_split_last hqN
    have hshort : ∃ wp p, wp.length = N ∧ MapsCone f wp p ∧ p.length < N := by
      by_contra hno
      have hge : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ N ≤ v.length :=
        fun w hw => by
          obtain ⟨v, hv, -⟩ := hf w hw
          refine ⟨v, hv, ?_⟩
          by_contra hlt
          exact hno ⟨w, v, hw, hv, by omega⟩
      have hl := swapGen_length_eq_of_le hge hw₀ hq
      omega
    obtain ⟨wp, p, hwp, hp, hpN⟩ := hshort
    obtain ⟨hpq, hqp⟩ := swapGen_move_incomparable hp hpN hwp hq hw₀ hq'N
    have hf' : ∀ w : List X, w.length = N →
        ∃ v, MapsCone (coneSwap p q' hpq hqp * f) w v ∧ v.length ≤ N + (B + 1) := by
      intro u hu
      obtain ⟨t, ht, htN⟩ := hf u hu
      obtain ⟨t', ht', hor⟩ :=
        swapGen_move hp hpN hwp hq hw₀ hq'N hpq hqp hu ht (by omega)
      refine ⟨t', ht', ?_⟩
      rcases hor with hl | ⟨htt, -⟩
      · omega
      · rw [htt]
        exact htN
    have hsub : {u : List X | u.length = N ∧
          ∃ v, MapsCone (coneSwap p q' hpq hqp * f) u v ∧ v.length = N + B + 1} ⊆
        {u : List X | u.length = N ∧ ∃ v, MapsCone f u v ∧ v.length = N + B + 1} := by
      rintro u ⟨hu, v, hv, hvN⟩
      obtain ⟨t, ht, htN⟩ := hf u hu
      obtain ⟨t', ht', hor⟩ :=
        swapGen_move hp hpN hwp hq hw₀ hq'N hpq hqp hu ht (by omega)
      rw [MapsCone.unique hv ht'] at hvN
      rcases hor with hl | ⟨htt, -⟩
      · omega
      · rw [htt] at hvN
        exact ⟨hu, t, ht, hvN⟩
    have hnot : w₀ ∉ {u : List X | u.length = N ∧
        ∃ v, MapsCone (coneSwap p q' hpq hqp * f) u v ∧ v.length = N + B + 1} := by
      rintro ⟨-, v, hv, hvN⟩
      obtain ⟨t', ht', hor⟩ :=
        swapGen_move hp hpN hwp hq hw₀ hq'N hpq hqp hw₀ hq (by omega)
      rw [MapsCone.unique hv ht'] at hvN
      rcases hor with hl | ⟨-, hno⟩
      · omega
      · exact hno (List.prefix_append q' [x])
    have hssub := (Set.ssubset_iff_of_subset hsub).mpr ⟨w₀, ⟨hw₀, q' ++ [x], hq, hqN⟩, hnot⟩
    have hlt := Set.ncard_lt_ncard hssub ((finite_words_length_eq N).subset fun u hu => hu.1)
    have hmem := ihn _ (by rw [← hn]; exact hlt) _ hf' rfl
    have hfeq : f = coneSwap p q' hpq hqp * (coneSwap p q' hpq hqp * f) := by
      rw [← mul_assoc, coneSwap_mul_self, one_mul]
    rw [hfeq]
    exact G.mul_mem (hG p q' hpq hqp) hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_mem_step

/-- Induction on the bound `N + B` for the lengths of the targets. -/
theorem swapGen_mem_of_bound [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    (hG : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G) (B : ℕ) :
    ∀ (N : ℕ) (f : Equiv.Perm (Cantor X)),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N + B) → f ∈ G := by
  induction B with
  | zero =>
    exact fun N f hf => swapGen_mem_base hG fun w hw =>
      (hf w hw).imp fun v hv => ⟨hv.1, by have hv2 := hv.2; omega⟩
  | succ B ih => exact fun N => swapGen_mem_step hG B ih N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_mem_of_bound

/-- **Part (A): the cone swaps generate `V_X`.** Every element of `higmanThompsonV X` lies in
every subgroup of `Equiv.Perm (Cantor X)` containing all cone swaps. -/
theorem swapGen_mem_of_coneSwap_mem [Finite X] [Nontrivial X]
    {G : Subgroup (Equiv.Perm (Cantor X))}
    (hG : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G)
    {f : Equiv.Perm (Cantor X)} (hf : f ∈ higmanThompsonV X) : f ∈ G := by
  obtain ⟨N, hN⟩ := mem_higmanThompsonV.mp hf
  obtain ⟨M, hM⟩ :=
    ((finite_words_length_eq N).image fun w : List X => (coneTarget f w).length).bddAbove
  refine swapGen_mem_of_bound hG (M - N) N f fun w hw => ?_
  obtain ⟨v, hv⟩ := hN w hw
  have hvt : coneTarget f w = v := MapsCone.unique (mapsCone_coneTarget ⟨v, hv⟩) hv
  have hle : (coneTarget f w).length ≤ M := hM ⟨w, hw, rfl⟩
  rw [hvt] at hle
  exact ⟨v, hv, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_mem_of_coneSwap_mem

/-- **Part (A), intrinsic form.** A subgroup of `V_X` containing all cone swaps is `⊤`. -/
theorem swapGen_closure_eq_top [Finite X] [Nontrivial X] {H : Subgroup ↥(higmanThompsonV X)}
    (hH : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v),
      (⟨coneSwap v w h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩ : ↥(higmanThompsonV X)) ∈ H) :
    H = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  have hmap : (g : Equiv.Perm (Cantor X)) ∈ H.map (higmanThompsonV X).subtype :=
    swapGen_mem_of_coneSwap_mem
      (fun v w h1 h2 => Subgroup.mem_map.mpr
        ⟨⟨coneSwap v w h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩, hH v w h1 h2, rfl⟩) g.2
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hmap
  have hy' : y = g := Subtype.ext hyg
  rw [← hy']
  exact hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_closure_eq_top

end GroupApproximation.BooneHigman.Metabelian.Envelope
