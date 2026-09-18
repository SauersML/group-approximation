import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelSwap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.MatrixUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# Root elements of `(p)` generate a normal subgroup (lane `sk-cohn-02`, module 3)

Write `C = C_2(𝔽₂)`, `u(α, β) = α p β*` and `I = (p)`.  For a finite set `S` of binary words,
`relKer_gens N S` is the set of roots `x_ij(u(α, β))` with `α, β ∈ S`.  Put
`relKer_U N = ⋃_S ⟨relKer_gens N S⟩`.  This is a subgroup, since the closures are directed.

* `relKer_x_mem_U`: `x_ij(a) ∈ U` for every `a ∈ I`.  Over `𝔽₂`, `I` is the span of the
  `u(α, β)` (`CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan`), and `x_ij` is additive.
* `relKer_U_normal`: for `N ≥ 3`, `U` is normal.  A conjugate of a root in `U` by a
  non-opposite root is a product of roots with coefficients in `I`.  For the opposite root,
  write `x_ij(u(α, β)) = ⁅x_im(u(α, β)), x_mj(u(β, β))⁆` with a third index `m`, and use the
  non-opposite case twice.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup
open scoped commutatorElement

local notation "C₂" => CohnTwo (ZMod 2)
local notation "D₂" => CohnTwo.data (ZMod 2)

/-- `c ⁅a, b⁆ c⁻¹ = ⁅c a c⁻¹, c b c⁻¹⁆`. -/
theorem relKer_conj_commutator {G : Type*} [Group G] (c a b : G) :
    c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_commutator

/-- `P X⁻¹ P⁻¹ = (P X P⁻¹)⁻¹`. -/
theorem relKer_grp_conj_inv {G : Type*} [Group G] (P X : G) :
    P * X⁻¹ * P⁻¹ = (P * X * P⁻¹)⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_inv

/-- Conjugation by a product. -/
theorem relKer_grp_conj_conj {G : Type*} [Group G] (c d g : G) :
    c * d * g * (c * d)⁻¹ = c * (d * g * d⁻¹) * c⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_conj

/-- Conjugation by the inverse of a product. -/
theorem relKer_grp_conj_conj' {G : Type*} [Group G] (c d g : G) :
    (c * d)⁻¹ * g * (c * d)⁻¹⁻¹ = d⁻¹ * (c⁻¹ * g * c⁻¹⁻¹) * d⁻¹⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_conj'

/-- A subgroup contains the commutator of two of its elements. -/
theorem relKer_commutator_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_commutator_mem

/-- The matrix unit `u(α, β)` lies in `(p)`. -/
theorem relKer_unit_mem (u v : List (Fin 2)) : (D₂).unit u v ∈ CohnTwo.pIdeal (ZMod 2) := by
  have hp : CohnTwo.cohnP (ZMod 2) ∈ CohnTwo.pIdeal (ZMod 2) :=
    TwoSidedIdeal.subset_span (Set.mem_singleton _)
  show (D₂).word u * CohnTwo.cohnP (ZMod 2) * (D₂).coword v ∈ CohnTwo.pIdeal (ZMod 2)
  exact (CohnTwo.pIdeal (ZMod 2)).mul_mem_right _ _
    ((CohnTwo.pIdeal (ZMod 2)).mul_mem_left _ _ hp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_unit_mem

/-- Roots `x_ij(u(α, β))` with `α, β ∈ S`. -/
def relKer_gens (N : ℕ) (S : Finset (List (Fin 2))) : Set (SteinbergGroup (Fin N) C₂) :=
  {g | ∃ (i j : Fin N) (hij : i ≠ j) (u v : List (Fin 2)), u ∈ S ∧ v ∈ S ∧
    g = x i j hij ((D₂).unit u v)}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_gens

theorem relKer_gens_mono (N : ℕ) {S T : Finset (List (Fin 2))} (h : S ⊆ T) :
    relKer_gens N S ⊆ relKer_gens N T := by
  rintro g ⟨i, j, hij, u, v, hu, hv, rfl⟩
  exact ⟨i, j, hij, u, v, h hu, h hv, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_gens_mono

/-- The directed union `U = ⋃_S ⟨relKer_gens N S⟩`. -/
def relKer_U (N : ℕ) : Subgroup (SteinbergGroup (Fin N) C₂) where
  carrier := {g | ∃ S : Finset (List (Fin 2)), g ∈ Subgroup.closure (relKer_gens N S)}
  one_mem' := ⟨∅, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨S, hS⟩ ⟨T, hT⟩
    exact ⟨S ∪ T, Subgroup.mul_mem _
      (Subgroup.closure_mono (relKer_gens_mono N Finset.subset_union_left) hS)
      (Subgroup.closure_mono (relKer_gens_mono N Finset.subset_union_right) hT)⟩
  inv_mem' := by
    rintro a ⟨S, hS⟩
    exact ⟨S, Subgroup.inv_mem _ hS⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_U

theorem relKer_mem_U_iff (N : ℕ) (g : SteinbergGroup (Fin N) C₂) :
    g ∈ relKer_U N ↔ ∃ S : Finset (List (Fin 2)), g ∈ Subgroup.closure (relKer_gens N S) :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_mem_U_iff

/-- Every root with coefficient in `(p)` lies in `U`. -/
theorem relKer_x_mem_U (N : ℕ) (i j : Fin N) (hij : i ≠ j) (a : C₂)
    (ha : a ∈ CohnTwo.pIdeal (ZMod 2)) : x i j hij a ∈ relKer_U N := by
  rw [CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan, CohnTwo.matrixUnitSpan] at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨u, v⟩, rfl⟩ := hy
      exact (relKer_mem_U_iff N _).mpr ⟨{u, v}, Subgroup.subset_closure
        ⟨i, j, hij, u, v, Finset.mem_insert_self u {v},
          Finset.mem_insert_of_mem (Finset.mem_singleton_self v), rfl⟩⟩
  | zero => rw [x_zero]; exact (relKer_U N).one_mem
  | add y z _ _ hy hz => rw [← x_mul]; exact (relKer_U N).mul_mem hy hz
  | smul c y _ hy =>
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with h | h
      · rw [h, zero_smul, x_zero]; exact (relKer_U N).one_mem
      · rw [h, one_smul]; exact hy

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_x_mem_U

/-- A third index. -/
theorem relKer_third {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) : ∃ m : Fin N, m ≠ i ∧ m ≠ j := by
  have ht : ∃ t : ℕ, t < 3 ∧ t ≠ i.val ∧ t ≠ j.val := by
    by_cases h0 : 0 ≠ i.val ∧ 0 ≠ j.val
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i.val ∧ 1 ≠ j.val
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨t, ht3, hti, htj⟩ := ht
  exact ⟨⟨t, by omega⟩, fun h => hti (congrArg Fin.val h), fun h => htj (congrArg Fin.val h)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_third
/-- **Non-opposite conjugation.**  If `x_kl` is not opposite to `x_ij` and `a ∈ (p)`, then
`x_kl(b) x_ij(a) x_kl(b)⁻¹ ∈ U`. -/
theorem relKer_conj_nonopp {N : ℕ} (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l) (a b : C₂)
    (ha : a ∈ CohnTwo.pIdeal (ZMod 2)) (h : j ≠ k ∨ l ≠ i) :
    x k l hkl b * x i j hij a * (x k l hkl b)⁻¹ ∈ relKer_U N := by
  by_cases hjk : j = k
  · have hli : l ≠ i := h.resolve_left (fun h' => h' hjk)
    subst hjk
    rw [relKer_conj_right _ _ _ hij hkl (fun h' => hli h'.symm) a b]
    exact (relKer_U N).mul_mem
      (relKer_x_mem_U N _ _ _ _ ((CohnTwo.pIdeal (ZMod 2)).neg_mem
        ((CohnTwo.pIdeal (ZMod 2)).mul_mem_right _ _ ha)))
      (relKer_x_mem_U N _ _ hij a ha)
  · by_cases hli : l = i
    · subst hli
      rw [relKer_conj_left _ _ _ hkl hij (fun h' => hjk h'.symm) b a]
      exact (relKer_U N).mul_mem
        (relKer_x_mem_U N _ _ _ _ ((CohnTwo.pIdeal (ZMod 2)).mul_mem_left _ _ ha))
        (relKer_x_mem_U N _ _ hij a ha)
    · rw [(x_commute_of_ne k l i j hkl hij hli (fun h' => hjk h'.symm) b a).eq,
        mul_inv_cancel_right]
      exact relKer_x_mem_U N i j hij a ha

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_nonopp

/-- **Conjugating a generator.**  For `N ≥ 3`, every conjugate of `x_ij(u(α, β))` by a root
lies in `U`.  In the opposite case, split `x_ij(u(α, β))` as a commutator through a third
index. -/
theorem relKer_conj_gen {N : ℕ} (hN : 3 ≤ N) (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l)
    (u v : List (Fin 2)) (b : C₂) :
    x k l hkl b * x i j hij ((D₂).unit u v) * (x k l hkl b)⁻¹ ∈ relKer_U N := by
  by_cases hop : j = k ∧ l = i
  · obtain ⟨hjk, hli⟩ := hop
    obtain ⟨m, hmi, hmj⟩ := relKer_third hN i j
    have hu : (D₂).unit u v = (D₂).unit u v * (D₂).unit v v := by
      rw [(D₂).unit_mul_unit u v v v, if_pos rfl]
    rw [hu, ← x_commutator i m j (fun h => hmi h.symm) hmj hij ((D₂).unit u v)
      ((D₂).unit v v), relKer_conj_commutator]
    exact relKer_commutator_mem (relKer_U N)
      (relKer_conj_nonopp i m k l (fun h => hmi h.symm) hkl _ b (relKer_unit_mem u v)
        (Or.inl (fun h => hmj (h.trans hjk.symm))))
      (relKer_conj_nonopp m j k l hmj hkl _ b (relKer_unit_mem v v)
        (Or.inr (fun h => hmi (h.symm.trans hli))))
  · exact relKer_conj_nonopp i j k l hij hkl _ b (relKer_unit_mem u v) (not_and_or.mp hop)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_gen

/-- For `N ≥ 3`, `U` is stable under conjugation by a root. -/
theorem relKer_conj_x_mem {N : ℕ} (hN : 3 ≤ N) (k l : Fin N) (hkl : k ≠ l) (b : C₂)
    (g : SteinbergGroup (Fin N) C₂) (hg : g ∈ relKer_U N) :
    x k l hkl b * g * (x k l hkl b)⁻¹ ∈ relKer_U N := by
  obtain ⟨S, hS⟩ := (relKer_mem_U_iff N g).mp hg
  clear hg
  induction hS using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, j, hij, u, v, _, _, rfl⟩ := hy
      exact relKer_conj_gen hN i j k l hij hkl u v b
  | one =>
      rw [mul_one, mul_inv_cancel]
      exact (relKer_U N).one_mem
  | mul y z _ _ hy hz =>
      rw [relKer_grp_conj_mul]
      exact (relKer_U N).mul_mem hy hz
  | inv y _ hy =>
      rw [relKer_grp_conj_inv]
      exact (relKer_U N).inv_mem hy

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_x_mem

/-- **Normality.**  For `N ≥ 3`, `U` is a normal subgroup of `St_N(C_2)`. -/
theorem relKer_U_normal {N : ℕ} (hN : 3 ≤ N) : (relKer_U N).Normal := by
  have key : ∀ c : SteinbergGroup (Fin N) C₂, ∀ g ∈ relKer_U N,
      c * g * c⁻¹ ∈ relKer_U N ∧ c⁻¹ * g * c⁻¹⁻¹ ∈ relKer_U N := by
    intro c
    have hc : c ∈ Subgroup.closure
        (Set.range (PresentedGroup.of (rels := relations (I := Fin N) (R := C₂)))) := by
      rw [PresentedGroup.closure_range_of]
      exact Subgroup.mem_top c
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨⟨k, l, hkl, b⟩, rfl⟩ := hy
        change ∀ g ∈ relKer_U N, x k l hkl b * g * (x k l hkl b)⁻¹ ∈ relKer_U N ∧
          (x k l hkl b)⁻¹ * g * (x k l hkl b)⁻¹⁻¹ ∈ relKer_U N
        intro g hg
        refine ⟨relKer_conj_x_mem hN k l hkl b g hg, ?_⟩
        rw [← x_neg k l hkl b]
        exact relKer_conj_x_mem hN k l hkl (-b) g hg
    | one =>
        intro g hg
        simp only [one_mul, inv_one, mul_one, and_self]
        exact hg
    | mul c d _ _ hc hd =>
        intro g hg
        refine ⟨?_, ?_⟩
        · rw [relKer_grp_conj_conj c d g]
          exact (hc _ (hd g hg).1).1
        · rw [relKer_grp_conj_conj' c d g]
          exact (hd _ (hc g hg).2).2
    | inv c _ hc =>
        intro g hg
        refine ⟨(hc g hg).2, ?_⟩
        simpa only [inv_inv] using (hc g hg).1
  exact ⟨fun g hg c => (key c g hg).1⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_U_normal

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
