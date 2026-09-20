import GroupApproximation.BooneHigmanLinear.RelGen.SteinCell2
import Mathlib.Data.Finset.Max
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 6: L–S Theorem 4.8, `St̄(A, M) = U⁺(M) · H̄(A, M) · U⁻(M)`

Lane bh-pal-wire, k2-poly H.L3. `A` is local with maximal ideal `M`, and `I` is linearly ordered
with a third index for every pair. `thm48 : Thm48Statement`.

The proof is induction on a finset `K` of indices, adding a new maximum `L` each time
(`Finset.induction_on_max`). Put `Y K = U⁺_K(M) · H̄ · U⁻_K(M)` and
`qGroup K = ⟨x_ij(M) : i, j ∈ K⟩ ⊔ H̄`; the claim is `qGroup K ⊆ Y K`.

* The step works with `B = colG(K, L) · qGroup K · rowG(K, L) · H̄` (`BSet`). `B` is stable under
  left multiplication by every generator of `qGroup (insert L K)` (`B_mul_left`):
  * `H̄` and the `K`-roots conjugate each factor into itself (`SteinCell1`, `SteinCell2`);
  * a column root `x_iL` is absorbed in `colG`;
  * a row root `x_Lb(m)` needs work. Split the column `c = x_bL(d) c'`, apply the local rank-one
    identity `gl1` to `x_Lb(m) x_bL(d)`, move the new row root past `c'` (`row_mul_colEx`) and
    past `qGroup K`, which normalizes `rowG`.
* Hence `qGroup (insert L K) ⊆ B`. The induction hypothesis on the middle factor turns `B` into
  `Y (insert L K)`, because `L` is the maximum: column roots are positive and row roots negative.
* At `K = univ`, `qGroup univ = St(Φ, M) ⊔ H̄ = St̄(A, M)` by `relKer_eq_sup_hBar`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open IsLocalRing

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] [IsLocalRing A]

section Cells

variable (A) in
/-- `B = colG · qGroup K · rowG · H̄` at a new index `L`. -/
def BSet (K : Finset I) (L : I) : Set (SteinbergGroup I A) :=
  {g | ∃ c ∈ colG (maximalIdeal A) K L, ∃ q ∈ qGroup (maximalIdeal A) K,
    ∃ r ∈ rowG (maximalIdeal A) K L, ∃ t ∈ hBar I (maximalIdeal A), g = c * q * r * t}

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.BSet

variable (A) in
/-- The generators of `qGroup K`. -/
def genSet (K : Finset I) : Set (SteinbergGroup I A) :=
  {g | ∃ (i j : I) (hij : i ≠ j) (s : A), (i ∈ K ∧ j ∈ K) ∧ s ∈ maximalIdeal A ∧
    x i j hij s = g} ∪ (hBar I (maximalIdeal A) : Set (SteinbergGroup I A))

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.genSet

theorem qGroup_eq_closure (K : Finset I) :
    qGroup (maximalIdeal A) K = Subgroup.closure (genSet A K) := by
  rw [qGroup, rootGroup, genSet, Subgroup.closure_union, Subgroup.closure_eq]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_eq_closure

theorem genSet_inv {K : Finset I} {g : SteinbergGroup I A} (hg : g ∈ genSet A K) :
    g⁻¹ ∈ genSet A K := by
  rcases hg with ⟨i, j, hij, s, hP, hs, rfl⟩ | hg
  · exact Or.inl ⟨i, j, hij, -s, hP, neg_mem hs, by rw [x_neg]⟩
  · exact Or.inr (Subgroup.inv_mem _ hg)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.genSet_inv

theorem one_mem_BSet (K : Finset I) (L : I) : (1 : SteinbergGroup I A) ∈ BSet A K L :=
  ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _,
    by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.one_mem_BSet

variable (third : ThirdIndex I)
include third

/-- Left multiplication by `H̄` preserves `B`. -/
theorem B_mul_hBar {K : Finset I} {L : I} {g y : SteinbergGroup I A}
    (hg : g ∈ hBar I (maximalIdeal A)) (hy : y ∈ BSet A K L) : g * y ∈ BSet A K L := by
  obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hy
  refine ⟨g * c * g⁻¹, hBar_conj_rootGroup third hg hc, g * q * g⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hg) hq)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hg)),
    g * r * g⁻¹, hBar_conj_rootGroup third hg hr, g * t, Subgroup.mul_mem _ hg ht, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.B_mul_hBar

/-- Left multiplication by a `K`-root preserves `B`. -/
theorem B_mul_block {K : Finset I} {L : I} (hLK : L ∉ K) {i j : I} (hij : i ≠ j) (hi : i ∈ K)
    (hj : j ∈ K) {s : A} (hs : s ∈ maximalIdeal A) {y : SteinbergGroup I A}
    (hy : y ∈ BSet A K L) : x i j hij s * y ∈ BSet A K L := by
  obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hy
  have hx : x i j hij s ∈ qGroup (maximalIdeal A) K :=
    Subgroup.mem_sup_left (x_mem_rootGroup hij ⟨hi, hj⟩ hs)
  refine ⟨x i j hij s * c * (x i j hij s)⁻¹,
    conj_mem_of_mem_normalizer (qGroup_le_normalizer_colG third hLK hx) hc,
    x i j hij s * q, Subgroup.mul_mem _ hx hq, r, hr, t, ht, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.B_mul_block

omit third in
/-- Left multiplication by a column root preserves `B`. -/
theorem B_mul_col {K : Finset I} {L : I} {i : I} (hiL : i ≠ L) (hi : i ∈ K) {s : A}
    (hs : s ∈ maximalIdeal A) {y : SteinbergGroup I A} (hy : y ∈ BSet A K L) :
    x i L hiL s * y ∈ BSet A K L := by
  obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hy
  exact ⟨x i L hiL s * c, Subgroup.mul_mem _ (x_mem_rootGroup hiL ⟨hi, rfl⟩ hs) hc, q, hq, r,
    hr, t, ht, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.B_mul_col

/-- **Left multiplication by a row root preserves `B`** (the rank-one step). -/
theorem B_mul_row {K : Finset I} {L : I} (hLK : L ∉ K) {b : I} (hLb : L ≠ b) (hb : b ∈ K)
    {m : A} (hm : m ∈ maximalIdeal A) {y : SteinbergGroup I A} (hy : y ∈ BSet A K L) :
    x L b hLb m * y ∈ BSet A K L := by
  obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hy
  have hbL : b ≠ L := hLb.symm
  obtain ⟨d, hd, c', hc', rfl⟩ := split_col hbL hc
  have hu : IsUnit (1 + d * m) :=
    isUnit_of_sub_one_mem (by
      rw [add_sub_cancel_left]; exact (maximalIdeal A).mul_mem_right _ hd)
  obtain ⟨u, huv⟩ : ∃ u : Aˣ, (u : A) = 1 + d * m := ⟨hu.unit, hu.unit_spec⟩
  obtain ⟨H₀, hH₀, E⟩ := gl1 third hbL hd u huv
  obtain ⟨q₀, hq₀, E2⟩ := row_mul_colEx hLK hLb (m * ((u⁻¹ : Aˣ) : A)) hc'
  have hq₀' : q₀ ∈ qGroup (maximalIdeal A) K :=
    Subgroup.mem_sup_left (rootGroup_mono (fun i j h => ⟨h.1, h.2 ▸ hb⟩) hq₀)
  have hr₀ : q⁻¹ * x L b hLb (m * ((u⁻¹ : Aˣ) : A)) * q⁻¹⁻¹ ∈ rowG (maximalIdeal A) K L :=
    conj_mem_of_mem_normalizer (qGroup_le_normalizer_rowG third hLK (Subgroup.inv_mem _ hq))
      (x_mem_rootGroup hLb ⟨rfl, hb⟩ ((maximalIdeal A).mul_mem_right _ hm))
  have hxc : x b L hbL (d * ((u⁻¹ : Aˣ) : A)) ∈ colG (maximalIdeal A) K L :=
    x_mem_rootGroup hbL ⟨hb, rfl⟩ ((maximalIdeal A).mul_mem_right _ hd)
  have hc'' : c' ∈ colG (maximalIdeal A) K L :=
    rootGroup_mono (fun i j h => ⟨h.1, h.2.2⟩) hc'
  refine ⟨x b L hbL (d * ((u⁻¹ : Aˣ) : A)) * (H₀ * c' * H₀⁻¹),
    Subgroup.mul_mem _ hxc (hBar_conj_rootGroup third hH₀ hc''),
    H₀ * (q₀ * q) * H₀⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hH₀)
      (Subgroup.mul_mem _ hq₀' hq)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hH₀)),
    H₀ * ((q⁻¹ * x L b hLb (m * ((u⁻¹ : Aˣ) : A)) * q⁻¹⁻¹) * r) * H₀⁻¹,
    hBar_conj_rootGroup third hH₀ (Subgroup.mul_mem _ hr₀ hr),
    H₀ * t, Subgroup.mul_mem _ hH₀ ht, ?_⟩
  calc x L b hLb m * (x b L hbL d * c' * q * r * t)
      = (x L b hLb m * x b L hbL d) * c' * q * r * t := by group
    _ = x b L hbL (d * ((u⁻¹ : Aˣ) : A)) * H₀ * (x L b hLb (m * ((u⁻¹ : Aˣ) : A)) * c') *
          q * r * t := by rw [E]; group
    _ = x b L hbL (d * ((u⁻¹ : Aˣ) : A)) * H₀ *
          (c' * q₀ * x L b hLb (m * ((u⁻¹ : Aˣ) : A))) * q * r * t := by rw [E2]
    _ = _ := by group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.B_mul_row

/-- Left multiplication by any generator of `qGroup (insert L K)` preserves `B`. -/
theorem B_mul_gen {K : Finset I} {L : I} (hLK : L ∉ K) {g y : SteinbergGroup I A}
    (hg : g ∈ genSet A (insert L K)) (hy : y ∈ BSet A K L) : g * y ∈ BSet A K L := by
  rcases hg with ⟨i, j, hij, s, ⟨hi, hj⟩, hs, rfl⟩ | hg
  · rcases Finset.mem_insert.mp hi with rfl | hi
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact absurd rfl hij
      · exact B_mul_row third hLK hij hj hs hy
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact B_mul_col hij hi hs hy
      · exact B_mul_block third hLK hij hi hj hs hy
  · exact B_mul_hBar third hg hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.B_mul_gen

end Cells

section Induction

variable [LinearOrder I] (third : ThirdIndex I)
include third

/-- **The inductive claim.** Every element of `qGroup K` is `u t v` with `u ∈ U⁺_K(M)`,
`t ∈ H̄(A, M)` and `v ∈ U⁻_K(M)`. -/
theorem qGroup_subset_Y (K : Finset I) : ∀ g ∈ qGroup (maximalIdeal A) K,
    ∃ u ∈ rootGroup I (maximalIdeal A) (fun i j => i ∈ K ∧ j ∈ K ∧ i < j),
      ∃ t ∈ hBar I (maximalIdeal A),
        ∃ v ∈ rootGroup I (maximalIdeal A) (fun i j => i ∈ K ∧ j ∈ K ∧ j < i), g = u * t * v := by
  induction K using Finset.induction_on_max with
  | empty =>
    intro g hg
    have hle : qGroup (maximalIdeal A) (∅ : Finset I) ≤ hBar I (maximalIdeal A) := by
      refine sup_le ((Subgroup.closure_le _).mpr ?_) le_rfl
      rintro _ ⟨i, j, hij, s, ⟨hi, -⟩, -, rfl⟩
      exact absurd hi (Finset.notMem_empty i)
    exact ⟨1, Subgroup.one_mem _, g, hle hg, 1, Subgroup.one_mem _, by group⟩
  | insert L K hLK ih =>
    intro g hg
    have hLK' : L ∉ K := fun h => lt_irrefl L (hLK L h)
    rw [qGroup_eq_closure] at hg
    have hB : g ∈ BSet A K L := by
      induction hg using Subgroup.closure_induction_left with
      | one => exact one_mem_BSet K L
      | mul_left x hx y _ hy => exact B_mul_gen third hLK' hx hy
      | inv_mul_cancel x hx y _ hy => exact B_mul_gen third hLK' (genSet_inv hx) hy
    obtain ⟨c, hc, q, hq, r, hr, t, ht, rfl⟩ := hB
    obtain ⟨uK, huK, tK, htK, vK, hvK, rfl⟩ := ih q hq
    have hc' : c ∈ rootGroup I (maximalIdeal A)
        (fun i j => i ∈ insert L K ∧ j ∈ insert L K ∧ i < j) :=
      rootGroup_mono (fun i j h => ⟨Finset.mem_insert_of_mem h.1,
        h.2 ▸ Finset.mem_insert_self L K, h.2 ▸ hLK i h.1⟩) hc
    have huK' : uK ∈ rootGroup I (maximalIdeal A)
        (fun i j => i ∈ insert L K ∧ j ∈ insert L K ∧ i < j) :=
      rootGroup_mono (fun i j h => ⟨Finset.mem_insert_of_mem h.1,
        Finset.mem_insert_of_mem h.2.1, h.2.2⟩) huK
    have hvK' : vK ∈ rootGroup I (maximalIdeal A)
        (fun i j => i ∈ insert L K ∧ j ∈ insert L K ∧ j < i) :=
      rootGroup_mono (fun i j h => ⟨Finset.mem_insert_of_mem h.1,
        Finset.mem_insert_of_mem h.2.1, h.2.2⟩) hvK
    have hr' : r ∈ rootGroup I (maximalIdeal A)
        (fun i j => i ∈ insert L K ∧ j ∈ insert L K ∧ j < i) :=
      rootGroup_mono (fun i j h => ⟨h.1 ▸ Finset.mem_insert_self L K,
        Finset.mem_insert_of_mem h.2, h.1 ▸ hLK j h.2⟩) hr
    have hv : t⁻¹ * (vK * r) * t ∈ rootGroup I (maximalIdeal A)
        (fun i j => i ∈ insert L K ∧ j ∈ insert L K ∧ j < i) := by
      have := hBar_conj_rootGroup third (Subgroup.inv_mem _ ht) (Subgroup.mul_mem _ hvK' hr')
      rwa [inv_inv] at this
    exact ⟨c * uK, Subgroup.mul_mem _ hc' huK', tK * t, Subgroup.mul_mem _ htK ht,
      t⁻¹ * (vK * r) * t, hv, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_subset_Y

end Induction

/-- **L–S Theorem 4.8 (Stein), type A.** Over a local ring `A` with maximal ideal `M`,
`St̄(A, M) = U⁺(M) · H̄(A, M) · U⁻(M)`. -/
theorem thm48 : Thm48Statement := by
  intro I _ _ _ third A _ _ g hg
  rw [relKer_eq_sup_hBar third] at hg
  have hq : g ∈ qGroup (maximalIdeal A) (Finset.univ : Finset I) := by
    refine (sup_le_sup_right ?_ _) hg
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, j, hij, s, hs, rfl⟩
    exact x_mem_rootGroup hij ⟨Finset.mem_univ i, Finset.mem_univ j⟩ hs
  obtain ⟨u, hu, t, ht, v, hv, rfl⟩ := qGroup_subset_Y third Finset.univ g hq
  exact ⟨u, rootGroup_mono (fun i j h => h.2.2) hu, t, ht, v,
    rootGroup_mono (fun i j h => h.2.2) hv, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.thm48

end GroupApproximation.BooneHigmanLinear.RelGen
