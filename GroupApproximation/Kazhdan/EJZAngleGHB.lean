import GroupApproximation.Kazhdan.EJZAngleSylowFour
import GroupApproximation.Kazhdan.KazhdanControl

/-!
# Property (T) for the Kac--Moody--Steinberg group `GHB(7)`

Caprace--Conder--Kaluba--Witzel (arXiv:2011.09276), Theorem 1.3 for `p = 7`: `GHB(7)` has Kazhdan's
property (T).  The proof is theirs: the Ershov--Jaikin-Zapirain criterion (EJZ Corollary 3.3,
`ThreeVertexKazhdan.isKazhdanSubset_of_movingAngles`) applied to `⟨a⟩, ⟨b⟩, ⟨c⟩` with the angles of
the vertex groups `⟨a, b⟩ ≅ U₃(7)` and `⟨c, b⟩ ≅ ⟨c, a⟩ ≅ U₄(7)` (CCKW Proposition 7.3), which are
proved in `EJZAngleHeisenberg` and `EJZAngleSylowFour` from the relators of `GHB(7)` alone.

Constants: `e₃ = 0.378 ≥ 1/√7` for `(⟨a⟩, ⟨b⟩)`, `e₁ = e₂ = 0.5346 ≥ √(2/7)` for `(⟨b⟩, ⟨c⟩)` and
`(⟨a⟩, ⟨c⟩)`, and `ε₀ = 0.96`, with `2 · 0.5346² ≤ 0.96² · (1 − 0.378)`.  The two transversality
tables of `U₄(7)` are decided.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

open EJZAngleHeisenberg EJZAngleSylowFour EJZAngleSylowFourGram

section Relations

variable {G : Type*} [Group G]

/-- A trivial commutator means the two elements commute. -/
theorem commute_of_comm_eq_one {x y : G} (h : comm x y = 1) : Commute x y := by
  unfold Commute SemiconjBy
  have h' := congrArg (fun g ↦ y * x * g) h
  simpa [comm, mul_assoc] using h'

/-- Commutators stay in a subgroup containing both entries. -/
theorem comm_mem {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) : comm x y ∈ H := by
  unfold comm
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hx) (H.inv_mem hy)) hx) hy

/-- The central commutator of a Heisenberg pair has exponent `p` when `b` does. -/
theorem heisenberg_comm_pow {a b : G} {p : ℕ} (hb : b ^ p = 1)
    (hza : Commute (comm a b) a) (hzb : Commute (comm a b) b) : comm a b ^ p = 1 := by
  have h := mul_pow_eq_of_central hza hzb p
  simp only [hb, mul_one] at h
  exact mul_right_cancel (h.symm.trans (one_mul a).symm)

/-- The exponent tables of `U₄(7)`, decided on bounded witnesses. -/
theorem tableT_seven : ∀ i ∈ (Finset.range 7).erase 0, ∀ j ∈ (Finset.range 7).erase 0, i ≠ j →
    ∃ α ∈ Finset.range 7, ∃ β ∈ Finset.range 7,
      (i * α + j * β) % 7 = 0 ∧ (triangular i * α + triangular j * β) % 7 = 1 := by
  decide

/-- The second exponent table of `U₄(7)`. -/
theorem tableS_seven : ∀ i ∈ (Finset.range 7).erase 0, ∀ j ∈ (Finset.range 7).erase 0, i ≠ j →
    ∃ α ∈ Finset.range 7, ∃ β ∈ Finset.range 7, (i * α + j * β) % 7 = 0 ∧
      ((triangular i + i * (7 - i)) * α + (triangular j + j * (7 - j)) * β) % 7 = 1 := by
  decide

/-- **The `U₄(7)` data from the three relators.**  If `b⁷ = 1`, `[c,b,c] = [c,b,b,c] = [c,b,b,b] = 1`,
then `(c, b, [c,b], [c,b,b])` satisfy `SylowFourData 7`. -/
theorem sylowFourData_seven {c b : G} (hb : b ^ 7 = 1) (h1 : comm3 c b c = 1)
    (h2 : comm4 c b b c = 1) (h3 : comm4 c b b b = 1) :
    SylowFourData 7 c b (comm c b) (comm (comm c b) b) := by
  have hwc : Commute (comm c b) c := commute_of_comm_eq_one (x := comm c b) (y := c) h1
  have hzc : Commute (comm (comm c b) b) c :=
    commute_of_comm_eq_one (x := comm (comm c b) b) (y := c) h2
  have hzb : Commute (comm (comm c b) b) b :=
    commute_of_comm_eq_one (x := comm (comm c b) b) (y := b) h3
  have hzw : Commute (comm (comm c b) b) (comm c b) := by
    show Commute (comm (comm c b) b) (c⁻¹ * b⁻¹ * c * b)
    exact ((hzc.inv_right.mul_right hzb.inv_right).mul_right hzc).mul_right hzb
  have hab : c * b = b * c * comm c b := mul_eq_mul_mul_comm c b
  have hwb : comm c b * b = b * comm c b * comm (comm c b) b := mul_eq_mul_mul_comm (comm c b) b
  have hz : comm (comm c b) b ^ 7 = 1 := by
    have h := pow_mul_pow_eq_of_commutator hwb hzw hzb 1 7
    simp only [hb, pow_one, one_mul, mul_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one (comm c b)).symm)
  have hw : comm c b ^ 7 = 1 := by
    have h := mul_pow_eq_sylowFour hab hwb hzw hzb 7
    have htri : triangular 7 = 7 * 3 := rfl
    rw [hb, htri, pow_mul, hz, one_pow, mul_one, one_mul, mul_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one c).symm)
  exact
    { prime := Nat.prime_seven
      hab := hab
      hwb := hwb
      hwa := hwc
      hza := hzc
      hzb := hzb
      hzw := hzw
      hb := hb
      hw := hw
      hz := hz
      tableT := fun i hi j hj hij ↦ by
        obtain ⟨α, _, β, _, h⟩ := tableT_seven i hi j hj hij
        exact ⟨α, β, h⟩
      tableS := fun i hi j hj hij ↦ by
        obtain ⟨α, _, β, _, h⟩ := tableS_seven i hi j hj hij
        exact ⟨α, β, h⟩ }

end Relations

/-- The cyclic subgroups `⟨a⟩, ⟨b⟩, ⟨c⟩` generate `GHB(p)`. -/
theorem zpowers_sup_eq_top (p : ℕ) :
    Subgroup.zpowers (a p) ⊔ Subgroup.zpowers (b p) ⊔ Subgroup.zpowers (c p) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of (relators p), Subgroup.closure_le]
  rintro g ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers (a p)))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers (b p)))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (c p))

/-- The powers of an element of order dividing `7` are its first seven powers. -/
theorem zpowers_subset_image {G : Type*} [Group G] [DecidableEq G] {x : G} (hx : x ^ 7 = 1) :
    (Subgroup.zpowers x : Set G) ⊆ ((Finset.range 7).image fun k ↦ x ^ k : Finset G) := by
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hx' : x ^ (7 : ℤ) = 1 := by
    rw [← hx]
    exact zpow_natCast x 7
  rw [zpow_eq_zpow_emod k hx']
  have hnn : 0 ≤ k % (7 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hlt : k % (7 : ℤ) < 7 := Int.emod_lt_of_pos k (by norm_num)
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  refine ⟨(k % (7 : ℤ)).toNat, by omega, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]

/-- **`GHB(7)` has Kazhdan's property (T)** (CCKW Theorem 1.3 at `p = 7`), with no literature input:
the EJZ criterion and the `U₃(7)`, `U₄(7)` angles are proved in this development. -/
theorem hasKazhdanPropertyT_ghb7 : HasKazhdanPropertyT.{0, 0} (GHB 7) := by
  classical
  -- the three moving angles
  have hzab : Commute (comm (a 7) (b 7)) (a 7) :=
    commute_of_comm_eq_one (x := comm (a 7) (b 7)) (y := a 7) (rel_aba 7)
  have hzbb : Commute (comm (a 7) (b 7)) (b 7) :=
    commute_of_comm_eq_one (x := comm (a 7) (b 7)) (y := b 7) (rel_abb 7)
  have h₁₂ : ThreeVertexKazhdan.MovingAngleLE.{0, 0} (Subgroup.zpowers (a 7))
      (Subgroup.zpowers (b 7)) (378 / 1000) :=
    movingAngleLE_heisenberg Nat.prime_seven (b_pow 7) hzab hzbb
      (heisenberg_comm_pow (b_pow 7) hzab hzbb) (by norm_num) (by norm_num)
  have hdca := sylowFourData_seven (a_pow 7) (rel_cac 7) (rel_caac 7) (rel_caaa 7)
  have hdcb := sylowFourData_seven (b_pow 7) (rel_cbc 7) (rel_cbbc 7) (rel_cbbb 7)
  have hzca : comm (comm (c 7) (a 7)) (a 7) ∈ Subgroup.zpowers (c 7) ⊔ Subgroup.zpowers (a 7) :=
    comm_mem (comm_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hzcb : comm (comm (c 7) (b 7)) (b 7) ∈ Subgroup.zpowers (c 7) ⊔ Subgroup.zpowers (b 7) :=
    comm_mem (comm_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have h₁₃ : ThreeVertexKazhdan.MovingAngleLE.{0, 0} (Subgroup.zpowers (a 7))
      (Subgroup.zpowers (c 7)) (5346 / 10000) :=
    (movingAngleLE_sylowFour hdca hzca (by norm_num) (by norm_num)).symm
  have h₂₃ : ThreeVertexKazhdan.MovingAngleLE.{0, 0} (Subgroup.zpowers (b 7))
      (Subgroup.zpowers (c 7)) (5346 / 10000) :=
    (movingAngleLE_sylowFour hdcb hzcb (by norm_num) (by norm_num)).symm
  -- the Kazhdan subset
  have hK := ThreeVertexKazhdan.isKazhdanSubset_of_movingAngles (Subgroup.zpowers (a 7))
    (Subgroup.zpowers (b 7)) (Subgroup.zpowers (c 7)) (zpowers_sup_eq_top 7)
    (e₁ := 5346 / 10000) (e₂ := 5346 / 10000) (e₃ := 378 / 1000) (epsilon₀ := 96 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [max_self]; norm_num) h₁₂ h₁₃ h₂₃
  -- the finite Kazhdan pair
  let Q : Finset (GHB 7) := ((Finset.range 7).image fun k ↦ a 7 ^ k) ∪
    ((Finset.range 7).image fun k ↦ b 7 ^ k) ∪ ((Finset.range 7).image fun k ↦ c 7 ^ k)
  have hsub : (Subgroup.zpowers (a 7) : Set (GHB 7)) ∪ Subgroup.zpowers (b 7) ∪
      Subgroup.zpowers (c 7) ⊆ (Q : Set (GHB 7)) := by
    simp only [Q, Finset.coe_union]
    exact Set.union_subset_union (Set.union_subset_union (zpowers_subset_image (a_pow 7))
      (zpowers_subset_image (b_pow 7))) (zpowers_subset_image (c_pow 7))
  exact ⟨Q, _, IsKazhdanSubset.to_pair (hK.mono hsub)⟩

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.commute_of_comm_eq_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.heisenberg_comm_pow
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.tableT_seven
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.tableS_seven
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.sylowFourData_seven
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.zpowers_sup_eq_top
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.zpowers_subset_image
#audit_closed_axioms GroupApproximation.KMSGroup.GHBQuotient.hasKazhdanPropertyT_ghb7
