import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.ConfigBasic

/-!
# Relations G1, G2, G5, G6, G7 as equations in `G(M)`

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  These are the relations
of Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Sec. 4.1 used to show that the normal
closure of the `x`-letters is abelian (Lemma `lT`).  Letters are `Forward.kLet M s`.
Conventions as in `KMSPresentation`: `u^g = g⁻¹ u g`, `[u, v] = u⁻¹ v⁻¹ u v`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Sol

open Forward

variable {K N : ℕ} (M : Minsky.Machine K N)

/-! ## Membership of relators -/

theorem x_sq_mem (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) :
    gx j S ^ 2 ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ ?_))))))))
  unfold g1Relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ ?_)))
  exact ⟨j, S, rfl⟩

theorem x_comm_mem (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) :
    khComm (gx j S) (gx j' S') ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ ?_))))))))
  unfold g1Relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_right _ ?_)))
  exact ⟨j, j', S, S', rfl⟩

theorem bigA_sq_mem (i : Fin (K + 1)) : gA (N := N) i ^ 2 ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ ?_))))))))
  unfold g1Relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
  exact ⟨i, rfl⟩

theorem g5a_mem (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (i : Fin (K + 1)) (hi : i ∉ S) :
    khComm (gx j S) (gA i) * (gx j (insert i S))⁻¹ ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_)))))
  exact ⟨j, S, i, hi, rfl⟩

theorem g5b_mem (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (n : Fin K) (hn : n.succ ∉ S) :
    khConj (gx j S) (ga n) * (gx j S)⁻¹ * (khConj (gx j S) (ga' n))⁻¹ ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_right _ ?_))))
  exact ⟨j, S, n, hn, rfl⟩

theorem g5c_mem (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (s : KhGen K N) (i : Fin (K + 1))
    (hi : i ∈ S) (hs : s.block = some i) :
    khComm (gx j S) (FreeGroup.of s) ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_right _ ?_)))
  exact ⟨j, S, s, i, hi, hs, rfl⟩

theorem g6a_mem (j : Fin (N + 1)) (n : Fin K) :
    khConj (gx (K := K) j ∅) (ga n) * (khConj (gx j ∅) (gta n))⁻¹ ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
  unfold g6Relators
  refine Set.mem_union_left _ ?_
  exact ⟨j, n, rfl⟩

theorem g6b_mem (j : Fin (N + 1)) (n : Fin K) :
    khConj (gx (K := K) j ∅) (ga' n) * (khConj (gx j ∅) (gta' n))⁻¹ ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
  unfold g6Relators
  refine Set.mem_union_right _ ?_
  exact ⟨j, n, rfl⟩

theorem g7_mem (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) (α : Fin K → Fin 3) :
    khComm (khConj (gx j S) (zword ga α)) (gx j' S') ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
  exact ⟨j, j', S, S', α, rfl⟩

/-! ## G1 and G2 -/

theorem x_mul_self (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) :
    kLet M (.x j S) * kLet M (.x j S) = 1 := by
  have h := mk_eq_one_of_mem_relators M (x_sq_mem M j S)
  rw [map_pow, pow_two] at h
  exact h

theorem x_inv (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) :
    (kLet M (.x j S))⁻¹ = kLet M (.x j S) :=
  inv_eq_of_mul_eq_one_right (x_mul_self M j S)

theorem bigA_mul_self (i : Fin (K + 1)) : kLet M (.bigA i) * kLet M (.bigA i) = 1 := by
  have h := mk_eq_one_of_mem_relators M (bigA_sq_mem M i)
  rw [map_pow, pow_two] at h
  exact h

theorem bigA_inv (i : Fin (K + 1)) : (kLet M (.bigA i))⁻¹ = kLet M (.bigA i) :=
  inv_eq_of_mul_eq_one_right (bigA_mul_self M i)

theorem commute_x_x (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) :
    Commute (kLet M (.x j S)) (kLet M (.x j' S')) :=
  commute_kLet_of_mem M (x_comm_mem M j j' S S')

theorem commute_small {s t : KhGen K N} (hs : s.IsSmall) (ht : t.IsSmall) :
    Commute (kLet M s) (kLet M t) :=
  commute_kLet_of_mem M (small_mem_relators M hs ht)

theorem commute_block {s t : KhGen K N} {i i' : Fin (K + 1)} (hs : s.block = some i)
    (ht : t.block = some i') (hii' : i ≠ i') : Commute (kLet M s) (kLet M t) :=
  commute_kLet_of_mem M (block_mem_relators M hs ht hii')

/-! ## G5 -/

/-- G5 a): `x_{u A_i} = [x_u, A_i]` for `A_i ∉ u`. -/
theorem x_insert (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) {i : Fin (K + 1)} (hi : i ∉ S) :
    kLet M (.x j (insert i S)) =
      (kLet M (.x j S))⁻¹ * (kLet M (.bigA i))⁻¹ * kLet M (.x j S) * kLet M (.bigA i) := by
  have h := mk_eq_one_of_mem_relators M (g5a_mem M j S i hi)
  simp only [khComm, map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h).symm

/-- G5 b): `x_u^{a_i} x_u⁻¹ = x_u^{a'_i}` for `A_i ∉ u`, `i ≥ 1`. -/
theorem x_conj_a (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) {n : Fin K} (hn : n.succ ∉ S) :
    (kLet M (.a n))⁻¹ * kLet M (.x j S) * kLet M (.a n) * (kLet M (.x j S))⁻¹ =
      (kLet M (.a' n))⁻¹ * kLet M (.x j S) * kLet M (.a' n) := by
  have h := mk_eq_one_of_mem_relators M (g5b_mem M j S n hn)
  simp only [khConj, map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- G5 c): `[x_u, z] = 1` for `A_i ∈ u` and `z ∈ M_i`. -/
theorem commute_x_block (j : Fin (N + 1)) {S : Finset (Fin (K + 1))} {s : KhGen K N}
    {i : Fin (K + 1)} (hi : i ∈ S) (hs : s.block = some i) :
    Commute (kLet M (.x j S)) (kLet M s) :=
  commute_kLet_of_mem M (g5c_mem M j S s i hi hs)

/-! ## G6 -/

/-- G6: `x_{q_j}^{a_i} = x_{q_j}^{ã_i}`. -/
theorem x_empty_a (j : Fin (N + 1)) (n : Fin K) :
    (kLet M (.a n))⁻¹ * kLet M (.x j ∅) * kLet M (.a n) =
      (kLet M (.ta n))⁻¹ * kLet M (.x j ∅) * kLet M (.ta n) := by
  have h := mk_eq_one_of_mem_relators M (g6a_mem M j n)
  simp only [khConj, map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- G6: `x_{q_j}^{a'_i} = x_{q_j}^{ã'_i}`. -/
theorem x_empty_a' (j : Fin (N + 1)) (n : Fin K) :
    (kLet M (.a' n))⁻¹ * kLet M (.x j ∅) * kLet M (.a' n) =
      (kLet M (.ta' n))⁻¹ * kLet M (.x j ∅) * kLet M (.ta' n) := by
  have h := mk_eq_one_of_mem_relators M (g6b_mem M j n)
  simp only [khConj, map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-! ## G7 -/

/-- Homomorphisms commute with ordered products of powers. -/
theorem hom_foldl_zpow {F H : Type*} [Group F] [Group H] (φ : F →* H)
    (t : Fin K → F) (e : Fin K → ℤ) (L : List (Fin K)) (g : F) :
    φ (List.foldl (fun h n => h * t n ^ e n) g L)
      = List.foldl (fun h n => h * φ (t n) ^ e n) (φ g) L := by
  induction L generalizing g with
  | nil => rfl
  | cons n L ih =>
    simp only [List.foldl_cons]
    rw [ih, map_mul, map_zpow]

theorem mk_zword (t : Fin K → FreeGroup (KhGen K N)) (α : Fin K → Fin 3) :
    PresentedGroup.mk (relators M) (zword t α) =
      List.foldl (fun h n => h * PresentedGroup.mk (relators M) (t n) ^ (((α n).val : ℤ) - 1))
        1 (List.finRange K) := by
  unfold zword
  rw [hom_foldl_zpow, map_one]

/-- G7: `[x_u^{a_1^{ε_1} ⋯ a_K^{ε_K}}, x_v] = 1`. -/
theorem commute_g7 (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) (α : Fin K → Fin 3) :
    Commute ((PresentedGroup.mk (relators M) (zword ga α))⁻¹ * kLet M (.x j S) *
        PresentedGroup.mk (relators M) (zword ga α)) (kLet M (.x j' S')) := by
  have h := mk_eq_one_of_mem_relators M (g7_mem M j j' S S' α)
  rw [map_khComm (PresentedGroup.mk (relators M)),
    map_khConj (PresentedGroup.mk (relators M))] at h
  exact commute_of_khComm_eq_one h

end Sol

end KMS

end GroupApproximation.Full.Kharlampovich
