import Mathlib

/-!
# The Coxeter relations present the finite symmetric groups

Kourovka 17.61 lane, the finite presentation of `CT_P(ℤ)` (research node
`ct-p-z-is-finitely-presented-by-position-shifting`). There, cell permutations at level `n` are
words in adjacent swaps. We need that two such words with the same effect are equal in any group
where the images of the swaps satisfy the Coxeter relations.

For `b : ℕ → G` satisfying the Coxeter relations for the indices `< N` (`IsCox b N`), and two
words `w, w'` in `{0, …, N-1}` whose products of the adjacent swaps `swap k (k+1)` in `Perm ℕ`
agree, the products of the `b k` agree (`prod_eq_of_perm_eq`). The proof is the classical
right-transversal argument: the cycles `s_N ⋯ s_j` are coset representatives of the stabilizer of
`N + 1`.
-/

namespace GroupApproximation.ClassTransposition.Presentation.Coxeter

open Equiv

variable {G : Type*} [Group G]

/-- The Coxeter relations for `b 0, …, b (N-1)`. -/
structure IsCox (b : ℕ → G) (N : ℕ) : Prop where
  sq : ∀ k, k < N → b k * b k = 1
  br : ∀ k, k + 1 < N → b k * b (k + 1) * b k = b (k + 1) * b k * b (k + 1)
  far : ∀ k l, k + 2 ≤ l → l < N → b k * b l = b l * b k

/-- `b N * b (N-1) * ⋯ * b j` (empty for `j = N + 1`). -/
def cprod (b : ℕ → G) (N j : ℕ) : G := ((List.range' j (N + 1 - j)).reverse.map b).prod

theorem cprod_top (b : ℕ → G) (N : ℕ) : cprod b N (N + 1) = 1 := by
  simp [cprod]

theorem cprod_succ (b : ℕ → G) {N j : ℕ} (hj : j ≤ N) :
    cprod b N j = cprod b N (j + 1) * b j := by
  unfold cprod
  rw [show N + 1 - j = (N - j) + 1 by omega, List.range'_succ, List.reverse_cons,
    List.map_append, List.prod_append, show N + 1 - (j + 1) = N - j by omega]
  simp

section Cox

variable {b : ℕ → G} {N : ℕ}

/-- `b k` commutes with `b N ⋯ b j` when `k + 2 ≤ j`. -/
theorem comm_cprod (hb : IsCox b (N + 1)) {k : ℕ} :
    ∀ d j, j + d = N + 1 → k + 2 ≤ j → b k * cprod b N j = cprod b N j * b k := by
  intro d
  induction d with
  | zero => intro j hj _; rw [show j = N + 1 by omega, cprod_top, mul_one, one_mul]
  | succ d ih =>
    intro j hj hkj
    rw [cprod_succ b (show j ≤ N by omega), ← mul_assoc, ih (j + 1) (by omega) (by omega),
      mul_assoc, hb.far k j hkj (by omega), mul_assoc]

theorem cprod_mul_self (hb : IsCox b (N + 1)) {j : ℕ} (hj : j ≤ N) :
    cprod b N j * b j = cprod b N (j + 1) := by
  rw [cprod_succ b hj, mul_assoc, hb.sq j (by omega), mul_one]

/-- `(b N ⋯ b j) * b k = b (k - 1) * (b N ⋯ b j)` when `j < k ≤ N`. -/
theorem cprod_mul_shift (hb : IsCox b (N + 1)) :
    ∀ d j, j + 1 + d ≤ N → cprod b N j * b (j + 1 + d) = b (j + d) * cprod b N j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have h1 := cprod_succ b (show j ≤ N by omega)
    have h2 := cprod_succ b (show j + 1 ≤ N by omega)
    have hc := comm_cprod hb (N + 1 - (j + 1 + 1)) (j + 1 + 1) (by omega) (le_refl (j + 1 + 1))
      (k := j)
    simp only [add_zero]
    rw [h1, h2]
    calc cprod b N (j + 1 + 1) * b (j + 1) * b j * b (j + 1)
        = cprod b N (j + 1 + 1) * (b (j + 1) * b j * b (j + 1)) := by simp only [mul_assoc]
      _ = cprod b N (j + 1 + 1) * (b j * b (j + 1) * b j) := by
          rw [← hb.br j (by omega)]
      _ = (b j * cprod b N (j + 1 + 1)) * b (j + 1) * b j := by
          rw [hc]; simp only [mul_assoc]
      _ = b j * (cprod b N (j + 1 + 1) * b (j + 1) * b j) := by simp only [mul_assoc]
  | succ d ih =>
    intro j hj
    rw [cprod_succ b (show j ≤ N by omega), mul_assoc,
      hb.far j (j + 1 + (d + 1)) (by omega) (by omega), ← mul_assoc,
      show j + 1 + (d + 1) = (j + 1) + 1 + d by omega, ih (j + 1) (by omega), mul_assoc,
      show j + 1 + d = j + (d + 1) by omega]

theorem IsCox.mono (h : IsCox b (N + 1)) : IsCox b N where
  sq k hk := h.sq k (by omega)
  br k hk := h.br k (by omega)
  far k l hkl hl := h.far k l hkl (by omega)

end Cox

/-! ### Adjacent swaps in `Perm ℕ` -/

/-- The adjacent transposition `(k k+1)`. -/
def s (k : ℕ) : Perm ℕ := swap k (k + 1)

theorem isCox_s (N : ℕ) : IsCox s N where
  sq k _ := swap_mul_self _ _
  br k _ := by
    ext x
    simp only [s, Perm.mul_apply, swap_apply_def]
    split_ifs <;> omega
  far k l hkl _ := by
    ext x
    simp only [s, Perm.mul_apply, swap_apply_def]
    split_ifs <;> omega

/-- `σ` moves no point above `N`. -/
def Supp (N : ℕ) (σ : Perm ℕ) : Prop := ∀ x, N < x → σ x = x

theorem supp_one (N : ℕ) : Supp N 1 := fun _ _ => rfl

theorem supp_mul {N : ℕ} {σ τ : Perm ℕ} (h1 : Supp N σ) (h2 : Supp N τ) : Supp N (σ * τ) :=
  fun x hx => by rw [Perm.mul_apply, h2 x hx, h1 x hx]

theorem supp_inv {N : ℕ} {σ : Perm ℕ} (h : Supp N σ) : Supp N σ⁻¹ := fun x hx => by
  rw [Perm.inv_eq_iff_eq]; exact (h x hx).symm

theorem supp_s {N k : ℕ} (hk : k < N) : Supp N (s k) := fun x hx => by
  simp only [s]; rw [swap_apply_of_ne_of_ne (by omega) (by omega)]

theorem supp_prod {N : ℕ} : ∀ w : List ℕ, (∀ k ∈ w, k < N) → Supp N (w.map s).prod
  | [], _ => supp_one N
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons]
    exact supp_mul (supp_s (hw k List.mem_cons_self))
      (supp_prod w fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))

theorem supp_cprod {N j : ℕ} (hj : j ≤ N + 1) : Supp (N + 1) (cprod s N j) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = N + 1 - d := ⟨N + 1 - j, by omega⟩
  induction d with
  | zero => rw [Nat.sub_zero, cprod_top]; exact supp_one _
  | succ d ih =>
    rcases Nat.lt_or_ge N d with h | h
    · rw [show N + 1 - (d + 1) = N + 1 - d by omega]; exact ih (by omega)
    · rw [cprod_succ s (show N + 1 - (d + 1) ≤ N by omega),
        show N + 1 - (d + 1) + 1 = N + 1 - d by omega]
      exact supp_mul (ih (by omega)) (supp_s (by omega))

theorem cprod_apply_self {N j : ℕ} (hj : j ≤ N + 1) : cprod s N j j = N + 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, j = N + 1 - d := ⟨N + 1 - j, by omega⟩
  induction d with
  | zero => rw [Nat.sub_zero, cprod_top]; rfl
  | succ d ih =>
    rcases Nat.lt_or_ge N d with h | h
    · rw [show N + 1 - (d + 1) = N + 1 - d by omega]; exact ih (by omega)
    · rw [cprod_succ s (show N + 1 - (d + 1) ≤ N by omega), Perm.mul_apply]
      simp only [s]
      rw [swap_apply_left, show N + 1 - (d + 1) + 1 = N + 1 - d by omega]
      exact ih (by omega)

/-! ### The normal form map -/

section Phi

variable (a : ℕ → G)

/-- The transversal normal form of a permutation supported in `{0, …, N}`: split off the
coset representative `s_N ⋯ s_j` with `j = σ⁻¹ (N + 1)`. -/
noncomputable def phi : ℕ → Perm ℕ → G
  | 0, _ => 1
  | N + 1, σ => phi N (σ * (cprod s N (σ⁻¹ (N + 1)))⁻¹) * cprod a N (σ⁻¹ (N + 1))

theorem phi_one : ∀ N, phi a N 1 = 1
  | 0 => rfl
  | N + 1 => by
    simp only [phi, inv_one, Perm.one_apply, cprod_top, mul_one]
    exact phi_one N

variable {a}

theorem phi_mul_s : ∀ N, IsCox a N → ∀ σ, Supp N σ → ∀ k, k < N →
    phi a N (σ * s k) = phi a N σ * a k
  | 0, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | N + 1, ha, σ, hσ, k, hk => by
    have ih := phi_mul_s N ha.mono
    have hs := isCox_s (N + 1)
    obtain ⟨j, hjdef⟩ : ∃ j, σ⁻¹ (N + 1) = j := ⟨_, rfl⟩
    have hσj : σ j = N + 1 := by rw [← hjdef]; exact σ.apply_symm_apply (N + 1)
    have hj : j ≤ N + 1 := by
      by_contra h
      have h1 : σ j = j := hσ j (by omega)
      omega
    have hσ' : Supp N (σ * (cprod s N j)⁻¹) := by
      intro x hx
      rcases Nat.lt_or_ge (N + 1) x with hx' | hx'
      · rw [Perm.mul_apply, supp_inv (supp_cprod hj) x hx', hσ x hx']
      · have hx1 : x = N + 1 := by omega
        subst hx1
        have hc : (cprod s N j)⁻¹ (N + 1) = j := by
          rw [Perm.inv_eq_iff_eq, cprod_apply_self hj]
        rw [Perm.mul_apply, hc, hσj]
    have hphi : phi a (N + 1) σ = phi a N (σ * (cprod s N j)⁻¹) * cprod a N j := by
      show phi a N (σ * (cprod s N (σ⁻¹ (N + 1)))⁻¹) * cprod a N (σ⁻¹ (N + 1)) = _
      rw [hjdef]
    have hj' : (σ * s k)⁻¹ (N + 1) = s k j := by
      rw [mul_inv_rev, Perm.mul_apply, hjdef, show (s k)⁻¹ = s k from swap_inv _ _]
    have hphik : phi a (N + 1) (σ * s k) =
        phi a N (σ * s k * (cprod s N (s k j))⁻¹) * cprod a N (s k j) := by
      show phi a N (σ * s k * (cprod s N ((σ * s k)⁻¹ (N + 1)))⁻¹) *
          cprod a N ((σ * s k)⁻¹ (N + 1)) = _
      rw [hj']
    rw [hphik, hphi]
    rcases Nat.lt_or_ge (k + 1) j with h1 | h1
    · -- `k + 2 ≤ j`: `s k` commutes with the representative
      have hkj : s k j = j := by
        simp only [s]; rw [swap_apply_of_ne_of_ne (by omega) (by omega)]
      have hcs := comm_cprod hs (N + 1 - j) j (by omega) (by omega) (k := k)
      have hca := comm_cprod ha (N + 1 - j) j (by omega) (by omega) (k := k)
      have e : σ * s k * (cprod s N j)⁻¹ = σ * (cprod s N j)⁻¹ * s k := by
        calc σ * s k * (cprod s N j)⁻¹
            = σ * (cprod s N j)⁻¹ * (cprod s N j * s k * (cprod s N j)⁻¹) := by group
          _ = σ * (cprod s N j)⁻¹ * s k := by rw [← hcs]; group
      rw [hkj, e, ih _ hσ' k (by omega), mul_assoc, hca, ← mul_assoc]
    rcases Nat.lt_or_ge k j with h2 | h2
    · -- `k + 1 = j`
      have hkj : k + 1 = j := by omega
      have hkj' : s k j = k := by simp only [s]; rw [← hkj, swap_apply_right]
      have e : cprod s N k = cprod s N j * s k := by
        rw [cprod_succ s (show k ≤ N by omega), hkj]
      have e' : cprod a N k = cprod a N j * a k := by
        rw [cprod_succ a (show k ≤ N by omega), hkj]
      rw [hkj', e, e', show σ * s k * (cprod s N j * s k)⁻¹ = σ * (cprod s N j)⁻¹ by group,
        mul_assoc]
    rcases Nat.lt_or_ge j k with h3 | h3
    · -- `j < k`: the representative shifts `s k` down to `s (k - 1)`
      obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - (j + 1), by omega⟩
      have hkj : s (j + 1 + d) j = j := by
        simp only [s]; rw [swap_apply_of_ne_of_ne (by omega) (by omega)]
      have hcs := cprod_mul_shift hs d j (by omega)
      have hca := cprod_mul_shift ha d j (by omega)
      have e : σ * s (j + 1 + d) * (cprod s N j)⁻¹ = σ * (cprod s N j)⁻¹ * s (j + d) := by
        calc σ * s (j + 1 + d) * (cprod s N j)⁻¹
            = σ * (cprod s N j)⁻¹ * (cprod s N j * s (j + 1 + d) * (cprod s N j)⁻¹) := by
              group
          _ = σ * (cprod s N j)⁻¹ * s (j + d) := by rw [hcs]; group
      rw [hkj, e, ih _ hσ' (j + d) (by omega), mul_assoc, ← hca, ← mul_assoc]
    · -- `k = j`
      have hkj : k = j := by omega
      have hkj' : s k j = j + 1 := by simp only [s]; rw [← hkj, swap_apply_left]
      have e : cprod s N (j + 1) = cprod s N j * s k := by
        rw [hkj, cprod_mul_self hs (show j ≤ N by omega)]
      have e' : cprod a N (j + 1) = cprod a N j * a k := by
        rw [hkj, cprod_mul_self ha (show j ≤ N by omega)]
      rw [hkj', e, e', show σ * s k * (cprod s N j * s k)⁻¹ = σ * (cprod s N j)⁻¹ by group,
        mul_assoc]

theorem phi_prod {N : ℕ} (ha : IsCox a N) (w : List ℕ) (hw : ∀ k ∈ w, k < N) :
    phi a N (w.map s).prod = (w.map a).prod := by
  induction w using List.reverseRecOn with
  | nil => exact phi_one a N
  | append_singleton w k ih =>
    have hw' : ∀ k' ∈ w, k' < N := fun k' hk' => hw k' (List.mem_append_left _ hk')
    have hk : k < N := hw k (List.mem_append_right _ List.mem_cons_self)
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      phi_mul_s N ha _ (supp_prod w hw') k hk, ih hw', List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]

/-- **Coxeter presentation.** Two words in the adjacent swaps with the same product in `Perm ℕ`
have the same product in any group satisfying the Coxeter relations. -/
theorem prod_eq_of_perm_eq {N : ℕ} (ha : IsCox a N) {w w' : List ℕ} (hw : ∀ k ∈ w, k < N)
    (hw' : ∀ k ∈ w', k < N) (h : (w.map s).prod = (w'.map s).prod) :
    (w.map a).prod = (w'.map a).prod := by
  rw [← phi_prod ha w hw, ← phi_prod ha w' hw', h]

end Phi

end GroupApproximation.ClassTransposition.Presentation.Coxeter
